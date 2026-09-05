import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, negLit, posLit, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, or, Value, xor, not } from '../src/expr.js';
import type { VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import {
  expressionValue,
  hypergraphFormula,
  mulberry32,
  randomFormula,
  referenceModels,
} from './helpers';

function clause(lits: number[]): Clause {
  return { lits: [...lits].sort((a, b) => a - b), learned: false, activity: 0, lbd: 0 };
}

function handBuiltCnf(names: string[], clauses: Clause[], levelZeroUnsat = false): CompiledCnf {
  return {
    numVars: names.length,
    numNamedVars: names.length,
    clauses,
    nameToIndex: new Map(names.map((name, index) => [name, index])),
    indexToName: names,
    levelZeroUnsat,
  };
}

function stats(): SolverStats {
  return {
    decisions: 0,
    propagations: 0,
    conflicts: 0,
    restarts: 0,
    learnedClauses: 0,
    learnedClausesCurrent: 0,
  };
}

function assertTrailInvariant(solver: Solver): void {
  const counts = new Int32Array(solver.assigns.length);
  for (const lit of solver.trail) {
    counts[varOf(lit)] += 1;
  }
  for (let variable = 0; variable < solver.assigns.length; variable += 1) {
    assert.strictEqual(
      solver.assigns[variable] !== Value.UNSET,
      counts[variable] === 1,
      `assigns/trail mismatch for variable ${variable}`,
    );
  }
}

describe('Solver enqueue, trail, and decision levels', () => {
  it('enqueues each variable once and rejects its opposite literal', () => {
    const solver = new Solver(handBuiltCnf(['a'], []));

    assert.strictEqual(solver.enqueue(posLit(0), null), true);
    assert.strictEqual(solver.enqueue(posLit(0), null), true);
    assert.strictEqual(solver.enqueue(negLit(0), null), false);
    assert.deepEqual(solver.trail, [posLit(0)]);
    assert.strictEqual(solver.assigns[0], Value.TRUE);
    assertTrailInvariant(solver);
  });

  it('debug assertions detect an assigns/trail invariant violation', () => {
    const solver = new Solver(handBuiltCnf(['a'], []));
    solver.assigns[0] = Value.TRUE;

    assert.throws(
      () => solver.enqueue(posLit(0), null),
      /trail invariant violated: assigns and trail membership must agree/,
    );
  });

  it('cancels levels in reverse while retaining level-zero assignments', () => {
    const root = clause([posLit(0)]);
    const reason = clause([negLit(1), posLit(2)]);
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c'], [root]));

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(1), null), true);
    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(posLit(2), reason), true);
    solver.qhead = solver.trail.length;
    solver.cancelUntil(1);

    assert.deepEqual([...solver.assigns], [Value.TRUE, Value.FALSE, Value.UNSET]);
    assert.deepEqual(solver.reason, [root, null, null]);
    assert.deepEqual(solver.trail, [posLit(0), negLit(1)]);
    assert.deepEqual(solver.trailLim, [1]);
    assert.strictEqual(solver.qhead, 2);
    assertTrailInvariant(solver);

    solver.cancelUntil(0);
    assert.deepEqual([...solver.assigns], [Value.TRUE, Value.UNSET, Value.UNSET]);
    assert.deepEqual(solver.trail, [posLit(0)]);
    assert.deepEqual(solver.trailLim, []);
    assert.strictEqual(solver.qhead, 1);
    assertTrailInvariant(solver);
  });
});

describe('Solver occurrence-list propagation', () => {
  it('propagates a complete unit-cascade chain with clause reasons', () => {
    const unit = clause([posLit(0)]);
    const implyB = clause([negLit(0), posLit(1)]);
    const implyC = clause([negLit(1), posLit(2)]);
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c'], [unit, implyB, implyC]), {
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.TRUE, c: Value.TRUE });
    assert.strictEqual(solver.reason[0], unit);
    assert.strictEqual(solver.reason[1], implyB);
    assert.strictEqual(solver.reason[2], implyC);
    assert.strictEqual(solverStats.propagations, 3);
    assert.strictEqual(solverStats.conflicts, 0);
    assertTrailInvariant(solver);
  });

  it('detects conflicting units at level zero', () => {
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a'], [clause([posLit(0)]), clause([negLit(0)])]), {
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), false);
    assert.strictEqual(solverStats.propagations, 1);
    assert.strictEqual(solverStats.conflicts, 1);
  });

  it('returns the original clause reference for a propagation conflict', () => {
    const conflict = clause([negLit(0), posLit(1)]);
    const solverStats = stats();
    const solver = new Solver(
      handBuiltCnf(['a', 'b'], [clause([posLit(0)]), clause([negLit(1)]), conflict]),
      { stats: solverStats },
    );

    assert.strictEqual(solver.propagate(), conflict);
    assert.strictEqual(solverStats.conflicts, 1);
    assert.strictEqual(solverStats.propagations, 2);
  });

  it('treats a level-zero propagation conflict as permanent UNSAT', () => {
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b'],
        [clause([posLit(0)]), clause([negLit(1)]), clause([negLit(0), posLit(1)])],
      ),
    );

    assert.strictEqual(solver.solve(), false);
    assert.strictEqual(solver.solve(), false);
  });

  it('short-circuits a compiler-marked empty clause', () => {
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf([], [clause([])], true), { stats: solverStats });

    assert.strictEqual(solver.solve(), false);
    assert.strictEqual(solverStats.conflicts, 0);
  });

  it('throws instead of reporting UNSAT when the conflict budget is exhausted', () => {
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b'],
        [clause([posLit(0)]), clause([negLit(1)]), clause([negLit(0), posLit(1)])],
      ),
      { maxConflicts: 1 },
    );

    assert.throws(() => solver.solve(), /maximum conflict budget exhausted \(1\)/);
  });
});

describe('Solver assumptions', () => {
  it('validates unknown names and invalid values', () => {
    const cnf = handBuiltCnf(['a'], []);
    assert.throws(
      () => new Solver(cnf, { assumptions: { missing: Value.TRUE } }),
      /unknown assumption variable: "missing"/,
    );
    assert.throws(
      () => new Solver(cnf, { assumptions: { a: 2 as Value } }),
      /invalid assumption value for "a": 2/,
    );
    assert.throws(
      () => new Solver(cnf, { assumptions: { a: true as unknown as Value } }),
      /invalid assumption value for "a": true/,
    );
  });

  it('ignores UNSET and does not count assumptions as propagations', () => {
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b'], [clause([posLit(0)])]), {
      assumptions: { a: Value.UNSET, b: Value.FALSE },
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.FALSE });
    assert.strictEqual(solverStats.propagations, 1);
  });

  it('propagates assumptions immediately at level zero', () => {
    const implication = clause([negLit(0), posLit(1)]);
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b'], [implication]), {
      assumptions: { a: Value.TRUE },
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.TRUE });
    assert.strictEqual(solver.reason[0], null);
    assert.strictEqual(solver.reason[1], implication);
    assert.strictEqual(solverStats.propagations, 1);
  });

  it('reports an assumption inconsistent with a unit formula as UNSAT', () => {
    const solver = new Solver(handBuiltCnf(['a'], [clause([posLit(0)])]), {
      assumptions: { a: Value.FALSE },
    });
    assert.strictEqual(solver.solve(), false);
  });
});

describe('Solver scoped pure-literal elimination', () => {
  it('assigns every currently-pure variable in one ascending global sweep', () => {
    const solverStats = stats();
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b', 'c'],
        [clause([posLit(0), posLit(1)]), clause([posLit(1), negLit(2)])],
      ),
      { enablePle: true, stats: solverStats },
    );

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.trail, [posLit(0), posLit(1), negLit(2)]);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.TRUE, c: Value.FALSE });
    assert.strictEqual(solverStats.propagations, 3);
  });

  it('computes purity over unsatisfied clauses only', () => {
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b', 'x'],
        [clause([posLit(2)]), clause([negLit(0), posLit(2)]), clause([posLit(0), posLit(1)])],
      ),
      { enablePle: true },
    );

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.TRUE, x: Value.TRUE });
  });

  it('falls back to chronological search when PLE is disabled', () => {
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b'], [clause([posLit(0), posLit(1)])]), {
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.FALSE, b: Value.TRUE });
    assert.strictEqual(solverStats.decisions, 1);
    assert.strictEqual(solverStats.propagations, 1);
    assert.strictEqual(solverStats.conflicts, 0);
  });
});

// Decision-count ceiling for the 25-variable prereq chain (calibrated below):
// FALSE-first on the first prereq lets unit propagation cascade through the
// whole chain, so the chain solves with exactly one decision.
const CHAIN_DECISION_BOUND = 4; // calibrated on Phase-1 implementation

// Decisions remaining after the hypergraph's UP+PLE fixpoint. Calibrated on
// Phase-1 implementation: the pinned global-sweep PLE (purity over
// unsatisfied clauses only) assigns d, f, i, s, j, r, k, q, l, p, m, o, but
// `e` and `n` become zero-occurrence don't-cares (every clause mentioning
// them is satisfied before they could become pure), so the search loop
// decides those two FALSE-first.
const HYPERGRAPH_DECISIONS = 2;

describe('Solver DPLL search loop', () => {
  it('solves the complex worked example to its exact unique model', () => {
    const formula = and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')));
    const solverStats = stats();
    const solver = new Solver(compile(formula), { stats: solverStats });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), {
      a: Value.TRUE,
      b: Value.FALSE,
      c: Value.TRUE,
      d: Value.TRUE,
      e: Value.TRUE,
    });
    assert.strictEqual(solverStats.decisions, 0);
    assert.strictEqual(solverStats.conflicts, 0);
  });

  it('reports UNSAT for the unsolvable worked example at level zero', () => {
    const formula = and(
      not('b'),
      or('a', 'b'),
      xor('b', 'c'),
      implies('c', and('d', 'e')),
      not('d'),
      xor('b', 'e'),
    );
    const solverStats = stats();
    const solver = new Solver(compile(formula), { stats: solverStats });

    assert.strictEqual(solver.solve(), false);
    assert.ok(solverStats.conflicts >= 1);
  });

  it('solves the 18-prereq hypergraph under { h: TRUE } with a calibrated decision count', () => {
    const formula = hypergraphFormula();
    const solverStats = stats();
    const solver = new Solver(compile(formula), {
      assumptions: { h: Value.TRUE },
      enablePle: true,
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solverStats.decisions, HYPERGRAPH_DECISIONS);
    assert.ok(solverStats.propagations >= 10, 'PLE enqueues count as propagations');

    const model = solver.model();
    // UP forces {h, b, g, a, c}; the pinned global-sweep PLE assigns the rest
    // of the chain and the search loop fills the two remaining don't-cares.
    for (const required of ['a', 'b', 'c', 'g', 'h']) {
      assert.strictEqual(model[required], Value.TRUE);
    }
    const expected: VariableAssignments = {};
    for (const name of ['a', 'b', 'c', 'd', 'g', 'h', 'i', 'j', 'k', 'l', 'm']) {
      expected[name] = Value.TRUE;
    }
    for (const name of ['e', 'f', 'n', 'o', 'p', 'q', 'r', 's']) {
      expected[name] = Value.FALSE;
    }
    assert.deepEqual(model, expected);
    assert.strictEqual(expressionValue(formula, model), Value.TRUE);
  });

  it('solves a 25-variable prereq chain within the calibrated decision bound', () => {
    const prereqClauses = [];
    for (let index = 2; index <= 25; index += 1) {
      prereqClauses.push(implies(`v${index}`, `v${index - 1}`));
    }
    const formula = and(...prereqClauses);
    const solverStats = stats();
    const solver = new Solver(compile(formula), { stats: solverStats });

    assert.strictEqual(solver.solve(), true);
    assert.ok(
      solverStats.decisions < CHAIN_DECISION_BOUND,
      `decisions ${solverStats.decisions} must stay below ${CHAIN_DECISION_BOUND}`,
    );
    assert.strictEqual(solverStats.conflicts, 0);
    assert.ok(solverStats.propagations >= 24);
    const model = solver.model();
    assert.strictEqual(Object.keys(model).length, 25);
    assert.strictEqual(expressionValue(formula, model), Value.TRUE);
  });

  it('flips a level decision after a conflict and finds the only model', () => {
    // (a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b): unique model { a: TRUE, b: FALSE }. The
    // FALSE-first decision a=FALSE forces b=TRUE and conflicts on (a∨¬b); the
    // loop flips the level and propagates a=TRUE, b=FALSE.
    const solverStats = stats();
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b'],
        [
          clause([posLit(0), posLit(1)]),
          clause([posLit(0), negLit(1)]),
          clause([negLit(0), negLit(1)]),
        ],
      ),
      { stats: solverStats },
    );

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.FALSE });
    assert.ok(solverStats.conflicts >= 1);
    assert.ok(solverStats.decisions >= 1);
  });

  it('exhausts every decision level to report UNSAT', () => {
    // (a∨b) ∧ (¬a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b): b is forced both ways — the search
    // must try a=FALSE, a=TRUE and, on the second conflict at the same level,
    // keep unwinding to report UNSAT.
    const solverStats = stats();
    const solver = new Solver(
      handBuiltCnf(
        ['a', 'b'],
        [
          clause([posLit(0), posLit(1)]),
          clause([negLit(0), posLit(1)]),
          clause([posLit(0), negLit(1)]),
          clause([negLit(0), negLit(1)]),
        ],
      ),
      { stats: solverStats },
    );

    assert.strictEqual(solver.solve(), false);
    assert.ok(solverStats.conflicts >= 2);
  });

  it('consults the variablePriority hook at decision points and honors its polarity', () => {
    let hookCalls = 0;
    const solverStats = stats();
    const solver = new Solver(compile(xor('a', 'b')), {
      variablePriority: (unassigned, _assignments) => {
        hookCalls += 1;
        assert.deepEqual(unassigned, ['a', 'b']);
        return ['a', true];
      },
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(hookCalls, 1);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.FALSE });
  });

  it('agrees with the reference evaluator on seeded random 3-variable formulas', () => {
    for (let seed = 0; seed < 20; seed += 1) {
      const rng = mulberry32(seed);
      const { expr } = randomFormula(rng, { maxDepth: 3, maxWidth: 4, maxVariables: 3 });
      const solver = new Solver(compile(expr));
      const sat = solver.solve();
      const reference = referenceModels(expr);

      assert.strictEqual(sat, reference.length > 0, `verdict mismatch on seed ${seed}`);
      if (sat) {
        const model = solver.model();
        assert.strictEqual(
          expressionValue(expr, model),
          Value.TRUE,
          `returned model falsifies the formula on seed ${seed}`,
        );
      }
    }
  });
});

describe('Solver model projection', () => {
  it('omits auxiliary variables and safely handles special property names', () => {
    const cnf = handBuiltCnf(['__proto__'], [clause([posLit(0)])]);
    cnf.numVars = 2;
    const solver = new Solver(cnf);

    assert.strictEqual(solver.enqueue(negLit(1), null), true);
    assert.strictEqual(solver.solve(), true);
    const model: VariableAssignments = solver.model();
    assert.deepEqual(Object.keys(model), ['__proto__']);
    assert.strictEqual(model.__proto__, Value.TRUE);
  });

  it('refuses to project an incomplete named assignment', () => {
    const solver = new Solver(handBuiltCnf(['a'], []));
    assert.throws(() => solver.model(), /before every named variable is assigned/);
  });
});
