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

describe('Solver unit propagation', () => {
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

describe('Solver two-watched-literal propagation', () => {
  // The watch invariant after ANY solver activity: every clause of length >= 2
  // appears in exactly two watch lists — those of its lits[0]/lits[1] slots —
  // and units/empty clauses are never watched at all.
  function assertWatchInvariant(solver: Solver): void {
    for (const clause of solver.clauses) {
      const memberships = solver.watches.reduce(
        (count, list) => (list.includes(clause) ? count + 1 : count),
        0,
      );
      if (clause.lits.length < 2) {
        assert.strictEqual(memberships, 0, 'units and the empty clause are never watched');
      } else {
        assert.strictEqual(
          memberships,
          2,
          `clause [${clause.lits.join(' ')}] must watch exactly two literals`,
        );
        assert.ok(solver.watches[clause.lits[0]].includes(clause));
        assert.ok(solver.watches[clause.lits[1]].includes(clause));
      }
    }
  }

  it('attaches two watches per non-unit clause and never watches units', () => {
    const C = clause([posLit(0), posLit(1), posLit(2)]);
    const unitC = clause([negLit(3)]);
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c', 'x'], [C, unitC]));

    assert.ok(solver.watches[posLit(0)].includes(C));
    assert.ok(solver.watches[posLit(1)].includes(C));
    assert.ok(!solver.watches[posLit(2)].includes(C));
    // The unit is asserted at level zero instead of being watched.
    assert.strictEqual(solver.reason[3], unitC);
    assert.ok(!solver.watches[posLit(3)].includes(unitC));
    assertWatchInvariant(solver);
  });

  it('relocates a watch to a live third literal, removing it from the falsified list', () => {
    const C = clause([posLit(0), posLit(1), posLit(2)]);
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c'], [C]));
    assert.ok(solver.watches[posLit(0)].includes(C));
    assert.ok(solver.watches[posLit(1)].includes(C));

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(0), null), true); // a = FALSE
    assert.strictEqual(solver.propagate(), null);

    // In-place swap: the falsified a moved out of the watched slots, the live
    // c took slot 1, and the watch on a was replaced by a watch on c.
    assert.deepEqual(C.lits, [posLit(1), posLit(2), posLit(0)]);
    assert.ok(!solver.watches[posLit(0)].includes(C), 'the falsified literal loses the watch');
    assert.ok(solver.watches[posLit(1)].includes(C));
    assert.ok(solver.watches[posLit(2)].includes(C), 'the live third literal gains the watch');
    assertWatchInvariant(solver);
  });

  it('goes unit mid-search when a falsified watch has no replacement', () => {
    // (a ∨ b ∨ c) with c = FALSE at level 0: deciding a = FALSE falsifies the
    // watched literal a, the swap puts a in slot 1, c is already false, and no
    // replacement exists — the clause goes unit and implies b.
    const unitC = clause([negLit(2)]);
    const C = clause([posLit(0), posLit(1), posLit(2)]);
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c'], [unitC, C]), {
      stats: solverStats,
    });

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(0), null), true);
    assert.strictEqual(solver.propagate(), null);

    assert.deepEqual(C.lits, [posLit(1), posLit(0), posLit(2)]);
    assert.strictEqual(solver.reason[1], C);
    assert.deepEqual(solver.trail, [negLit(2), negLit(0), posLit(1)]);
    assert.strictEqual(solverStats.propagations, 2); // level-0 unit c + implied b
    assert.strictEqual(solverStats.conflicts, 0);
    assertWatchInvariant(solver);
  });

  it('keeps watch lists untouched across cancelUntil and propagates correctly afterwards', () => {
    const unitC = clause([negLit(2)]);
    const C = clause([posLit(0), posLit(1), posLit(2)]);
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c'], [unitC, C]));
    const watchesBefore = [solver.watches[posLit(0)], solver.watches[posLit(1)]];

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(0), null), true); // a = FALSE → unit b
    assert.strictEqual(solver.propagate(), null);
    assert.deepEqual(C.lits, [posLit(1), posLit(0), posLit(2)]);

    solver.cancelUntil(0);
    // Backtrack-safe by construction: no watch list was touched, and qhead is
    // clamped to the truncated trail (entries below it stay pending).
    assert.deepEqual(solver.watches[posLit(0)], watchesBefore[0]);
    assert.deepEqual(solver.watches[posLit(1)], watchesBefore[1]);
    assert.strictEqual(solver.qhead, 1);
    assert.deepEqual([...solver.assigns], [Value.UNSET, Value.UNSET, Value.FALSE]);
    assert.deepEqual(C.lits, [posLit(1), posLit(0), posLit(2)], 'swaps survive backtracking');

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(1), null), true); // b = FALSE → unit a
    assert.strictEqual(solver.propagate(), null);
    assert.deepEqual(C.lits, [posLit(0), posLit(1), posLit(2)]);
    assert.strictEqual(solver.reason[0], C);
    assert.deepEqual(solver.trail, [negLit(2), negLit(1), posLit(0)]);
    assertWatchInvariant(solver);
  });

  it('examines every clause watching the same literal and keeps multi-watch membership exact', () => {
    const C1 = clause([posLit(0), posLit(1)]);
    const C2 = clause([posLit(0), posLit(2)]);
    const C3 = clause([posLit(0), posLit(3)]);
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c', 'x'], [C1, C2, C3]));
    assert.strictEqual(solver.watches[posLit(0)].length, 3);

    solver.newDecisionLevel();
    assert.strictEqual(solver.enqueue(negLit(0), null), true); // a = FALSE
    assert.strictEqual(solver.propagate(), null);

    // The list is walked backwards, so the last clause implies first.
    assert.deepEqual(solver.trail, [negLit(0), posLit(3), posLit(2), posLit(1)]);
    assert.strictEqual(solver.reason[1], C1);
    assert.strictEqual(solver.reason[2], C2);
    assert.strictEqual(solver.reason[3], C3);
    assert.strictEqual(solver.watches[posLit(0)].length, 3, 'unit clauses keep their watches');
    assertWatchInvariant(solver);
  });

  it('detects a propagation conflict across decision levels through falsified watches', () => {
    // (a∨b∨c), (¬c∨d), (b∨¬d): the level-1 decision a=FALSE relocates the
    // first clause's watch to c; the level-2 decision b=FALSE turns both
    // remaining 2-literal clauses unit (d first, then c, in backward walk
    // order); dequeuing d=FALSE falsifies (¬c∨d) — both of its watched
    // literals — and propagate() returns that clause reference.
    const C1 = clause([posLit(0), posLit(1), posLit(2)]);
    const C2 = clause([negLit(2), posLit(3)]);
    const C3 = clause([posLit(1), negLit(3)]);
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c', 'd'], [C1, C2, C3]), {
      stats: solverStats,
    });

    solver.newDecisionLevel(); // level 1
    assert.strictEqual(solver.enqueue(negLit(0), null), true); // a = FALSE
    assert.strictEqual(solver.propagate(), null);
    assert.deepEqual(C1.lits, [posLit(1), posLit(2), posLit(0)]); // watch relocated to c

    solver.newDecisionLevel(); // level 2
    assert.strictEqual(solver.enqueue(negLit(1), null), true); // b = FALSE
    assert.strictEqual(solver.propagate(), C2);
    assert.strictEqual(solverStats.conflicts, 1);
    assert.strictEqual(solverStats.propagations, 2); // implied d, then implied c
    assertWatchInvariant(solver);
  });

  it('keeps watch lists consistent across level-zero PLE assignments', () => {
    const C1 = clause([posLit(0), posLit(1)]);
    const C2 = clause([posLit(2), posLit(3)]);
    const solverStats = stats();
    const solver = new Solver(handBuiltCnf(['a', 'b', 'c', 'x'], [C1, C2]), {
      enablePle: true,
      stats: solverStats,
    });

    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.model(), {
      a: Value.TRUE,
      b: Value.TRUE,
      c: Value.TRUE,
      x: Value.TRUE,
    });
    // The global sweep pins all four pure literals; no decision is needed and
    // the watchers see nothing to propagate afterwards.
    assert.strictEqual(solverStats.decisions, 0);
    assert.strictEqual(solverStats.propagations, 4);
    assertWatchInvariant(solver);
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

  it('falls back to search when PLE is disabled', () => {
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
const CHAIN_DECISION_BOUND = 4; // calibrated against the pinned reference implementation

// Decisions remaining after the hypergraph's UP+PLE fixpoint. The pinned
// global-sweep PLE (purity over unsatisfied clauses only) assigns d, f, i, s,
// j, r, k, q, l, p, m, o, but `e` and `n` become zero-occurrence don't-cares
// (every clause mentioning them is satisfied before they could become pure),
// so the search loop decides those two FALSE-first.
const HYPERGRAPH_DECISIONS = 2;

describe('Solver CDCL search loop', () => {
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

  it('learns a root unit after a conflict and finds the only model', () => {
    // (a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b): unique model { a: TRUE, b: FALSE }. The
    // FALSE-first a=FALSE forces b=FALSE (backward watch-list order), which
    // conflicts on (a∨b). Resolving b learns the unary (a), asserted at level
    // zero with a clause reason; propagation then forces b=FALSE again.
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
    assert.deepEqual(solverStats, {
      decisions: 1,
      propagations: 3, // b before conflict, learned a at root, then b at root
      conflicts: 1,
      restarts: 0,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
    });
    const learned = solver.reason[0];
    assert.ok(learned !== null);
    assert.strictEqual(learned.learned, true);
    assert.ok(solver.clauses.includes(learned));
    assert.deepEqual(learned.lits, [posLit(0)]);
    assert.strictEqual(solver.level[0], 0);
    assert.strictEqual(solver.level[1], 0);
    assert.ok(
      solver.watches.every((list) => !list.includes(learned)),
      'units are never watched',
    );
  });

  it('reports UNSAT on the root conflict after learning, without another decision', () => {
    // (a∨b) ∧ (¬a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b): b is forced both ways — the search
    // learns (a) from the a=FALSE branch, then the root assertion leads to a
    // second conflict. A root conflict is UNSAT, not another analyzed clause.
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
    assert.deepEqual(solverStats, {
      decisions: 1,
      propagations: 3,
      conflicts: 2,
      restarts: 0,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
    });
    assert.strictEqual(solver.trailLim.length, 0);
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
