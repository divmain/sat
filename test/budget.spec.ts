// Public and internal conflict budgets (Design § Target Public API, Budget
// contract): validation order and shapes, the explicit budget-zero startup
// exception, hard positive caps with atomic conflict handling, verdict
// precedence at the limit, the budget-1 second-root-conflict witness,
// per-call scoping across repeated incremental calls, and the single
// enumeration-wide budget with partial-model evidence. Async rejection
// contracts live in async.spec.ts; both share these witnesses.

import assert from 'node:assert';
import { describe, it } from 'node:test';
import { and, createSolver, getAllSolutions, getSolution, not, or, Value } from '../src/index.js';
import type { BooleanExpr } from '../src/index.js';
import { compile } from '../src/compile.js';
import { createSolverStats, Solver } from '../src/solver.js';
import { expectCompleteModels, expressionValue, modelKey, referenceModels } from './helpers.js';

// The boundary witness from the design: UNSAT needs two root conflicts, and
// the first (at decision level 1) learns the root unit (a).
const boundaryWitness = () =>
  and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'), or(not('a'), not('b')));

// Resolving t derives (¬a∨¬b∨¬xi) per gadget: a=b=TRUE with every xi=FALSE
// is a satisfiable context, and targeting xi exposes exactly one genuine
// conflict before SAT (the incremental.spec witness), without synthesizing
// clauses, activities, or counters.
const gadgets = (count: number): BooleanExpr =>
  and(
    ...Array.from({ length: count }, (_, index) =>
      and(
        or(not('a'), not(`x${index}`), 't'),
        or(not('b'), not(`x${index}`), not('t')),
        or('a', 'b', `x${index}`, 't'),
      ),
    ),
  );

const INVALID_BUDGETS: readonly unknown[] = [
  -1,
  0.5,
  Number.NaN,
  Number.POSITIVE_INFINITY,
  Number.NEGATIVE_INFINITY,
  2 ** 53,
];

describe('conflictBudget validation', () => {
  it('rejects invalid budgets before any search at every entry point', () => {
    const expr = or('a', 'b');
    const handle = createSolver(expr);
    for (const budget of INVALID_BUDGETS) {
      const options = { conflictBudget: budget } as never;
      assert.throws(() => getSolution(expr, options), /conflictBudget/);
      assert.throws(() => getAllSolutions(expr, options), /conflictBudget/);
      assert.throws(() => handle.solve(undefined, options), /conflictBudget/);
      // The internal option validates identically at construction and per call.
      assert.throws(
        () => new Solver(compile(expr), { conflictBudget: budget as number }),
        /conflictBudget/,
      );
      assert.throws(
        () => new Solver(compile(expr)).solveAssuming(undefined, undefined, budget as number),
        /conflictBudget/,
      );
    }
  });

  it('validates the budget before assumption validation and before any cached-UNSAT short-circuit', () => {
    // Budget validation precedes assumption validation.
    assert.throws(
      () =>
        getSolution(and('a'), {
          conflictBudget: -1,
          assumptions: { missing: Value.TRUE },
        }),
      /conflictBudget/,
    );
    // ...and precedes a cached verdict: the base proves UNSAT on the first
    // call, yet an invalid budget on a later call is still an error.
    const handle = createSolver(and('a', not('a')));
    assert.strictEqual(handle.solve().status, 'unsat');
    assert.throws(() => handle.solve(undefined, { conflictBudget: 0.5 }), /conflictBudget/);
    assert.throws(() => handle.solve({ alsoMissing: Value.TRUE }), /unknown assumption/);
  });

  it('zeroes stats before budget validation', () => {
    const stats = createSolverStats();
    for (const call of [
      () => getSolution(or('a', 'b'), { conflictBudget: -1, stats }),
      () => getAllSolutions(or('a', 'b'), { conflictBudget: -1, stats }),
      () => createSolver(or('a', 'b')).solve(undefined, { conflictBudget: -1, stats }),
    ]) {
      stats.decisions = 999;
      assert.throws(call, /conflictBudget/);
      assert.strictEqual(stats.decisions, 0, 'stats zeroing precedes validation');
    }
  });
});

describe('the budget-zero startup exception', () => {
  it('returns compiled/cached UNSAT without any propagation', () => {
    const stats = createSolverStats();
    assert.deepStrictEqual(getSolution(or(), { conflictBudget: 0, stats }), {
      status: 'unsat',
      core: {},
    });
    assert.deepStrictEqual(stats, createSolverStats(), 'compiled UNSAT needs no search');
    assert.deepStrictEqual(getAllSolutions(or(), { conflictBudget: 0 }), {
      status: 'complete',
      models: [],
    });
    const handle = createSolver(and('a', not('a')));
    assert.deepStrictEqual(handle.solve(undefined, { conflictBudget: 0 }), {
      status: 'unsat',
      core: {},
    });
  });

  it('returns an initial root conflict found by the one permitted propagation pass', () => {
    // Two contradictory units: the exception pass discovers the falsified
    // clause and counts the terminal conflict once, over the zero budget.
    const stats = createSolverStats();
    assert.deepStrictEqual(getSolution(and('a', not('a')), { conflictBudget: 0, stats }), {
      status: 'unsat',
      core: {},
    });
    assert.strictEqual(stats.conflicts, 1);
  });

  it('returns an already-complete model after the permitted root fixpoint', () => {
    const stats = createSolverStats();
    assert.deepStrictEqual(getSolution(and('a', 'b'), { conflictBudget: 0, stats }), {
      status: 'sat',
      model: { a: Value.TRUE, b: Value.TRUE },
    });
    assert.strictEqual(stats.decisions, 0, 'no search decision at budget zero');
    assert.strictEqual(stats.conflicts, 0);
  });

  it('otherwise returns unknown without PLE or a search decision', () => {
    // or('a', ¬'a') is a tautology that single-shot PLE would pin outright;
    // the exhausted budget forbids PLE, so the answer is honestly unknown.
    for (const expr of [or('a', 'b'), or('a', not('a')), and(or('a', 'b'), 'c')]) {
      const stats = createSolverStats();
      const result = getSolution(expr, { conflictBudget: 0, stats });
      assert.deepStrictEqual(result, { status: 'unknown', reason: 'conflictBudget' });
      assert.strictEqual(stats.decisions, 0, 'budget zero never decides');
      assert.strictEqual(stats.conflicts, 0);
    }
  });

  it('never re-arms the allowance between enumeration models', () => {
    // and('a','b'): the first (and only) model is already complete at root.
    // The budget-zero exception permits its establishing propagation pass,
    // but grants no second allowance for the terminal search.
    assert.deepStrictEqual(getAllSolutions(and('a', 'b'), { conflictBudget: 0 }), {
      status: 'unknown',
      models: [{ a: Value.TRUE, b: Value.TRUE }],
      reason: 'conflictBudget',
    });
    // or('a','b') needs a decision: unknown with no models at all.
    assert.deepStrictEqual(getAllSolutions(or('a', 'b'), { conflictBudget: 0 }), {
      status: 'unknown',
      models: [],
      reason: 'conflictBudget',
    });
  });
});

describe('hard positive budgets: boundary witnesses', () => {
  it('budget 1 on the second-root-conflict witness: unknown after learning a root unit, not UNSAT', () => {
    const expr = boundaryWitness();
    const stats = createSolverStats();
    // PLE is vacuous here (every literal appears in both polarities), so the
    // public single-shot path exercises the same trajectory the design's
    // PLE-disabled witness pins.
    assert.deepStrictEqual(getSolution(expr, { conflictBudget: 1, stats }), {
      status: 'unknown',
      reason: 'conflictBudget',
    });
    assert.strictEqual(stats.conflicts, 1, 'exactly the budgeted conflict');
    assert.strictEqual(stats.learnedClauses, 1, 'the final transaction still learns');
    assert.strictEqual(stats.decisions, 1);
    // The formula is UNSAT; only the budget hid the proof. Unlimited agrees.
    assert.strictEqual(getSolution(expr).status, 'unsat');
  });

  it('verdict at the limit: budget 2 reaches the terminal second conflict and returns UNSAT', () => {
    const stats = createSolverStats();
    assert.deepStrictEqual(getSolution(boundaryWitness(), { conflictBudget: 2, stats }), {
      status: 'unsat',
      core: {},
    });
    assert.strictEqual(stats.conflicts, 2);
  });

  it('keeps learned clauses and the retained root unit reusable after exhaustion', () => {
    const handle = createSolver(boundaryWitness());
    assert.deepStrictEqual(handle.solve(undefined, { conflictBudget: 1 }), {
      status: 'unknown',
      reason: 'conflictBudget',
    });
    // The learned root unit persisted: the next call's initial propagation
    // finds the terminal conflict it hides, with no further learning needed.
    const stats = createSolverStats();
    assert.deepStrictEqual(handle.solve(undefined, { stats }), { status: 'unsat', core: {} });
    assert.strictEqual(stats.conflicts, 1);
    assert.strictEqual(stats.learnedClauses, 0, 'the earlier call already learned it');
  });

  it('SAT side: a budget exactly at the conflict count still returns unknown; one more completes', () => {
    const target = 'x0';
    const make = () =>
      createSolver(gadgets(1), {
        variablePriority: (unassigned) => {
          if (unassigned.includes(target)) return [target, true];
          const x = unassigned.find((name) => name.startsWith('x'));
          return x === undefined ? null : [x, false];
        },
      });
    const measured = createSolverStats();
    const unlimited = make().solve({ a: Value.TRUE, b: Value.TRUE }, { stats: measured });
    assert.strictEqual(unlimited.status, 'sat');
    assert.strictEqual(measured.conflicts, 1, 'the witness really spends one conflict');
    // Exactly-at-need: the conflict's atomic transaction completes, but no
    // further propagation pass may run merely to seek the verdict.
    assert.deepStrictEqual(make().solve({ a: Value.TRUE, b: Value.TRUE }, { conflictBudget: 1 }), {
      status: 'unknown',
      reason: 'conflictBudget',
    });
    const stats = createSolverStats();
    const completed = make().solve({ a: Value.TRUE, b: Value.TRUE }, { conflictBudget: 2, stats });
    assert.strictEqual(completed.status, 'sat');
    assert.strictEqual(stats.conflicts, 1);
  });

  it('scopes one budget per incremental call across repeated calls', () => {
    let target = 'x0';
    const handle = createSolver(gadgets(3), {
      variablePriority: (unassigned) => {
        if (unassigned.includes(target)) return [target, true];
        const x = unassigned.find((name) => name.startsWith('x'));
        return x === undefined ? null : [x, false];
      },
    });
    const stats = createSolverStats();
    for (let call = 0; call < 3; call += 1) {
      target = `x${call}`;
      assert.deepStrictEqual(
        handle.solve({ a: Value.TRUE, b: Value.TRUE }, { conflictBudget: 1, stats }),
        { status: 'unknown', reason: 'conflictBudget' },
      );
      assert.strictEqual(stats.conflicts, 1, 'per-call accounting, never cumulative');
    }
    // The handle stays coherent: an unbudgeted call completes normally.
    const result = handle.solve({ a: Value.FALSE }, { stats });
    assert.strictEqual(result.status, 'sat');
    assert.strictEqual(stats.conflicts, 0);
  });
});

describe('one enumeration-wide budget', () => {
  const pairs = (count: number): BooleanExpr =>
    and(...Array.from({ length: count }, (_, i) => or(`a${i + 1}`, `b${i + 1}`)));

  it('partial results are a genuine prefix of the complete enumeration, valid and unique', () => {
    const expr = pairs(2);
    const complete = expectCompleteModels(getAllSolutions(expr));
    assert.strictEqual(complete.length, 9);
    const totalStats = createSolverStats();
    getAllSolutions(expr, { stats: totalStats });
    const totalConflicts = totalStats.conflicts;
    assert.ok(totalConflicts > 0, 'the fixture really conflicts during enumeration');

    let sawGenuinePartial = false;
    for (let budget = 0; budget <= totalConflicts; budget += 1) {
      const stats = createSolverStats();
      const result = getAllSolutions(expr, { conflictBudget: budget, stats });
      if (budget >= totalConflicts) {
        // The final conflict of the terminal search is terminal: verdict
        // precedence completes the enumeration at the full count.
        assert.strictEqual(result.status, 'complete', `budget ${budget} completes`);
        assert.deepStrictEqual(
          result.status === 'complete' ? result.models : [],
          complete,
          'identical order for identical histories',
        );
        continue;
      }
      assert.strictEqual(result.status, 'unknown', `budget ${budget} exhausts mid-enumeration`);
      assert.strictEqual(result.reason, 'conflictBudget');
      assert.ok(stats.conflicts <= budget, 'hard cap respected');
      assert.ok(result.models.length < complete.length, 'strictly partial');
      // Every partial model is valid and unique, and the partial list is an
      // exact PREFIX of the unlimited run's deterministic order.
      const seen = new Set<string>();
      result.models.forEach((model, index) => {
        assert.strictEqual(expressionValue(expr, model), Value.TRUE);
        assert.deepStrictEqual(model, complete[index]);
        seen.add(modelKey(model));
      });
      assert.strictEqual(seen.size, result.models.length);
      if (result.models.length > 0) sawGenuinePartial = true;
    }
    assert.ok(sawGenuinePartial, 'some budget lands between model boundaries');
  });

  it('exhaustion during the first model search yields an empty partial', () => {
    const result = getAllSolutions(pairs(2), { conflictBudget: 0 });
    assert.deepStrictEqual(result, { status: 'unknown', models: [], reason: 'conflictBudget' });
  });

  it('spans the internal enumeration driver with one constructor budget', () => {
    const expr = pairs(2);
    const complete = expectCompleteModels(new Solver(compile(expr)).enumerateModels());
    const measured = new Solver(compile(expr));
    const unlimited = measured.enumerateModels();
    assert.strictEqual(unlimited.status, 'complete');
    const totalConflicts = measured.stats.conflicts;
    assert.ok(totalConflicts > 0);
    const budgeted = new Solver(compile(expr), { conflictBudget: 1 });
    const outcome = budgeted.enumerateModels();
    assert.strictEqual(outcome.status, 'unknown');
    assert.ok(outcome.models.length < complete.length);
    outcome.models.forEach((model, index) =>
      assert.deepStrictEqual(model, complete[index], 'prefix model'),
    );
  });
});

describe('unlimited budgets never produce unknown', () => {
  it('no budget anywhere means no unknown anywhere', () => {
    const formulas = [
      and(),
      or(),
      and('a', not('a')),
      or('a', 'b'),
      boundaryWitness(),
      gadgets(2),
      and(or('a', 'b'), or(not('a'), 'c'), impliesChain()),
    ];
    for (const expr of formulas) {
      const single = getSolution(expr);
      assert.notStrictEqual(single.status, 'unknown');
      const enumerated = getAllSolutions(expr);
      assert.strictEqual(enumerated.status, 'complete');
      const handle = createSolver(expr);
      const reference = referenceModels(expr);
      assert.strictEqual(handle.solve().status, reference.length > 0 ? 'sat' : 'unsat');
      if (single.status === 'sat') {
        assert.strictEqual(expressionValue(expr, single.model), Value.TRUE);
      }
      for (const model of enumerated.models) {
        assert.strictEqual(expressionValue(expr, model), Value.TRUE);
      }
    }
  });
});

// A small helper so the unlimited battery includes an implication gadget.
function impliesChain(): BooleanExpr {
  return and(or('p', 'q'), or(not('p'), 'r'), or(not('q'), not('r')));
}
