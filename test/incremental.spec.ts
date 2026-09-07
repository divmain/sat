import assert from 'node:assert';
import { describe, it } from 'node:test';
import { and, createSolver, implies, not, or, Value, xor } from '../src/index.js';
import type { SatSolver, VariableAssignments, VariablePriority } from '../src/index.js';
import { compile, compileCount, varOf } from '../src/compile.js';
import { Solver } from '../src/solver.js';
import {
  assertModelListsEqual,
  assertModelShape,
  cnfToExpr,
  modelKey,
  mulberry32,
  random3Cnf,
  referenceModels,
} from './helpers.js';
import {
  assertEntailed,
  assertResult,
  assertRoot,
  cnfTruthTable,
  counters,
  extendsAssumptions,
  IncrementalAudit,
  internals,
  literal,
} from './incremental-helpers.js';

const free = (name: string) => or(name, not(name));
const lostAssumption = () => and(or(not('a'), 'x'), or(not('a'), not('x')));
const belowPrefix = () => and(free('a'), free('b'), or('x', 't'), or('x', not('t')));

describe('createSolver public lifecycle', () => {
  it('uses the real compiler exactly once across 256 sequential public calls with varying subsets', (t) => {
    const expr = and(implies('a', 'b'), xor('c', 'd'), or('a', 'c'));
    const reference = referenceModels(expr);
    const countBefore = compileCount.value;
    const solver: SatSolver = createSolver(expr, { variablePriority: undefined });
    assert.strictEqual(compileCount.value, countBefore + 1, 'factory invokes the REAL compile()');
    assert.deepStrictEqual(Object.keys(solver), ['solve']);
    const instances = new Set<Solver>();
    const searches = Solver.prototype.solve;
    const boundary = Solver.prototype.solveAssuming;
    let searchCalls = 0;
    t.mock.method(
      Solver.prototype,
      'solve',
      function (this: Solver, assumptions: readonly number[] = []) {
        instances.add(this);
        searchCalls += 1;
        return searches.call(this, assumptions);
      },
    );
    t.mock.method(
      Solver.prototype,
      'solveAssuming',
      function (this: Solver, ...args: Parameters<Solver['solveAssuming']>) {
        try {
          return boundary.apply(this, args);
        } finally {
          assertRoot(this);
        }
      },
    );
    const samples = new Set<string>();
    let sat = 0;
    let unsat = 0;
    for (let pattern = 0; pattern < 256; pattern += 1) {
      const entries: Array<[string, Value]> = [];
      for (const [index, name] of ['a', 'b', 'c', 'd'].entries()) {
        const choice = (pattern >> (2 * index)) & 3;
        if (choice > 0) entries.push([name, [Value.UNSET, Value.FALSE, Value.TRUE][choice - 1]]);
      }
      if (pattern % 2 === 1) entries.reverse();
      const assumptions = Object.fromEntries(entries);
      samples.add(modelKey(assumptions));
      const stats = counters(999);
      const actual = solver.solve(assumptions, stats);
      assertResult(expr, assumptions, reference, actual);
      if (actual === null) unsat += 1;
      else sat += 1;
      assert.strictEqual(
        compileCount.value,
        countBefore + 1,
        `no recompilation on call ${pattern}`,
      );
    }
    assert.strictEqual(samples.size, 256);
    assert.strictEqual(searchCalls, 256, 'every public call uses the SAME shared search loop');
    assert.strictEqual(instances.size, 1, 'one persistent core, not just cached compilation');
    assert.ok(sat > 0 && unsat > 0);
    t.diagnostic(`compile delta 1; 256 calls / distinct subsets; ${sat} SAT, ${unsat} UNSAT`);
  });

  it('fixes the lost-assumption witness without poisoning later compatible or base calls', () => {
    // Resolving x gives ¬a. Learning it must replay/check a, not return a=FALSE
    // as a model of the original call. This is NOT permanent base UNSAT.
    const expr = lostAssumption();
    const reference = referenceModels(expr);
    const solver = createSolver(expr);
    const stats = counters(999);
    assert.strictEqual(solver.solve({ a: Value.TRUE }, stats), null);
    assert.deepStrictEqual(stats, {
      ...counters(),
      propagations: 2,
      conflicts: 1,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
    });
    const assumptionSets: VariableAssignments[] = [
      { a: Value.FALSE, x: Value.TRUE },
      {},
      { a: Value.TRUE },
      { x: Value.FALSE },
    ];
    for (const assumptions of assumptionSets) {
      assertResult(expr, assumptions, reference, solver.solve(assumptions, stats));
      assert.strictEqual(stats.learnedClauses, 0, 'do not recount the retained unit');
      assert.strictEqual(stats.learnedClausesCurrent, 1, 'do not zero a live database');
    }
  });

  it('never installs stale PLE pins across the (a∨b)∧(¬a∨c) witness', () => {
    const expr = and(or('a', 'b'), or(not('a'), 'c'));
    const solver = createSolver(expr);
    const reference = referenceModels(expr);
    const assumptionSets: VariableAssignments[] = [
      {},
      { c: Value.FALSE },
      { a: Value.TRUE },
      { b: Value.FALSE },
      {},
    ];
    for (const assumptions of assumptionSets) {
      assertResult(expr, assumptions, reference, solver.solve(assumptions));
    }
    assert.deepStrictEqual(solver.solve({ c: Value.FALSE }), {
      a: Value.FALSE,
      b: Value.TRUE,
      c: Value.FALSE,
    });
  });

  it('checks assumptions before SAT even when every named variable is already assigned at root', () => {
    const expr = and('a', 'b');
    const solver = createSolver(expr);
    const reference = referenceModels(expr);
    const assumptionSets: VariableAssignments[] = [
      { a: Value.FALSE },
      { a: Value.TRUE, b: Value.FALSE },
      { b: Value.TRUE, a: Value.TRUE },
      { a: Value.UNSET },
      {},
    ];
    for (const assumptions of assumptionSets) {
      const stats = counters(999);
      assertResult(expr, assumptions, reference, solver.solve(assumptions, stats));
      assert.deepStrictEqual(stats, counters(), 'no heuristic/implication work on a total root');
    }
  });

  it('handles empty formulas repeatedly and validates even compiler-known UNSAT', () => {
    const sat = createSolver(and());
    const unsat = createSolver(or());
    for (let call = 0; call < 3; call += 1) {
      const stats = counters(999);
      assert.deepStrictEqual(sat.solve(undefined, stats), {});
      assert.deepStrictEqual(stats, counters());
      assert.strictEqual(unsat.solve({}, stats), null);
      assert.deepStrictEqual(stats, counters());
      for (const solver of [sat, unsat]) {
        assert.throws(
          () => solver.solve({ missing: Value.UNSET }, stats),
          /unknown assumption variable: "missing"/,
        );
      }
    }
  });

  it('returns detached numeric models and retains the formula compiled at construction', () => {
    const expr = { and: [or('a', 'b')] };
    const solver = createSolver(expr);
    const model = solver.solve({ a: Value.FALSE });
    assert.ok(model !== null);
    model.a = Value.TRUE;
    model.b = Value.FALSE;
    expr.and.push(and('later'));
    assert.deepStrictEqual(solver.solve({ a: Value.FALSE }), { a: Value.FALSE, b: Value.TRUE });
    assert.throws(
      () => solver.solve({ later: Value.UNSET }),
      /unknown assumption variable: "later"/,
    );
  });

  it('forwards only variablePriority, never constructor assumptions, stats, PLE or internal knobs', (t) => {
    const original = Solver.prototype.solveAssuming;
    t.mock.method(
      Solver.prototype,
      'solveAssuming',
      function (this: Solver, ...args: Parameters<Solver['solveAssuming']>) {
        assert.strictEqual(internals(this).enablePle, false);
        assert.strictEqual(internals(this).restartBaseConflicts, 100);
        assert.strictEqual(internals(this).learnedClauseReductionThreshold, 10_000);
        assert.strictEqual(internals(this).maxConflicts, undefined);
        return original.apply(this, args);
      },
    );
    const ignoredStats = counters(999);
    const options = {
      variablePriority: undefined,
      assumptions: { a: Value.TRUE },
      stats: ignoredStats,
      enablePle: true,
      restartBaseConflicts: 1,
      learnedClauseReductionThreshold: 1,
      maxConflicts: 0,
    };
    assert.deepStrictEqual(createSolver(or('a', 'b'), options).solve({ a: Value.FALSE }), {
      a: Value.FALSE,
      b: Value.TRUE,
    });
    assert.deepStrictEqual(ignoredStats, counters(999));
  });
});

describe('incremental MiniSat prefix in the shared decision loop', () => {
  it('continues after a genuine 3→0 backjump on a NON-assumption variable and re-enqueues both assumptions', () => {
    const expr = belowPrefix();
    const base = compile(expr);
    const solver = new IncrementalAudit(base, {
      variablePriority: (unassigned) => (unassigned.includes('x') ? ['x', false] : null),
    });
    const assumptions = { b: Value.TRUE, a: Value.TRUE };
    const result = solver.solveAssuming(assumptions);
    assertResult(expr, assumptions, referenceModels(expr), result);
    assert.strictEqual(solver.analyses.length, 1);
    assert.deepStrictEqual(solver.analyses[0], {
      from: 3,
      backjumpLevel: 0,
      lits: [literal(base, 'x')],
      levels: [3],
      lbd: 1,
      call: 1,
    });
    assert.deepStrictEqual(
      solver.enqueues.filter((event) => event.assumption).map((event) => [event.lit, event.level]),
      [
        [literal(base, 'b'), 1],
        [literal(base, 'a'), 2],
        [literal(base, 'b'), 1],
        [literal(base, 'a'), 2],
      ],
    );
    assert.strictEqual(solver.reason[varOf(literal(base, 'x'))], solver.admissions[0]);
    assert.strictEqual(internals(solver).permanentUnsat, false);
    assertRoot(solver);
    solver.assertCounters();
  });

  it('propagates before advancing, and gives already-TRUE root and implied assumptions dummy levels', () => {
    const expr = and('root', implies('b', 'a'), free('z'), free('free'));
    const base = compile(expr);
    const solver = new IncrementalAudit(base, {
      variablePriority: (unassigned, partial) => {
        assert.deepStrictEqual(unassigned, ['free']);
        assert.deepStrictEqual(partial, {
          a: Value.TRUE,
          b: Value.TRUE,
          root: Value.TRUE,
          z: Value.FALSE,
        });
        assert.strictEqual(solver.trailLim.length, 4);
        return null;
      },
    });
    const assumptions = { b: Value.TRUE, a: Value.TRUE, root: Value.TRUE, z: Value.FALSE };
    assertResult(expr, assumptions, referenceModels(expr), solver.solveAssuming(assumptions));
    const levels = solver.levels.filter((event) => event.pending !== undefined);
    assert.deepStrictEqual(
      levels.map((event) => event.value),
      [Value.UNSET, Value.TRUE, Value.TRUE, Value.UNSET],
    );
    assert.deepStrictEqual(
      levels.map((event) => event.level),
      [1, 2, 3, 4],
    );
    assert.strictEqual(levels[1].boundary, levels[2].boundary, 'first dummy enqueues nothing');
    assert.strictEqual(levels[2].boundary, levels[3].boundary, 'second dummy enqueues nothing');
    assert.strictEqual(solver.enqueues.filter((event) => event.assumption).length, 2);
    assert.strictEqual(solver.stats.decisions, 1, 'dummy and actual assumptions are not decisions');
    assert.strictEqual(solver.stats.propagations, 2, 'constructor root and b→a, not assumptions');
    assertRoot(solver);
    solver.assertCounters();
  });

  for (const trailing of [false, true]) {
    it(`detects a conflict after ${
      trailing ? 'an early' : 'the last'
    } assumption without losing later-call satisfiability`, () => {
      const expr = and(or(not('a'), not('b'), 'x'), or(not('a'), not('b'), not('x')), free('c'));
      const base = compile(expr);
      const solver = new IncrementalAudit(base);
      const assumptions: VariableAssignments = trailing
        ? { a: Value.TRUE, b: Value.TRUE, c: Value.TRUE }
        : { a: Value.TRUE, b: Value.TRUE };
      assert.strictEqual(solver.solveAssuming(assumptions), null);
      assert.strictEqual(solver.analyses.length, 1);
      assert.strictEqual(solver.analyses[0].from, 2);
      assert.strictEqual(solver.analyses[0].backjumpLevel, 1);
      assert.ok(
        !solver.enqueues.some(
          (event) => event.assumption && varOf(event.lit) === base.nameToIndex.get('c'),
        ),
      );
      assert.strictEqual(internals(solver).permanentUnsat, false);
      assertRoot(solver);
      const compatibleAssumptions: VariableAssignments[] = [
        { a: Value.FALSE, b: Value.TRUE },
        { b: Value.FALSE },
        {},
      ];
      for (const compatible of compatibleAssumptions) {
        assertResult(expr, compatible, referenceModels(expr), solver.solveAssuming(compatible));
        assertRoot(solver);
      }
      solver.assertCounters();
    });
  }

  it('detects a falsified implied assumption without pretending it is a propagation conflict', () => {
    const expr = implies('a', 'b');
    const solver = new IncrementalAudit(compile(expr));
    const stats = counters(999);
    assert.strictEqual(solver.solveAssuming({ a: Value.TRUE, b: Value.FALSE }, stats), null);
    assert.deepStrictEqual(stats, { ...counters(), propagations: 1 });
    assert.strictEqual(internals(solver).permanentUnsat, false);
    assertRoot(solver);
    assertResult(expr, {}, referenceModels(expr), solver.solveAssuming());
    solver.assertCounters();
  });

  it('checks assumptions against a newly learned total root model without caching call-local UNSAT', () => {
    const expr = and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'));
    const solver = new IncrementalAudit(compile(expr));
    assert.deepStrictEqual(solver.solveAssuming(), { a: Value.TRUE, b: Value.TRUE });
    assert.strictEqual(solver.trail.length, 2, 'learned root unit and its root implication');
    const stats = counters(999);
    assert.strictEqual(solver.solveAssuming({ b: Value.FALSE }, stats), null);
    assert.deepStrictEqual(stats, { ...counters(), learnedClausesCurrent: 1 });
    assert.strictEqual(internals(solver).permanentUnsat, false);
    assert.deepStrictEqual(solver.solveAssuming(), { a: Value.TRUE, b: Value.TRUE });
    assertRoot(solver);
    solver.assertCounters();
  });

  it('snapshots getters and call order once, including replay after a callback mutates the caller record', () => {
    const expr = belowPrefix();
    let reads = 0;
    let value = Value.TRUE;
    const assumptions = {
      b: Value.TRUE,
      get a() {
        reads += 1;
        return value;
      },
    };
    const solver = createSolver(expr, {
      variablePriority: (unassigned) => {
        value = Value.FALSE;
        assumptions.b = Value.FALSE;
        return unassigned.includes('x') ? ['x', false] : null;
      },
    });
    const first = solver.solve(assumptions);
    assertResult(expr, { b: Value.TRUE, a: Value.TRUE }, referenceModels(expr), first);
    assert.strictEqual(reads, 1, 'backjump replay never re-reads the caller');
    const next = solver.solve(assumptions);
    assertResult(expr, { b: Value.FALSE, a: Value.FALSE }, referenceModels(expr), next);
    assert.strictEqual(reads, 2, 'a new call takes a fresh snapshot');
  });
});

describe('incremental validation, cached UNSAT, and exception cleanup', () => {
  const globallyUnsat = () =>
    and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'), or(not('a'), not('b')));

  for (const assumed of [false, true]) {
    it(`caches a genuine searched root conflict (${
      assumed ? 'first exposed under assumptions' : 'base call'
    }) and does no later work`, () => {
      const expr = globallyUnsat();
      assert.deepStrictEqual(referenceModels(expr), []);
      const solver = new IncrementalAudit(compile(expr));
      const stats = counters(999);
      assert.strictEqual(
        solver.solveAssuming(assumed ? { a: Value.TRUE } : undefined, stats),
        null,
      );
      assert.ok(stats.conflicts > 0 && stats.learnedClauses > 0);
      assert.strictEqual(internals(solver).permanentUnsat, true);
      const lifetime = { ...solver.stats };
      const assumptionSets: VariableAssignments[] = [{}, { a: Value.FALSE }, { b: Value.UNSET }];
      for (const assumptions of assumptionSets) {
        assert.strictEqual(solver.solveAssuming(assumptions, stats), null);
        assert.deepStrictEqual(stats, {
          ...counters(),
          learnedClausesCurrent: lifetime.learnedClausesCurrent,
        });
        assert.deepStrictEqual(solver.stats, lifetime, 'cached UNSAT is not new work');
        assertRoot(solver);
      }
      solver.assertCounters();
    });
  }

  it('validates every entry before cached UNSAT, including unknown UNSET and all invalid/coerced values', () => {
    const invalid: unknown[] = [
      true,
      false,
      2,
      -2,
      Number.NaN,
      Number.POSITIVE_INFINITY,
      '1',
      '0',
      null,
      undefined,
      1n,
      Symbol('value'),
      [],
      {},
      new Number(1),
    ];
    for (const expr of [and('a'), and(or(), 'a'), and('a', not('a')), globallyUnsat()]) {
      const solver = createSolver(expr);
      solver.solve();
      for (const value of [Value.UNSET, Value.FALSE, Value.TRUE]) {
        const stats = counters(999);
        assert.throws(
          () => solver.solve({ a: Value.FALSE, missing: value }, stats),
          /unknown assumption variable: "missing"/,
        );
        assert.strictEqual(stats.decisions, 0, 'zero before validation, even after cached UNSAT');
      }
      for (const value of invalid) {
        const stats = counters(999);
        assert.throws(
          () => solver.solve({ a: value } as VariableAssignments, stats),
          /invalid assumption value for "a"/,
        );
        assert.strictEqual(stats.decisions, 0);
        assert.strictEqual(stats.conflicts, 0);
      }
      assertResult(
        expr,
        { a: Value.UNSET },
        referenceModels(expr),
        solver.solve({ a: Value.UNSET }),
      );
    }
  });

  it('preserves own arbitrary string names, numeric key order, and numeric assumption values', () => {
    const names = [
      '__proto__',
      'constructor',
      'toString',
      'hasOwnProperty',
      '',
      '10',
      '2',
      'a=0,b',
      'quote"\\\nλ',
    ];
    const expr = and(...names.map(free));
    const base = compile(expr);
    const solver = new IncrementalAudit(base);
    for (const value of [Value.FALSE, Value.TRUE]) {
      const assumptions = Object.fromEntries(names.map((name) => [name, value]));
      const model = solver.solveAssuming(assumptions);
      assert.deepStrictEqual(model, assumptions);
      assertModelShape(model, expr);
      const call = solver.calls;
      assert.deepStrictEqual(
        solver.enqueues
          .filter((event) => event.call === call && event.assumption)
          .map((event) => base.indexToName[varOf(event.lit)]),
        Object.keys(assumptions),
        'JS own-key call order, NOT sorted compiler order',
      );
      assertRoot(solver);
    }
    const inherited = Object.create({ missing: Value.TRUE }) as VariableAssignments;
    Object.defineProperty(inherited, '__proto__', { value: Value.FALSE, enumerable: true });
    const model = solver.solveAssuming(inherited);
    assert.ok(model !== null);
    assertModelShape(model, expr);
    assert.strictEqual(model.__proto__, Value.FALSE);
    solver.assertCounters();
  });

  it('finishes validation before installing any assumptions and recovers from throwing getters', () => {
    const solver = new IncrementalAudit(compile(belowPrefix()));
    assert.throws(
      () => solver.solveAssuming({ a: Value.TRUE, unknown: Value.UNSET }),
      /unknown assumption/,
    );
    assert.deepStrictEqual(solver.enqueues, []);
    const error = new Error('caller getter failed');
    assert.throws(
      () =>
        solver.solveAssuming({
          a: Value.TRUE,
          get b(): Value {
            throw error;
          },
        }),
      (thrown) => thrown === error,
    );
    assertRoot(solver);
    assert.deepStrictEqual(solver.enqueues, []);
    assertResult(
      belowPrefix(),
      { a: Value.FALSE },
      referenceModels(belowPrefix()),
      solver.solveAssuming({ a: Value.FALSE }),
    );
    assertRoot(solver);
    solver.assertCounters();
  });

  it('cleans up a throwing hook after learning while retaining sound root reasons, phases and VSIDS', () => {
    const expr = belowPrefix();
    const base = compile(expr);
    const error = new Error('priority failed after learning');
    let fail = true;
    const solver = new IncrementalAudit(base, {
      variablePriority: (unassigned) => {
        if (unassigned.includes('x')) return ['x', false];
        if (fail) {
          fail = false;
          throw error;
        }
        return null;
      },
    });
    const stats = counters(999);
    assert.throws(
      () => solver.solveAssuming({ a: Value.TRUE, b: Value.TRUE }, stats),
      (thrown) => thrown === error,
    );
    assert.strictEqual(stats.learnedClauses, 1);
    assert.strictEqual(stats.conflicts, 1);
    assert.strictEqual(internals(solver).permanentUnsat, false);
    assert.strictEqual(internals(solver).incrementalCallActive, false);
    assert.ok(solver.activity.some((score) => score > 0));
    assert.strictEqual(solver.reason[varOf(literal(base, 'x'))], solver.admissions[0]);
    assert.strictEqual(solver.polarity[varOf(literal(base, 'a'))], Value.TRUE);
    assertRoot(solver);
    const previous = { ...stats };
    const assumptions = { a: Value.FALSE, b: Value.FALSE };
    assertResult(expr, assumptions, referenceModels(expr), solver.solveAssuming(assumptions));
    assert.deepStrictEqual(stats, previous, 'later calls do not keep writing an old output object');
    assertRoot(solver);
    solver.assertCounters();
  });

  it('also recovers through the public handle, and guards reentrant hooks without cancelling the outer call', () => {
    let fail = true;
    let nested = true;
    const expr = and(implies('a', 'b'), free('c'));
    const solver = createSolver(expr, {
      variablePriority: (_unassigned, assigned) => {
        if (fail) {
          fail = false;
          throw new Error('public hook failure');
        }
        if (nested) {
          nested = false;
          assert.throws(() => solver.solve(), /cannot be reentered/);
          assert.strictEqual(assigned.a, Value.TRUE);
          assert.strictEqual(assigned.b, Value.TRUE);
        }
        return null;
      },
    });
    assert.throws(() => solver.solve({ a: Value.TRUE }), /public hook failure/);
    assertResult(expr, { a: Value.TRUE }, referenceModels(expr), solver.solve({ a: Value.TRUE }));
    assertResult(expr, { a: Value.FALSE }, referenceModels(expr), solver.solve({ a: Value.FALSE }));
  });

  it('cancels before publishing into throwing output setters and releases the call guard', () => {
    const expr = and(free('a'), free('b'));
    const solver = new IncrementalAudit(compile(expr));
    const stats = counters();
    Object.defineProperty(stats, 'decisions', {
      get: () => 0,
      set: (value: number) => {
        if (value > 0) {
          assertRoot(solver);
          throw new Error('output setter failed');
        }
      },
    });
    assert.throws(() => solver.solveAssuming({ a: Value.TRUE }, stats), /output setter failed/);
    assertRoot(solver);
    assert.strictEqual(internals(solver).incrementalCallActive, false);
    assert.throws(() => solver.solveAssuming(undefined, Object.freeze(counters())), TypeError);
    assertRoot(solver);
    assertResult(
      expr,
      { a: Value.FALSE },
      referenceModels(expr),
      solver.solveAssuming({ a: Value.FALSE }),
    );
    solver.assertCounters();
  });

  it('remembers a proven root conflict before a hard-cap exception can leave an already-drained queue', () => {
    const expr = and(or('a', 'b'), not('a'), not('b'));
    const solver = new Solver(compile(expr), { maxConflicts: 1 });
    const stats = counters(999);
    assert.throws(
      () => solver.solveAssuming(undefined, stats),
      /maximum conflict budget exhausted \(1\)/,
    );
    assert.strictEqual(stats.conflicts, 1);
    assert.strictEqual(internals(solver).permanentUnsat, true);
    const lifetime = { ...solver.stats };
    for (let repeat = 0; repeat < 4; repeat += 1) {
      assert.strictEqual(solver.solveAssuming(undefined, stats), null);
      assert.deepStrictEqual(stats, counters());
      assert.deepStrictEqual(solver.stats, lifetime);
      assertRoot(solver);
    }
  });

  it('refuses incremental reuse of a PLE-enabled internal solver or its lifetime ledger as an output', () => {
    const solver = new Solver(compile(or('a', 'b')), { enablePle: true });
    assert.throws(() => solver.solveAssuming(), /incremental solving requires enablePle: false/);
    assertRoot(solver);
    const safe = new Solver(compile(or('a', 'b')));
    assert.throws(
      () => safe.solveAssuming(undefined, safe.stats),
      /separate from the lifetime ledger/,
    );
    assertResult(or('a', 'b'), {}, referenceModels(or('a', 'b')), safe.solveAssuming());
  });
});

// Resolving t derives (¬a∨¬b∨¬xi). a=b=TRUE, every xi=FALSE is a
// satisfiable context with genuine LBD 3; changing the targeted xi exposes new
// conflicts across calls without synthesizing clauses, activities or counters.
const gadgets = (count: number) =>
  and(
    ...Array.from({ length: count }, (_, index) =>
      and(
        or(not('a'), not(`x${index}`), 't'),
        or(not('b'), not(`x${index}`), not('t')),
        or('a', 'b', `x${index}`, 't'),
      ),
    ),
  );

describe('incremental stats scope and retained database cadence', () => {
  it('counts work during solve only, never replays constructor units or retained root implications', () => {
    const expr = and('root', implies('root', 'forced'), free('free'));
    const base = compile(expr);
    const solver = new IncrementalAudit(base);
    assert.strictEqual(solver.stats.propagations, 1, 'constructor unit really was enqueued');
    const stats = counters(999);
    assertResult(expr, {}, referenceModels(expr), solver.solveAssuming(undefined, stats));
    assert.deepStrictEqual(stats, { ...counters(), decisions: 1, propagations: 1 });
    assert.strictEqual(solver.stats.propagations, 2, 'lifetime includes construction');
    const rootReasons = [...solver.reason];
    assertResult(
      expr,
      { free: Value.TRUE },
      referenceModels(expr),
      solver.solveAssuming({ free: Value.TRUE }, stats),
    );
    assert.deepStrictEqual(stats, counters(), 'assumption is not a decision or propagation');
    assert.deepStrictEqual(solver.reason, rootReasons);
    assertRoot(solver);
    solver.assertCounters();
  });

  it('keeps output calls isolated, including omitted/reused/distinct outputs and validation-error live snapshots', () => {
    const expr = lostAssumption();
    const solver = createSolver(expr);
    assert.strictEqual(solver.solve({ a: Value.TRUE }), null, 'learning with no output object');
    const first = counters(999);
    assert.strictEqual(solver.solve({ a: Value.TRUE }, first), null);
    assert.deepStrictEqual(first, { ...counters(), learnedClausesCurrent: 1 });
    const second = counters(-99);
    assert.ok(solver.solve(undefined, second) !== null);
    assert.deepStrictEqual(second, { ...counters(), decisions: 1, learnedClausesCurrent: 1 });
    assert.deepStrictEqual(first, { ...counters(), learnedClausesCurrent: 1 });
    assert.throws(() => solver.solve({ unknown: Value.UNSET }, second), /unknown assumption/);
    assert.deepStrictEqual(second, { ...counters(), learnedClausesCurrent: 1 });
    assert.throws(
      () => solver.solve({ a: true } as unknown as VariableAssignments, first),
      /invalid assumption/,
    );
    assert.deepStrictEqual(first, { ...counters(), learnedClausesCurrent: 1 });
  });

  it('preserves admission cadence across output resets and actually deletes/re-derives high-LBD clauses across calls', (t) => {
    const expr = gadgets(5);
    const base = compile(expr);
    const reference = referenceModels(expr);
    const truth = cnfTruthTable(base);
    let target = 'x0';
    let firstHook = false;
    const stats = counters(999);
    const priority: VariablePriority = (unassigned) => {
      if (firstHook) {
        firstHook = false;
        assert.deepStrictEqual(stats, counters(), 'all public outputs reset before work');
        Object.assign(stats, counters(987), { conflicts: Number.NaN });
      }
      if (unassigned.includes(target)) return [target, true];
      const x = unassigned.find((name) => name.startsWith('x'));
      return x === undefined ? null : [x, false];
    };
    const solver = new IncrementalAudit(base, {
      variablePriority: priority,
      restartBaseConflicts: 1,
      learnedClauseReductionThreshold: 3,
    });
    solver.verifyLearned = (clause) => assertEntailed(truth, clause);
    const outputs = [];
    for (let call = 0; call < 15; call += 1) {
      target = `x${call % 5}`;
      firstHook = true;
      Object.assign(stats, counters(999));
      const before = { ...solver.stats };
      const assumptions = { a: Value.TRUE, b: Value.TRUE };
      assertResult(expr, assumptions, reference, solver.solveAssuming(assumptions, stats));
      const expected = {
        ...counters(),
        learnedClausesCurrent: solver.clauses.filter((clause) => clause.learned).length,
      };
      for (const key of [
        'decisions',
        'propagations',
        'conflicts',
        'restarts',
        'learnedClauses',
      ] as const) {
        expected[key] = solver.stats[key] - before[key];
      }
      assert.deepStrictEqual(stats, expected);
      outputs.push({ ...stats });
      assertRoot(solver);
      solver.assertCounters();
    }
    assert.ok(solver.reductions.length > 1);
    assert.deepStrictEqual(
      solver.reductions.map((round) => round.total),
      solver.reductions.map((_, index) => (index + 1) * 3),
    );
    assert.ok(
      solver.reductions.every((round) => round.call > 1),
      'cadence spans completed calls',
    );
    assert.ok(solver.reductions.filter((round) => round.removed.length > 0).length > 1);
    assert.ok(solver.stats.restarts > 0);
    assert.ok(solver.analyses.every((analysis) => analysis.lbd === 3));
    assert.ok(
      outputs.some((output) => output.learnedClauses === 0 && output.learnedClausesCurrent > 0),
    );
    const removed = solver.reductions.flatMap((round) => round.removed);
    assert.ok(
      removed.some((dead) =>
        solver.admissions.some(
          (clause) =>
            clause !== dead &&
            [...clause.lits].sort().join(',') === [...dead.lits].sort().join(','),
        ),
      ),
      'real re-derivation after deletion, not stale canonical identity',
    );
    t.diagnostic(
      `15 calls, base1/threshold3: ${JSON.stringify(solver.stats)}; ${
        solver.reductions.length
      } rounds; ${removed.length} deletions`,
    );
  });

  it('keeps the hard conflict cap lifetime-private across per-call output resets and never substitutes UNSAT for exhaustion', () => {
    const expr = gadgets(3);
    let target = 'x0';
    const solver = new Solver(compile(expr), {
      restartBaseConflicts: 1,
      maxConflicts: 3,
      variablePriority: (unassigned) => {
        if (unassigned.includes(target)) return [target, true];
        const x = unassigned.find((name) => name.startsWith('x'));
        return x === undefined ? null : [x, false];
      },
    });
    const stats = counters(999);
    for (let call = 0; call < 3; call += 1) {
      target = `x${call}`;
      if (call < 2) {
        assertResult(
          expr,
          { a: Value.TRUE, b: Value.TRUE },
          referenceModels(expr),
          solver.solveAssuming({ a: Value.TRUE, b: Value.TRUE }, stats),
        );
      } else {
        assert.throws(
          () => solver.solveAssuming({ a: Value.TRUE, b: Value.TRUE }, stats),
          /maximum conflict budget exhausted \(3\)/,
        );
      }
      assert.strictEqual(stats.conflicts, 1, 'per-call work, not cumulative output');
      assert.strictEqual(internals(solver).conflictsSoFar, call + 1, 'cap does not rewind');
      assert.strictEqual(internals(solver).permanentUnsat, false);
      assertRoot(solver);
    }
    assertResult(
      expr,
      { a: Value.FALSE },
      referenceModels(expr),
      solver.solveAssuming({ a: Value.FALSE }, stats),
    );
    assert.strictEqual(stats.conflicts, 0);
    assert.strictEqual(internals(solver).conflictsSoFar, 3);
  });
});

describe('retained learning is independently entailed without the exposing assumptions', () => {
  it('keeps conditional learned clauses but not conditional root pins on subsequent calls', () => {
    const expr = and(or(not('a'), not('x'), 't'), or(not('a'), not('x'), not('t')));
    const base = compile(expr);
    const truth = cnfTruthTable(base);
    const solver = new IncrementalAudit(base, {
      variablePriority: (unassigned) => (unassigned.includes('x') ? ['x', true] : null),
    });
    solver.verifyLearned = (clause) => assertEntailed(truth, clause);
    const assumptions = { a: Value.TRUE };
    assertResult(expr, assumptions, referenceModels(expr), solver.solveAssuming(assumptions));
    assert.strictEqual(solver.admissions.length, 1);
    assert.deepStrictEqual(
      [...solver.admissions[0].lits].sort((a, b) => a - b),
      [literal(base, 'a', Value.FALSE), literal(base, 'x', Value.FALSE)],
    );
    assert.deepStrictEqual(solver.trail, [], 'conditional assertion is not a permanent root fact');
    const retained = solver.admissions[0];
    const assumptionSets: VariableAssignments[] = [
      { a: Value.FALSE, x: Value.TRUE },
      { x: Value.TRUE },
      { a: Value.TRUE, x: Value.TRUE },
      {},
    ];
    for (const partial of assumptionSets) {
      assertResult(expr, partial, referenceModels(expr), solver.solveAssuming(partial));
      assert.ok(solver.clauses.includes(retained));
      assertRoot(solver);
    }
    solver.assertCounters();
  });

  it('checks real auxiliary learning against the FULL base-CNF truth table across calls and forced restarts', () => {
    const expr = and(or(not('v'), and('x', 't'), and('x', not('t'))), or('v', 'x', 't'));
    const base = compile(expr);
    assert.ok(base.numVars > base.numNamedVars);
    const truth = cnfTruthTable(base);
    const reference = referenceModels(expr);
    assertModelListsEqual(
      truth.map((model) =>
        Object.fromEntries(base.indexToName.map((name, index) => [name, model[index]])),
      ),
      reference,
    );
    const solver = new IncrementalAudit(base, {
      restartBaseConflicts: 1,
      learnedClauseReductionThreshold: 1,
      variablePriority: (unassigned) => (unassigned.includes('x') ? ['x', false] : null),
    });
    solver.verifyLearned = (clause) => assertEntailed(truth, clause);
    const assumptionSets: VariableAssignments[] = [
      { v: Value.TRUE },
      { v: Value.FALSE, x: Value.FALSE },
      { v: Value.TRUE, x: Value.FALSE },
      { x: Value.TRUE },
      {},
    ];
    for (const assumptions of assumptionSets) {
      assertResult(expr, assumptions, reference, solver.solveAssuming(assumptions));
      assertRoot(solver);
    }
    assert.ok(solver.analyses.length > 0);
    assert.ok(solver.activity.slice(base.numNamedVars).some((score) => score > 0));
    assert.ok(solver.stats.restarts > 0);
    solver.assertCounters();
  });

  it('checks EVERY analyzed clause, including ones later deleted, against independent seeded base models', (t) => {
    let analyses = 0;
    let formulas = 0;
    let calls = 0;
    for (let seed = 0; seed < 64; seed += 1) {
      const expr = cnfToExpr(random3Cnf(mulberry32(seed), 7, 28));
      const reference = referenceModels(expr);
      const base = compile(expr);
      const truth = cnfTruthTable(base);
      if (reference.length === 0) continue; // entailment must NOT pass vacuously
      assert.ok(truth.length > 0);
      formulas += 1;
      const solver = new IncrementalAudit(base, {
        restartBaseConflicts: 1,
        learnedClauseReductionThreshold: 1,
      });
      solver.verifyLearned = (clause) => {
        assertEntailed(truth, clause);
        analyses += 1;
      };
      const rng = mulberry32(30_000 + seed);
      for (let call = 0; call < 8; call += 1) {
        const assumptions =
          call === 0 || call === 7
            ? {}
            : Object.fromEntries(
                base.indexToName
                  .filter(() => rng.boolean())
                  .map((name) => [name, rng.pick([Value.FALSE, Value.TRUE, Value.UNSET])]),
              );
        assertResult(expr, assumptions, reference, solver.solveAssuming(assumptions));
        assertRoot(solver);
        solver.assertCounters();
        calls += 1;
      }
    }
    assert.ok(formulas > 0 && analyses > 0);
    assert.strictEqual(calls, formulas * 8);
    t.diagnostic(
      `${formulas} SAT base formulas; ${calls} calls; ${analyses} non-vacuous learned entailments`,
    );
  });
});

describe('incremental independent acceptance oracles reject invalid evidence', () => {
  it('rejects Boolean values, inherited keys, missing keys, bad verdicts and assumption-violating models', () => {
    const expr = or('a', 'b');
    const reference = referenceModels(expr);
    const assumptions = { a: Value.TRUE };
    for (const invalid of [
      { a: true, b: Value.FALSE },
      { a: Value.TRUE, b: false },
      { a: Value.UNSET, b: Value.TRUE },
      { a: Value.TRUE },
      Object.create({ a: Value.TRUE, b: Value.FALSE }),
      { a: Value.FALSE, b: Value.FALSE },
      { a: Value.FALSE, b: Value.TRUE },
      null,
    ]) {
      assert.throws(
        () => assertResult(expr, assumptions, reference, invalid as VariableAssignments),
        { name: 'AssertionError' },
      );
    }
    assert.throws(
      () => assertResult(and('a', not('a')), {}, [], { a: Value.TRUE }),
      /reference verdict/,
    );
    assert.strictEqual(
      extendsAssumptions({ a: true } as unknown as VariableAssignments, { a: Value.TRUE }),
      false,
    );
    assert.strictEqual(
      extendsAssumptions(Object.create({ a: Value.TRUE }), { a: Value.TRUE }),
      false,
    );
    const base = compile(free('a'));
    assert.throws(
      () =>
        assertEntailed(cnfTruthTable(base), {
          lits: [literal(base, 'a')],
          learned: true,
          lbd: 1,
          activity: 0,
        }),
      /learned clause holds/,
    );
  });
});
