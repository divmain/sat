import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, not, or, Value } from '../src/expr.js';
import type { BooleanExpr } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import {
  cnfToExpr,
  expectSatModel,
  expressionValue,
  mulberry32,
  phpCnf,
  random3Cnf,
} from './helpers.js';
import { IncrementalAudit, internals, literal } from './incremental-helpers.js';

const key = (clause: Clause | null): string | null =>
  clause === null ? null : [...clause.lits].sort((a, b) => a - b).join(',');

function snapshot(solver: Solver) {
  return {
    trail: [...solver.trail],
    levels: [...solver.trailLim],
    qhead: solver.qhead,
    assigns: [...solver.assigns],
    reasons: solver.reason.map(key),
    activity: [...solver.activity],
    polarity: [...solver.polarity],
    clauses: solver.clauses.map((clause) => ({ ...clause, lits: [...clause.lits] })),
    watches: solver.watches.map((list) =>
      list.map((entry) => ({ clause: key(entry.clause), blocker: entry.blocker })),
    ),
    stats: { ...solver.stats },
  };
}

// Observe real operations, never inject scores, learned clauses or counters.
class TraceSolver extends Solver {
  readonly events: unknown[] = [];
  readonly boundaries: number[] = [];
  pendingAssertion = false;

  override enqueue(lit: number, reason: Clause | null): boolean {
    const unset = this.assigns[varOf(lit)] === Value.UNSET;
    const result = super.enqueue(lit, reason);
    if (result && unset) {
      this.events?.push(['enqueue', lit, key(reason), [...this.trail], [...this.trailLim]]);
      if (reason !== null) this.pendingAssertion = false;
    }
    return result;
  }

  override analyze(conflict: Clause) {
    const result = super.analyze(conflict);
    this.pendingAssertion = true;
    this.events.push(['analyze', key(conflict), result]);
    return result;
  }

  override cancelUntil(level: number): void {
    this.events.push(['cancel', level, [...this.trail], this.stats.conflicts]);
    super.cancelUntil(level);
  }

  override reduceLearnedClauses(): void {
    super.reduceLearnedClauses();
    this.events.push(['reduce', this.clauses.map(key), { ...this.stats }]);
  }

  override addPermanentClause(lits: readonly number[]): Clause | null {
    const result = super.addPermanentClause(lits);
    this.boundaries.push(this.stats.decisions);
    this.events.push(['blocker', [...lits], [...this.trail]]);
    return result;
  }
}

function sliced(solver: Solver, quantum: number, assumptions: readonly number[] = []) {
  solver.startSearch(assumptions);
  let pauses = 0;
  let result = solver.searchSlice(quantum);
  while (result === 'paused') {
    solver.checkInvariants();
    if (solver instanceof TraceSolver) assert.strictEqual(solver.pendingAssertion, false);
    assert.ok(++pauses < 1_000_000, 'finite scheduling makes progress');
    result = solver.searchSlice(quantum);
  }
  return { result, pauses };
}

function rawCnf(count: number, lits: number[][]): CompiledCnf {
  const names = Array.from({ length: count }, (_, index) => `v${index}`);
  return {
    numVars: count,
    numNamedVars: count,
    nameToIndex: new Map(names.map((name, index) => [name, index])),
    indexToName: names,
    levelZeroUnsat: false,
    clauses: lits.map((row) => ({ lits: [...row], learned: false, activity: 0, lbd: 0 })),
  };
}

describe('resumable search parity', () => {
  for (const quantum of [1, 2, 3, 17]) {
    for (const [name, expr] of [
      ['PHP(5,4)', cnfToExpr(phpCnf(5, 4))],
      ['seeded SAT', cnfToExpr(random3Cnf(mulberry32(42), 20, 85))],
      ['root gates', and('a', implies('a', and('b', 'c')), or('d', 'e'))],
    ] as const) {
      it(`${name}, quantum ${quantum}: exact transactions, trails, watches and counters`, () => {
        const options = {
          restartPolicy: 'luby' as const,
          restartBaseConflicts: 1,
          learnedClauseReductionThreshold: 2,
        };
        const whole = new TraceSolver(compile(expr), options);
        const paused = new TraceSolver(compile(expr), options);
        const expected = whole.solve();
        const actual = sliced(paused, quantum);
        assert.strictEqual(actual.result, expected ? 'sat' : 'unsat');
        if (name !== 'root gates' || quantum < 17) assert.ok(actual.pauses > 0);
        assert.deepStrictEqual(snapshot(paused), snapshot(whole));
        assert.deepStrictEqual(paused.events, whole.events);
        if (expected) {
          assert.deepStrictEqual(paused.model(), whole.model());
          assert.strictEqual(expressionValue(expr, paused.model()), Value.TRUE);
        }
        if (name === 'PHP(5,4)') {
          assert.ok(paused.stats.restarts > 0);
          assert.ok(paused.events.some((event) => Array.isArray(event) && event[0] === 'reduce'));
        }
      });
    }
  }

  for (const relocation of [false, true]) {
    it(`pauses in a long ${relocation ? 'relocation-only' : 'satisfied-watch'} scan`, () => {
      const rows = Array.from({ length: 80 }, (_, index) =>
        relocation ? [1, (index + 2) * 2, 2] : [1, 2, (index + 2) * 2],
      );
      const make = () => rawCnf(82, [[0], [2], ...rows]);
      const solver = new TraceSolver(make());
      const whole = new TraceSolver(make());
      const initial = { ...solver.stats };
      for (let index = 0; index < rows.length; index += 1) {
        assert.strictEqual(solver.searchSlice(1), 'paused');
        assert.deepStrictEqual(solver.stats, initial, 'inspection-only work consumes allowance');
        if (index < rows.length - 1) {
          assert.strictEqual(internals(solver).propagationCursor?.nextWatch, 78 - index);
        }
      }
      let result = solver.searchSlice(3);
      while (result === 'paused') result = solver.searchSlice(3);
      assert.strictEqual(result, whole.solve() ? 'sat' : 'unsat');
      assert.deepStrictEqual(snapshot(solver), snapshot(whole));
      assert.deepStrictEqual(solver.events, whole.events);
      assert.strictEqual(solver.watches[1].length, relocation ? 0 : 80);
    });
  }

  it('resumes one already-true prefix step at a time before SAT, then starts fresh calls', () => {
    const names = Array.from({ length: 64 }, (_, index) => `a${index}`);
    const expr = and(...names);
    const cnf = compile(expr);
    const assumptions = names.map((name) => literal(cnf, name));
    const solver = new TraceSolver(cnf);
    const whole = new TraceSolver(compile(expr));
    solver.startSearch(assumptions);
    const initial = { ...solver.stats };
    for (let index = 0; index < names.length; index += 1) {
      assert.strictEqual(solver.searchSlice(1), index === names.length - 1 ? 'sat' : 'paused');
      assert.strictEqual(solver.trailLim.length, index + 1);
      assert.deepStrictEqual(solver.stats, initial);
    }
    assert.strictEqual(whole.solve(assumptions), true);
    assert.deepStrictEqual(snapshot(solver), snapshot(whole));
    solver.finishSearch();
    solver.cancelUntil(0);
    whole.cancelUntil(0);
    const opposite = [assumptions[0] ^ 1];
    assert.strictEqual(sliced(solver, 1, opposite).result, 'unsat');
    assert.strictEqual(whole.solve(opposite), false);
    assert.deepStrictEqual(snapshot(solver), snapshot(whole));
    assert.deepStrictEqual(solver.solveAssuming(), whole.solveAssuming());
  });

  it('propagates the last unset assumption and replays prefixes after actual backjumps', () => {
    const expr = and(
      or('a', 'b', 'c'),
      or('a', 'b', not('c')),
      or('a', not('b'), 'c'),
      or('a', not('b'), not('c')),
      implies('z', 'y'),
    );
    for (const quantum of [1, 2, 5]) {
      const cnf = compile(expr);
      const assumptions = [literal(cnf, 'a', Value.FALSE), literal(cnf, 'z')];
      const whole = new TraceSolver(compile(expr), {
        restartPolicy: 'luby',
        restartBaseConflicts: 1,
      });
      const solver = new TraceSolver(cnf, { restartPolicy: 'luby', restartBaseConflicts: 1 });
      const actual = sliced(solver, quantum, assumptions);
      assert.strictEqual(actual.result, whole.solve(assumptions) ? 'sat' : 'unsat');
      assert.ok(solver.stats.learnedClauses > 0);
      assert.deepStrictEqual(snapshot(solver), snapshot(whole));
      assert.deepStrictEqual(solver.events, whole.events);
      solver.finishSearch();
      solver.cancelUntil(0);
      whole.cancelUntil(0);
      const next = [literal(cnf, 'z')];
      assert.strictEqual(sliced(solver, quantum, next).result, 'sat');
      assert.strictEqual(whole.solve(next), true);
      assert.deepStrictEqual(snapshot(solver), snapshot(whole));
      assert.strictEqual(solver.model().y, Value.TRUE);
    }
  });

  it('keeps PLE atomic and scoped, with identical sliced single-shot results', () => {
    const expr = and(or('a', 'b'), implies('b', 'c'));
    const whole = new TraceSolver(compile(expr), { enablePle: true });
    const solver = new TraceSolver(compile(expr), { enablePle: true });
    assert.strictEqual(sliced(solver, 1).result, whole.solve() ? 'sat' : 'unsat');
    assert.deepStrictEqual(snapshot(solver), snapshot(whole));
  });

  it('exhausts an inspection allowance but completes learning, restart and reduction before pausing', () => {
    const solver = new TraceSolver(compile(cnfToExpr(phpCnf(5, 4))), {
      restartPolicy: 'luby',
      restartBaseConflicts: 1,
      learnedClauseReductionThreshold: 1,
    });
    // Quantum 1 exhausts at the conflict-producing inspection. That is NOT
    // a safe pause: all parts of the transaction must nevertheless complete.
    do {
      assert.strictEqual(solver.searchSlice(1), 'paused');
    } while (solver.stats.conflicts === 0);
    assert.strictEqual(solver.stats.conflicts, 1);
    assert.strictEqual(solver.stats.learnedClauses, 1);
    assert.strictEqual(solver.stats.restarts, 1);
    const policy = internals(solver).restartPolicy;
    assert.strictEqual(policy.kind, 'luby');
    assert.strictEqual(policy.restartIndex, 2, 'the forced-Luby epoch advanced exactly once');
    assert.deepStrictEqual(solver.trailLim, []);
    assert.strictEqual(internals(solver).propagationCursor, null);
    assert.strictEqual(solver.pendingAssertion, false);
    const kinds = solver.events.map((event) => (Array.isArray(event) ? event[0] : null));
    assert.deepStrictEqual(kinds.slice(-5), ['analyze', 'cancel', 'enqueue', 'cancel', 'reduce']);
  });
});

describe('abandoned propagation and scheduling lifecycle', () => {
  it('releases standalone allowances and starts each later call with a fresh quantum', () => {
    const solver = new Solver(compile(and(or('a', not('a')), or('b', not('b')))));
    for (let call = 0; call < 3; call += 1) {
      assert.deepStrictEqual(sliced(solver, 5), { result: 'sat', pauses: 0 });
      assert.strictEqual(internals(solver).scheduling?.remaining, 1);
      solver.finishSearch();
      solver.cancelUntil(0);
      assert.strictEqual(internals(solver).scheduling, null);
      assert.strictEqual(internals(solver).searchState, null);
    }
    assert.strictEqual(solver.solveAssuming().status, 'sat');
    assert.strictEqual(internals(solver).scheduling, null);
  });

  for (const admission of [false, true]) {
    it(`requeues a retained root gate scan before ${
      admission ? 'root admission' : 'another solve'
    }`, () => {
      // v0 -> v1 is deliberately visited LAST. v2 is already true, so the
      // first inspection consumes work without an enqueue or conflict.
      const solver = new IncrementalAudit(rawCnf(3, [[0], [4], [1, 2], [1, 4]]));
      assert.strictEqual(solver.searchSlice(1), 'paused');
      assert.strictEqual(solver.qhead, 1);
      assert.strictEqual(solver.assigns[1], Value.UNSET);
      assert.strictEqual(internals(solver).propagationCursor?.event, 0);
      solver.cancelUntil(0); // The oracle must handle a root-level NO-OP too.
      assert.strictEqual(solver.qhead, 0);
      solver.finishSearch();
      if (admission) solver.addPermanentClause([3]);
      const result = solver.solveAssuming();
      if (admission) {
        assert.deepStrictEqual(
          result,
          { status: 'unsat', core: {} },
          'pending gate conflicts with the newly admitted root unit',
        );
      } else {
        assert.strictEqual(expectSatModel(result).v1, Value.TRUE);
        assert.strictEqual(solver.stats.decisions, 0, 'gate implication precedes decision/SAT');
        assert.strictEqual(solver.stats.propagations, 3, 'reinspection does not recount roots');
      }
    });
  }

  it('discards the cursor for an undone assignment instead of replaying its old polarity', () => {
    const solver = new IncrementalAudit(rawCnf(4, [[4], [1, 2], [1, 4], [1, 6]]));
    solver.propagate();
    solver.newDecisionLevel();
    solver.enqueue(0, null);
    assert.strictEqual(solver.searchSlice(1), 'paused');
    assert.ok(internals(solver).propagationCursor !== null);
    solver.cancelUntil(0);
    solver.finishSearch();
    assert.strictEqual(internals(solver).propagationCursor, null);
    assert.strictEqual(solver.qhead, solver.trail.length);
    const gated = solver.solveAssuming({ v0: Value.FALSE, v1: Value.FALSE });
    assert.strictEqual(expectSatModel(gated).v1, Value.FALSE);
  });

  it('applies the non-throwing conflictBudget contract and cleanup for partial root scans', () => {
    // Budget zero: the explicit startup exception still permits the initial
    // root-propagation pass (here resumable across slices), and the terminal
    // root conflict it finds establishes UNSAT with precedence over the
    // spent budget.
    const solver = new Solver(rawCnf(3, [[0], [3], [4], [1, 2], [1, 4]]), { conflictBudget: 0 });
    assert.strictEqual(solver.searchSlice(1), 'paused');
    assert.strictEqual(solver.searchSlice(1), 'unsat');
    assert.strictEqual(solver.stats.conflicts, 1, 'the terminal root conflict counts once');
    solver.finishSearch();
    solver.cancelUntil(0);
    // The conflict was found mid-scan: the cursor is gone, unexamined root
    // events stay queued (never mistaken for a fixpoint), and the established
    // permanent UNSAT short-circuits every later call regardless.
    assert.strictEqual(internals(solver).propagationCursor, null);
    assert.ok(solver.qhead <= solver.trail.length);
    assert.strictEqual(internals(solver).permanentUnsat, true);
    assert.deepStrictEqual(
      solver.solveAssuming(),
      { status: 'unsat', core: {} },
      'established root UNSAT survives budget exhaustion',
    );
  });

  for (const quantum of [1, 7, 64]) {
    it(`enumeration shares quantum ${quantum} across short searches and admitted blockers`, () => {
      const expr = and(
        ...Array.from({ length: 5 }, (_, index) => or(`v${index}`, not(`v${index}`))),
      );
      const whole = new TraceSolver(compile(expr));
      const solver = new TraceSolver(compile(expr));
      const expected = whole.enumerateModels();
      const driver = solver.enumerateSlices(quantum);
      let result = driver.next();
      let pauses = 0;
      let boundaryPauses = 0;
      let previousModels = 0;
      while (!result.done) {
        pauses += 1;
        if (solver.boundaries.length > previousModels && solver.trailLim.length === 0) {
          boundaryPauses += 1;
        }
        previousModels = solver.boundaries.length;
        solver.checkInvariants();
        assert.strictEqual(solver.pendingAssertion, false);
        result = driver.next();
      }
      assert.ok(pauses > 0);
      if (quantum === 1) assert.ok(boundaryPauses > 0);
      if (quantum === 64) {
        assert.ok(pauses < expected.models.length, 'many searches share each allowance');
      }
      assert.deepStrictEqual(result.value, expected);
      assert.strictEqual(expected.models.length, 32);
      assert.deepStrictEqual(snapshot(solver), snapshot(whole));
      assert.deepStrictEqual(solver.events, whole.events);
    });
  }

  it('charges even the empty-model boundary and runs cleanup when a driver is abandoned', () => {
    const empty = new Solver(compile(and()));
    const driver = empty.enumerateSlices(1);
    assert.deepStrictEqual(driver.next(), { value: 'paused', done: false });
    assert.ok(empty.clauses.some((clause) => clause.lits.length === 0));
    assert.deepStrictEqual(driver.next(), {
      value: { status: 'complete', models: [{}] },
      done: true,
    });

    const expr: BooleanExpr = and('a', implies('a', 'b'), implies('a', 'c'));
    const solver = new Solver(compile(expr));
    const abandoned = solver.enumerateSlices(1);
    assert.strictEqual(abandoned.next().done, false);
    abandoned.return({ status: 'unknown', models: [], reason: 'aborted' });
    assert.strictEqual(internals(solver).propagationCursor, null);
    assert.deepStrictEqual(solver.trailLim, []);
    assert.strictEqual(expressionValue(expr, expectSatModel(solver.solveAssuming())), Value.TRUE);
  });

  it('cleans up a finite enumeration hook failure after earlier pauses and remains reusable', () => {
    let fail = true;
    const expr = and('a', implies('a', 'b'), implies('a', 'c'), or('d', 'e'));
    const solver = new Solver(compile(expr), {
      variablePriority: () => {
        if (fail) throw new Error('priority failure');
        return null;
      },
    });
    const driver = solver.enumerateSlices(1);
    assert.strictEqual(driver.next().done, false);
    assert.throws(() => {
      while (!driver.next().done) {
        solver.checkInvariants();
      }
    }, /priority failure/);
    assert.strictEqual(internals(solver).scheduling, null);
    assert.strictEqual(internals(solver).searchState, null);
    assert.strictEqual(internals(solver).propagationCursor, null);
    assert.deepStrictEqual(solver.trailLim, []);
    fail = false;
    assert.strictEqual(expressionValue(expr, expectSatModel(solver.solveAssuming())), Value.TRUE);
  });

  it('validates internal quanta and supports cached verdicts and changed slice sizes', () => {
    const solver = new Solver(compile(or('a', 'b')));
    for (const quantum of [0, -1, 0.5, Number.NaN]) {
      assert.throws(() => solver.searchSlice(quantum), /work quantum/);
    }
    assert.strictEqual(solver.searchSlice(1), 'paused');
    assert.strictEqual(solver.searchSlice(Number.POSITIVE_INFINITY), 'sat');
    const before = snapshot(solver);
    assert.strictEqual(solver.searchSlice(1), 'sat');
    assert.deepStrictEqual(snapshot(solver), before);
  });
});
