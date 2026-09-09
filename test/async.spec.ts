// Async solving (Design § Budgets, Async, and Interruptibility): Promise
// rejection contracts, the platform-neutral scheduler fallback chain and its
// lifecycle, abort delivery at slice checkpoints via the controlled internal
// scheduler seam, reentrancy across the busy guard, and the async≡sync
// determinism oracle for identical non-aborted histories. No timer-based
// performance assertions anywhere: the only clock-sensitive check is the
// child-process liveness proof (natural exit), with a deadlock backstop.

import assert from 'node:assert';
import { spawnSync } from 'node:child_process';
import { dirname, join } from 'node:path';
import { describe, it } from 'node:test';
import { fileURLToPath } from 'node:url';
import {
  and,
  atLeast,
  atMost,
  createSolver,
  exactly,
  getAllSolutions,
  getAllSolutionsAsync,
  getSolution,
  getSolutionAsync,
  not,
  or,
  Value,
} from '../src/index.js';
import type {
  BooleanExpr,
  EnumerateResult,
  SolveResult,
  VariableAssignments,
} from '../src/index.js';
import { createSolverStats, setYieldScheduler } from '../src/solver.js';
import { expectCompleteModels, expressionValue } from './helpers.js';

// The budget-1 boundary witness from budget.spec.ts (two root conflicts to
// prove UNSAT; the first learns the root unit (a)).
const boundaryWitness = () =>
  and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'), or(not('a'), not('b')));

// A unit forces root=TRUE; propagating it scans 3×width watch entries that
// only inspect satisfied blockers or relocate watches — no propagation
// cascade, no conflict. Work before any verdict is pure scanning, so a pause
// lands mid-root-scan and stats stay at zero (no propagations, no decisions).
const wideScan = (width: number): BooleanExpr =>
  and(
    'root',
    ...Array.from({ length: width }, (_, i) => `sat${i}`),
    ...Array.from({ length: width }, (_, i) =>
      and(
        or(not('root'), `sat${i}`),
        or(not('root'), `free${i}`, `t${i}`),
        or(not('root'), `free${i}`, not(`t${i}`)),
      ),
    ),
  );

// 200 named variables, each constrained only by a tautology: assumption
// prefix replay does real per-step work without any propagation or decision.
const freeVariables = (count: number): { expr: BooleanExpr; assumptions: VariableAssignments } => ({
  expr: and(...Array.from({ length: count }, (_, i) => or(`v${i}`, not(`v${i}`)))),
  assumptions: Object.fromEntries(
    Array.from({ length: count }, (_, i) => [`v${i}`, Value.TRUE] as const),
  ),
});

const pairs = (count: number): BooleanExpr =>
  and(...Array.from({ length: count }, (_, i) => or(`a${i + 1}`, `b${i + 1}`)));

// A scheduler that aborts the controller once it has been invoked `after`
// times; every invocation otherwise resolves immediately.
const abortingScheduler = (controller: AbortController, after: number) => {
  let yields = 0;
  return () => {
    yields += 1;
    if (yields >= after) controller.abort();
    return Promise.resolve();
  };
};

describe('async validation and rejection contracts', () => {
  it('rejects — never synchronously throws — on invalid budgets, quanta, and assumptions', async () => {
    const handle = createSolver(or('a', 'b'));
    const badCalls: Array<() => Promise<unknown>> = [];
    for (const conflictBudget of [-1, 0.5, Number.NaN, Number.POSITIVE_INFINITY, 2 ** 53]) {
      badCalls.push(() => getSolutionAsync(or('a', 'b'), { conflictBudget }));
      badCalls.push(() => getAllSolutionsAsync(or('a', 'b'), { conflictBudget }));
      badCalls.push(() => handle.solveAsync(undefined, { conflictBudget }));
    }
    for (const yieldQuantum of [0, -1, 0.5, Number.NaN, Number.POSITIVE_INFINITY]) {
      badCalls.push(() => getSolutionAsync(or('a', 'b'), { yieldQuantum }));
      badCalls.push(() => getAllSolutionsAsync(or('a', 'b'), { yieldQuantum }));
      badCalls.push(() => handle.solveAsync(undefined, { yieldQuantum }));
    }
    badCalls.push(() => getSolutionAsync(or('a', 'b'), { assumptions: { missing: 1 } }));
    badCalls.push(() => getAllSolutionsAsync(or('a', 'b'), { assumptions: { missing: 1 } }));
    badCalls.push(() => handle.solveAsync({ missing: 1 }));
    for (const call of badCalls) {
      const pending = call();
      assert.ok(pending instanceof Promise, 'async entry points always return a Promise');
      await assert.rejects(pending, /conflictBudget|yieldQuantum|unknown assumption/);
    }
  });

  it('zeroes stats before rejecting invalid async options', async () => {
    const stats = createSolverStats();
    stats.decisions = 999;
    await assert.rejects(getSolutionAsync(or('a', 'b'), { conflictBudget: -1, stats }));
    assert.strictEqual(stats.decisions, 0, 'stats zeroing precedes validation');
    stats.decisions = 999;
    await assert.rejects(getSolutionAsync(or('a', 'b'), { yieldQuantum: 0, stats }));
    assert.strictEqual(stats.decisions, 0);
  });

  it('accepts yieldQuantum below the floor by clamping, and matches sync results', async () => {
    const expr = and('a', or('a', 'b'));
    for (const yieldQuantum of [1, 63, 64]) {
      const result = await getSolutionAsync(expr, { yieldQuantum });
      assert.strictEqual(result.status, 'sat');
      assert.strictEqual(result.model.a, Value.TRUE);
      assert.strictEqual(expressionValue(expr, result.model), Value.TRUE);
    }
  });
});

describe('pre-aborted signals consult only established verdicts', () => {
  it('validates first: invalid inputs reject even with a pre-aborted signal', async () => {
    const controller = new AbortController();
    controller.abort();
    await assert.rejects(
      getSolutionAsync(or('a', 'b'), { signal: controller.signal, conflictBudget: -1 }),
      /conflictBudget/,
    );
    await assert.rejects(
      getSolutionAsync(or('a', 'b'), { signal: controller.signal, assumptions: { nope: 1 } }),
      /unknown assumption/,
    );
  });

  it('returns compiled or construction-proven verdicts without propagation or preprocessing', async () => {
    const controller = new AbortController();
    controller.abort();
    const { signal } = controller;
    // The scheduler must never run: no slice ever starts.
    let schedulerCalls = 0;
    setYieldScheduler(() => {
      schedulerCalls += 1;
      return Promise.resolve();
    });
    try {
      const stats = createSolverStats();
      assert.deepStrictEqual(await getSolutionAsync(or(), { signal, stats }), {
        status: 'unsat',
        core: {},
      });
      assert.deepStrictEqual(stats, createSolverStats(), 'compiled UNSAT does no work at all');
      assert.deepStrictEqual(await getSolutionAsync(and('a', not('a')), { signal, stats }), {
        status: 'unsat',
        core: {},
      });
      // Constructor unit installation is synchronous construction work, so
      // the a=TRUE unit enqueue counts — but the contradiction detected at
      // construction is never propagated or counted: no search slice ran.
      assert.strictEqual(stats.decisions, 0);
      assert.strictEqual(stats.conflicts, 0, 'the startup conflict was never propagated');
      assert.strictEqual(stats.propagations, 1, 'only the constructor unit');
      assert.deepStrictEqual(await getAllSolutionsAsync(and('a', not('a')), { signal }), {
        status: 'complete',
        models: [],
      });
      assert.deepStrictEqual(await getSolutionAsync(and(), { signal }), {
        status: 'unknown',
        reason: 'aborted',
      });
      assert.deepStrictEqual(await getAllSolutionsAsync(or('a', 'b'), { signal }), {
        status: 'unknown',
        models: [],
        reason: 'aborted',
      });
      assert.strictEqual(schedulerCalls, 0, 'a pre-aborted call never yields');
    } finally {
      setYieldScheduler(undefined);
    }
  });

  it('consults a previously established UNSAT verdict on an incremental handle', async () => {
    const handle = createSolver(and('a', not('a')));
    assert.strictEqual((await handle.solveAsync()).status, 'unsat');
    const controller = new AbortController();
    controller.abort();
    assert.deepStrictEqual(await handle.solveAsync(undefined, { signal: controller.signal }), {
      status: 'unsat',
      core: {},
    });
  });
});

describe('abort delivery at slice checkpoints', () => {
  it('aborts during satisfied-watch/relocation-only root scans, then solve() stays sound', async () => {
    const handle = createSolver(wideScan(96));
    const controller = new AbortController();
    setYieldScheduler(abortingScheduler(controller, 2));
    let result: SolveResult;
    const stats = createSolverStats();
    try {
      result = await handle.solveAsync(undefined, {
        signal: controller.signal,
        yieldQuantum: 64,
        stats,
      });
    } finally {
      setYieldScheduler(undefined);
    }
    assert.deepStrictEqual(result, { status: 'unknown', reason: 'aborted' });
    // The abort landed inside the initial root-propagation scan: zero
    // decisions, zero propagations (constructor units are construction, not
    // call work), zero conflicts — the pause came from pure watch scanning.
    assert.deepStrictEqual(stats, createSolverStats(), 'aborted mid-scan, before any decision');
    // Abort and scheduler-error abandonment mid-root-scan must leave the
    // handle coherent: the unbudgeted sync solve completes and agrees with a
    // fresh handle.
    const recovered = handle.solve();
    assert.strictEqual(recovered.status, 'sat');
    const fresh = createSolver(wideScan(96)).solve();
    assert.strictEqual(fresh.status, 'sat');
    assert.deepStrictEqual(recovered, fresh);
  });

  it('aborts during assumption prefix replay with zero decisions recorded', async () => {
    const { expr, assumptions } = freeVariables(200);
    const handle = createSolver(expr);
    const controller = new AbortController();
    setYieldScheduler(abortingScheduler(controller, 2));
    const stats = createSolverStats();
    let result: SolveResult;
    try {
      result = await handle.solveAsync(assumptions, {
        signal: controller.signal,
        yieldQuantum: 64,
        stats,
      });
    } finally {
      setYieldScheduler(undefined);
    }
    assert.deepStrictEqual(result, { status: 'unknown', reason: 'aborted' });
    assert.strictEqual(stats.decisions, 0, 'aborted mid-prefix, before any decision');
    assert.strictEqual(stats.conflicts, 0);
    // The prefix was cancelled in cleanup; the handle is immediately reusable.
    assert.strictEqual(handle.solve(assumptions).status, 'sat');
  });

  it('aborts across many short enumeration searches, returning a genuine valid prefix', async () => {
    const expr = pairs(4);
    const complete = expectCompleteModels(getAllSolutions(expr));
    assert.strictEqual(complete.length, 81);
    const controller = new AbortController();
    setYieldScheduler(abortingScheduler(controller, 3));
    let result: EnumerateResult;
    try {
      result = await getAllSolutionsAsync(expr, {
        signal: controller.signal,
        yieldQuantum: 64,
      });
    } finally {
      setYieldScheduler(undefined);
    }
    assert.strictEqual(result.status, 'unknown');
    if (result.status !== 'unknown') throw new Error('unreachable');
    assert.strictEqual(result.reason, 'aborted');
    assert.ok(result.models.length > 0, 'the abort lands mid-enumeration, not at entry');
    assert.ok(result.models.length < complete.length, 'strictly partial');
    const seen = new Set<string>();
    result.models.forEach((model, index) => {
      assert.strictEqual(expressionValue(expr, model), Value.TRUE);
      assert.deepStrictEqual(model, complete[index], 'deterministic prefix of the sync order');
      seen.add(JSON.stringify(model));
    });
    assert.strictEqual(seen.size, result.models.length);
  });

  it('abort outranks a simultaneously-exhausted budget, and a verdict outranks abort', async () => {
    // Budget 0 plus an abort at the first yield: the budget-zero startup
    // allowance is mid-scan when the abort lands — 'aborted' wins over the
    // pending budget outcome.
    const handle = createSolver(wideScan(96));
    const controller = new AbortController();
    setYieldScheduler(abortingScheduler(controller, 1));
    let result: SolveResult;
    try {
      result = await handle.solveAsync(undefined, {
        conflictBudget: 0,
        signal: controller.signal,
        yieldQuantum: 64,
      });
    } finally {
      setYieldScheduler(undefined);
    }
    assert.deepStrictEqual(result, { status: 'unknown', reason: 'aborted' });
    assert.strictEqual(handle.solve().status, 'sat', 'handle remains sound');

    // A verdict established before the abort check wins: compiled UNSAT with
    // a pre-aborted signal returns 'unsat', not 'aborted'.
    const pre = new AbortController();
    pre.abort();
    assert.strictEqual(
      (await getSolutionAsync(and('a', not('a')), { signal: pre.signal })).status,
      'unsat',
    );
  });

  it('enumeration: abort outranks a budget outcome when the abort lands in the final slice', async () => {
    // The hook aborts mid-slice (the core never checks signals); the same
    // synchronous generator step then exhausts the one-conflict budget. The
    // outcome reports 'aborted', never 'conflictBudget'.
    const controller = new AbortController();
    const result = await getAllSolutionsAsync(pairs(2), {
      conflictBudget: 1,
      yieldQuantum: 64,
      signal: controller.signal,
      variablePriority: () => {
        controller.abort();
        return null;
      },
    });
    assert.strictEqual(result.status, 'unknown');
    if (result.status !== 'unknown') throw new Error('unreachable');
    assert.strictEqual(result.reason, 'aborted');
    // The first model was already found before exhaustion: partial evidence
    // survives the precedence resolution, identical to the sync first model.
    const syncFirst = expectCompleteModels(getAllSolutions(pairs(2)))[0];
    assert.deepStrictEqual(result.models, [syncFirst]);
  });
});

describe('async ≡ sync for identical non-aborted histories', () => {
  const battery: BooleanExpr[] = [
    and(),
    or(),
    and('a', not('a')),
    or('a', 'b'),
    boundaryWitness(),
    and(or('a', 'b'), or(not('a'), 'c'), or('a', not('c'), 'd')),
    pairs(3),
    // Cardinality: an asserted Sinz counter, a nested (totalized) threshold
    // in both polarities, and an UNSAT band.
    atMost(1, 'a', 'b', 'c', 'd', 'e', 'f', 'g'),
    or(not(atLeast(2, 'a', 'b', 'c')), 'd'),
    and(exactly(2, 'a', 'b', 'c'), or(not(atMost(1, 'd', 'e')), 'f')),
    and(atLeast(2, 'a', 'b'), atMost(1, 'a', 'b')),
  ];

  it('single-shot: identical verdict, model, and counters at every quantum', async () => {
    for (const expr of battery) {
      const syncStats = createSolverStats();
      const syncResult = getSolution(expr, { stats: syncStats });
      for (const yieldQuantum of [64, 4096, undefined]) {
        const asyncStats = createSolverStats();
        const asyncResult = await getSolutionAsync(expr, { yieldQuantum, stats: asyncStats });
        assert.deepStrictEqual(asyncResult, syncResult);
        assert.deepStrictEqual(asyncStats, syncStats, 'scheduling never changes counters');
        assert.notStrictEqual(asyncResult.status, 'unknown', 'no budget, no abort: never unknown');
      }
    }
  });

  it('enumeration: identical status, ordered models, and counters at every quantum', async () => {
    for (const expr of battery) {
      const syncStats = createSolverStats();
      const syncResult = getAllSolutions(expr, { stats: syncStats });
      for (const yieldQuantum of [64, 4096, undefined]) {
        const asyncStats = createSolverStats();
        const asyncResult = await getAllSolutionsAsync(expr, { yieldQuantum, stats: asyncStats });
        assert.deepStrictEqual(asyncResult, syncResult);
        assert.deepStrictEqual(asyncStats, syncStats);
      }
    }
  });

  it('incremental: identical per-call verdicts and counters across a call sequence', async () => {
    const expr = and(or('a', 'b'), or(not('a'), 'c'), or(not('b'), not('c')));
    const calls: Array<VariableAssignments | undefined> = [
      undefined,
      { a: Value.TRUE },
      { a: Value.TRUE, c: Value.TRUE },
      { a: Value.FALSE },
      { b: Value.FALSE, c: Value.FALSE },
      undefined,
    ];
    const syncHandle = createSolver(expr);
    const asyncHandle = createSolver(expr);
    for (const assumptions of calls) {
      const syncStats = createSolverStats();
      const syncResult = syncHandle.solve(assumptions, { stats: syncStats });
      const asyncStats = createSolverStats();
      const asyncResult = await asyncHandle.solveAsync(assumptions, {
        yieldQuantum: 64,
        stats: asyncStats,
      });
      assert.deepStrictEqual(asyncResult, syncResult);
      assert.deepStrictEqual(asyncStats, syncStats);
    }
  });

  it('incremental with cardinality adds: identical verdicts and counters across the history', async () => {
    const syncHandle = createSolver(or('a', 'b'));
    const asyncHandle = createSolver(or('a', 'b'));
    const batches: BooleanExpr[] = [
      atMost(1, 'a', 'b', 'c'),
      atLeast(2, 'a', 'b', 'c', 'd'),
      or(not(exactly(1, 'a', 'd')), 'e'),
    ];
    for (const batch of batches) {
      syncHandle.add(batch);
      asyncHandle.add(batch);
    }
    for (const assumptions of [
      undefined,
      { a: Value.TRUE, b: Value.TRUE },
      { c: Value.FALSE, d: Value.TRUE },
      { e: Value.FALSE, a: Value.TRUE, d: Value.FALSE },
    ] as Array<VariableAssignments | undefined>) {
      const syncStats = createSolverStats();
      const syncResult = syncHandle.solve(assumptions, { stats: syncStats });
      const asyncStats = createSolverStats();
      const asyncResult = await asyncHandle.solveAsync(assumptions, {
        yieldQuantum: 64,
        stats: asyncStats,
      });
      assert.deepStrictEqual(asyncResult, syncResult);
      assert.deepStrictEqual(asyncStats, syncStats);
    }
  });

  it('async budget exhaustion matches sync exactly, including counters', async () => {
    const expr = boundaryWitness();
    const syncStats = createSolverStats();
    const syncResult = getSolution(expr, { conflictBudget: 1, stats: syncStats });
    const asyncStats = createSolverStats();
    const asyncResult = await getSolutionAsync(expr, {
      conflictBudget: 1,
      yieldQuantum: 64,
      stats: asyncStats,
    });
    assert.deepStrictEqual(asyncResult, syncResult);
    assert.deepStrictEqual(asyncStats, syncStats);
    assert.deepStrictEqual(asyncResult, { status: 'unknown', reason: 'conflictBudget' });
  });
});

describe('failure atomicity and reentrancy', () => {
  it('propagates scheduler rejection and leaves the handle reusable', async () => {
    const failure = new Error('scheduler failure');
    let calls = 0;
    setYieldScheduler(() => {
      calls += 1;
      return calls === 2 ? Promise.reject(failure) : Promise.resolve();
    });
    try {
      const handle = createSolver(wideScan(96));
      await assert.rejects(
        handle.solveAsync(undefined, { yieldQuantum: 64 }),
        (error: unknown) => error === failure,
      );
      // Scheduler-error abandonment mid-root-scan followed by solve is sound.
      assert.strictEqual(handle.solve().status, 'sat');
      // A fresh single-shot call rejects identically (re-arm the failing yield).
      calls = 0;
      await assert.rejects(
        getSolutionAsync(wideScan(32), { yieldQuantum: 64 }),
        (error: unknown) => error === failure,
      );
    } finally {
      setYieldScheduler(undefined);
    }
  });

  it('rejects on hook failure mid-slice and leaves the handle reusable', async () => {
    const failure = new Error('consumer priority failure');
    let fail = true;
    const handle = createSolver(and(freeVariables(96).expr, or('x', 'y')), {
      variablePriority: () => {
        if (fail) throw failure;
        return null;
      },
    });
    await assert.rejects(
      handle.solveAsync(undefined, { yieldQuantum: 64 }),
      (error: unknown) => error === failure,
    );
    fail = false;
    assert.strictEqual(handle.solve().status, 'sat');
    assert.strictEqual((await handle.solveAsync()).status, 'sat');
  });

  it('hooks cannot reenter a busy async handle, and the outer call completes', async () => {
    let reentryChecked = false;
    const handle = createSolver(and(freeVariables(96).expr, or('x', 'y')), {
      variablePriority: () => {
        assert.throws(() => handle.solve(), /reentered/);
        reentryChecked = true;
        return null;
      },
    });
    const result = await handle.solveAsync(undefined, { yieldQuantum: 64 });
    assert.strictEqual(result.status, 'sat');
    assert.ok(reentryChecked, 'the hook really ran during the async call');
  });

  it('a sync solve on a busy handle throws; a second async call rejects without mutating state', async () => {
    let release: (() => void) | undefined;
    let parked = false;
    setYieldScheduler(() => {
      if (!parked) {
        parked = true;
        return new Promise<void>((resolve) => {
          release = resolve;
        });
      }
      return Promise.resolve();
    });
    try {
      const handle = createSolver(wideScan(96));
      const outerStats = createSolverStats();
      // The async body runs synchronously to its first yield, so the call is
      // parked mid-root-scan before solveAsync returns.
      const pending = handle.solveAsync(undefined, { yieldQuantum: 64, stats: outerStats });
      assert.ok(parked, 'the outer call reached its first yield');
      // Sync solve on the busy handle throws...
      assert.throws(() => handle.solve(), /reentered/);
      // ...and a second async call rejects, without zeroing its own stats or
      // touching the outer call's in-flight state.
      const innerStats = createSolverStats();
      innerStats.decisions = 999;
      await assert.rejects(handle.solveAsync(undefined, { stats: innerStats }), /reentered/);
      assert.strictEqual(innerStats.decisions, 999, 'the rejected call never zeroed its stats');
      assert.ok(release !== undefined);
      release();
      const outer = await pending;
      assert.strictEqual(outer.status, 'sat');
      assert.ok(outerStats.propagations > 0, 'outer stats reflect only the outer call');
      // The busy guard was released: the handle is reusable.
      assert.strictEqual(handle.solve().status, 'sat');
    } finally {
      setYieldScheduler(undefined);
    }
  });
});

describe('real scheduler fallback selection and lifecycle', () => {
  // Node exposes no WHATWG `scheduler` global, so the platform fallback in
  // these tests genuinely selects MessageChannel, then setTimeout.
  interface GlobalSchedulerSlot {
    scheduler?: { yield?: (() => Promise<void>) | undefined } | undefined;
  }

  it('selects scheduler.yield when the platform provides it', async () => {
    const holder = globalThis as GlobalSchedulerSlot;
    const saved = holder.scheduler;
    let yields = 0;
    holder.scheduler = {
      yield: () => {
        yields += 1;
        return Promise.resolve();
      },
    };
    try {
      const result = await getSolutionAsync(wideScan(96), { yieldQuantum: 64 });
      assert.strictEqual(result.status, 'sat');
      assert.ok(yields > 0, 'the WHATWG scheduler global was selected');
    } finally {
      holder.scheduler = saved;
    }
  });

  it('uses one MessageChannel per yield and closes both of its ports', async () => {
    const RealMessageChannel = globalThis.MessageChannel;
    const created: Array<{ port1Closed: boolean; port2Closed: boolean }> = [];
    class TrackingChannel {
      readonly port1: { onmessage: (() => void) | null; close(): void };
      readonly port2: {
        onmessage: (() => void) | null;
        close(): void;
        postMessage(m: unknown): void;
      };
      constructor() {
        const inner = new RealMessageChannel();
        const record = { port1Closed: false, port2Closed: false };
        created.push(record);
        const wrap = (
          // Structural, not the DOM/Node MessagePort type: the strict
          // typecheck pins `lib` to es2022, where no global MessagePort
          // interface exists, and either flavor satisfies this shape.
          port: { close(): void; postMessage(message: unknown): void },
          markClosed: () => void,
        ): { onmessage: (() => void) | null; close(): void; postMessage(m: unknown): void } => {
          let handler: (() => void) | null = null;
          const typed = port as unknown as { onmessage: (() => void) | null };
          return {
            get onmessage() {
              return handler;
            },
            set onmessage(next: (() => void) | null) {
              handler = next;
              typed.onmessage = next === null ? null : () => next();
            },
            close: () => {
              markClosed();
              port.close();
            },
            postMessage: (message: unknown) => port.postMessage(message),
          };
        };
        this.port1 = wrap(inner.port1, () => {
          record.port1Closed = true;
        });
        this.port2 = wrap(inner.port2, () => {
          record.port2Closed = true;
        });
      }
    }
    const mutable = globalThis as unknown as { MessageChannel: unknown };
    mutable.MessageChannel = TrackingChannel;
    try {
      const result = await getSolutionAsync(wideScan(96), { yieldQuantum: 64 });
      assert.strictEqual(result.status, 'sat');
    } finally {
      mutable.MessageChannel = RealMessageChannel;
    }
    assert.ok(created.length >= 2, 'multiple slices really yielded through channels');
    for (const channel of created) {
      assert.ok(
        channel.port1Closed && channel.port2Closed,
        'every owned port closed when its message landed',
      );
    }
  });

  it('falls back to setTimeout(0) when no scheduler or MessageChannel exists', async () => {
    const holder = globalThis as unknown as { MessageChannel?: unknown; setTimeout: unknown };
    const realChannel = globalThis.MessageChannel;
    const realSetTimeout = globalThis.setTimeout;
    let timeouts = 0;
    holder.setTimeout = ((callback: () => void, ms?: number) => {
      timeouts += 1;
      return realSetTimeout(callback, ms);
    }) as typeof setTimeout;
    Reflect.deleteProperty(globalThis, 'MessageChannel');
    try {
      const result = await getSolutionAsync(wideScan(96), { yieldQuantum: 64 });
      assert.strictEqual(result.status, 'sat');
      assert.ok(timeouts > 0, 'the zero-millisecond timer fallback really engaged');
    } finally {
      holder.MessageChannel = realChannel;
      holder.setTimeout = realSetTimeout;
    }
  });

  it('prefers the injected scheduler seam over every platform global', async () => {
    const holder = globalThis as GlobalSchedulerSlot;
    const saved = holder.scheduler;
    let globalYields = 0;
    let injectedYields = 0;
    holder.scheduler = {
      yield: () => {
        globalYields += 1;
        return Promise.resolve();
      },
    };
    setYieldScheduler(() => {
      injectedYields += 1;
      return Promise.resolve();
    });
    try {
      const result = await getSolutionAsync(wideScan(96), { yieldQuantum: 64 });
      assert.strictEqual(result.status, 'sat');
      assert.ok(injectedYields > 0, 'the injected seam was used');
      assert.strictEqual(globalYields, 0, 'platform globals never engaged');
    } finally {
      setYieldScheduler(undefined);
      holder.scheduler = saved;
    }
  });

  it('a settled async solve does not keep a Node runtime alive', () => {
    // Liveness, not a wall-clock assertion: the child must exit NATURALLY
    // after its settled solves (leaked MessageChannel ports or listeners
    // would pin the event loop); the backstop timeout only bounds a genuine
    // deadlock regression and never gates on speed.
    const child = join(dirname(fileURLToPath(import.meta.url)), 'async-exit-child.mts');
    const result = spawnSync(process.execPath, ['--import', 'tsx', child], {
      encoding: 'utf8',
      timeout: 120_000,
    });
    assert.strictEqual(result.error, undefined, `child spawn failed: ${result.error}`);
    assert.strictEqual(result.status, 0, `child failed:\n${result.stderr}`);
    assert.ok(result.stdout.includes('ASYNC_CHILD_SETTLED'), 'child settled and exited');
  });
});
