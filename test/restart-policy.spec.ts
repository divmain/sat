// Direct drivers for the extracted restart policy units: scripted LBD and
// trail-length streams pin the exact restart/block decisions of the pinned
// deterministic EMA default and the retained Luby schedule, without any
// solver coupling. Expected values are literal streams and exact doubles
// (shortest-round-trip literals), never derived from the policies themselves.
import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile } from '../src/compile.js';
import { cnfToExpr, phpCnf } from './helpers.js';
import { EmaRestartPolicy, LubyRestartPolicy, Solver } from '../src/solver.js';
import type { RestartPolicy } from '../src/solver.js';
import { internals } from './incremental-helpers.js';

const kinds = (verdicts: Array<{ kind: string }>): string[] => verdicts.map((v) => v.kind);

describe('EmaRestartPolicy initialization and the exact recurrence', () => {
  it('initializes both EMAs to the first learned LBD and never restarts on a constant stream', () => {
    const policy = new EmaRestartPolicy();
    assert.strictEqual(policy.emaFast, null);
    assert.strictEqual(policy.emaSlow, null);
    const verdicts: string[] = [];
    for (let conflict = 1; conflict <= 100; conflict += 1) {
      verdicts.push(policy.onConflict({ lbd: 7, trailLength: 3, atRoot: false }).kind);
      // First-sample initialization, then the constant stream leaves both
      // histories exactly at the constant (zero delta): the 1.25 ratio can
      // never trigger from equal averages, even past the 32-conflict interval.
      assert.strictEqual(policy.emaFast, 7);
      assert.strictEqual(policy.emaSlow, 7);
    }
    assert.deepStrictEqual(verdicts, Array<string>(100).fill('none'));
    assert.strictEqual(policy.conflictsSinceRestart, 100, 'the interval alone consumes no epoch');
    assert.strictEqual(policy.nextEligibleAt, 32);
    assert.strictEqual(policy.previousRestartTrail, null);
  });

  it('tracks the pinned fast/slow recurrence exactly on a rising stream', () => {
    const policy = new EmaRestartPolicy();
    policy.onConflict({ lbd: 2, trailLength: 1, atRoot: false });
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], [2, 2]);
    policy.onConflict({ lbd: 100, trailLength: 1, atRoot: false });
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], [26.5, 3.96]);
    policy.onConflict({ lbd: 100, trailLength: 1, atRoot: false });
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], [44.875, 5.8808]);
    policy.onConflict({ lbd: 100, trailLength: 1, atRoot: false });
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], [58.65625, 7.763184]);
  });
});

describe('EmaRestartPolicy eligibility, blocking, and epochs', () => {
  it('gates the first check at exactly 32 conflicts and re-arms after each consumed epoch', () => {
    // Init at LBD 2, then a permanent rise to 100: the fast average crosses
    // 1.25x the slow one from the second conflict on, but the interval defers
    // the first restart to exactly conflict 32. The averages converge on the
    // constant stream, so the ratio is dead by the third check.
    const policy = new EmaRestartPolicy();
    const verdicts: string[] = [];
    for (let conflict = 1; conflict <= 100; conflict += 1) {
      const lbd = conflict === 1 ? 2 : 100;
      verdicts.push(policy.onConflict({ lbd, trailLength: 10, atRoot: false }).kind);
    }
    const expected = Array<string>(100).fill('none');
    expected[31] = 'restart';
    expected[63] = 'restart';
    assert.deepStrictEqual(verdicts, expected);
    assert.strictEqual(policy.previousRestartTrail, 10, 'each actual restart re-snapshots');
    assert.strictEqual(policy.conflictsSinceRestart, 36);
    assert.strictEqual(policy.nextEligibleAt, 32);
  });

  it('postpones a triggered restart by exactly one interval when the trail outgrows its snapshot', () => {
    // Constant low LBD with a single high spike at each check point. Distinct
    // trail lengths at the trigger conflicts pin the snapshot timing: the
    // sample is taken at the restart, before cancellation, never later.
    const policy = new EmaRestartPolicy();
    const trailAt = (conflict: number): number => {
      if (conflict === 96) return 12;
      if (conflict === 128) return 11;
      if (conflict === 160) return 13;
      if (conflict === 192) return 12;
      return 10;
    };
    const verdicts: string[] = [];
    const snapshots: Array<number | null> = [];
    for (let conflict = 1; conflict <= 192; conflict += 1) {
      const spike = conflict >= 64 && (conflict - 64) % 32 === 0;
      const verdict = policy.onConflict({
        lbd: spike ? 100 : 2,
        trailLength: trailAt(conflict),
        atRoot: false,
      });
      verdicts.push(verdict.kind);
      if (verdict.kind !== 'none') {
        snapshots.push(policy.previousRestartTrail);
        if (verdict.kind === 'restart') {
          assert.strictEqual(verdict.actual, true);
        }
      }
    }
    const expected = Array<string>(192).fill('none');
    expected[63] = 'restart'; // first trigger is unblocked: no snapshot exists
    expected[95] = 'blocked'; // trail 12 > 1.1 x snapshot 10; next check +32
    expected[127] = 'restart'; // trail 11 is NOT beyond 1.1 x 10: boundary fires
    expected[159] = 'blocked'; // trail 13 > 1.1 x snapshot 11
    expected[191] = 'restart'; // trail 12 is within 1.1 x 11
    assert.deepStrictEqual(verdicts, expected);
    assert.deepStrictEqual(
      snapshots,
      [10, 10, 11, 11, 12],
      'blocked attempts never replace the previous actual snapshot',
    );
    // Per-search state resets; the lifetime EMA histories do not.
    const ema: [number | null, number | null] = [policy.emaFast, policy.emaSlow];
    policy.resetSearch();
    assert.strictEqual(policy.conflictsSinceRestart, 0);
    assert.strictEqual(policy.nextEligibleAt, 32);
    assert.strictEqual(policy.previousRestartTrail, null, 'blocking history is per search');
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], ema);
  });

  it('consumes root-level epochs without an actual restart or a blocking snapshot', () => {
    const policy = new EmaRestartPolicy();
    for (let conflict = 1; conflict <= 31; conflict += 1) {
      assert.strictEqual(policy.onConflict({ lbd: 2, trailLength: 5, atRoot: false }).kind, 'none');
    }
    const noop = policy.onConflict({ lbd: 100, trailLength: 50, atRoot: true });
    assert.deepStrictEqual(noop, { kind: 'restart', actual: false });
    assert.strictEqual(policy.conflictsSinceRestart, 0, 'a root no-op consumes the epoch');
    assert.strictEqual(policy.nextEligibleAt, 32);
    assert.strictEqual(policy.previousRestartTrail, null, 'a root no-op never snapshots');
    // The first ACTUAL restart of the search stays unblocked, however long
    // its trail: the no-op left no snapshot to compare against.
    for (let conflict = 33; conflict <= 63; conflict += 1) {
      assert.strictEqual(policy.onConflict({ lbd: 2, trailLength: 5, atRoot: false }).kind, 'none');
    }
    const first = policy.onConflict({ lbd: 100, trailLength: 1000, atRoot: false });
    assert.deepStrictEqual(first, { kind: 'restart', actual: true });
    assert.strictEqual(policy.previousRestartTrail, 1000);
    // A later root no-op does not overwrite the existing snapshot either.
    for (let conflict = 65; conflict <= 95; conflict += 1) {
      assert.strictEqual(policy.onConflict({ lbd: 2, trailLength: 5, atRoot: false }).kind, 'none');
    }
    const secondNoop = policy.onConflict({ lbd: 100, trailLength: 1, atRoot: true });
    assert.deepStrictEqual(secondNoop, { kind: 'restart', actual: false });
    assert.strictEqual(policy.previousRestartTrail, 1000);
  });

  it('keeps the EMA histories across searches while the epoch state resets', () => {
    const policy = new EmaRestartPolicy();
    for (let conflict = 1; conflict <= 10; conflict += 1) {
      policy.onConflict({ lbd: 8, trailLength: 4, atRoot: false });
    }
    assert.deepStrictEqual([policy.emaFast, policy.emaSlow], [8, 8]);
    policy.resetSearch();
    assert.strictEqual(policy.conflictsSinceRestart, 0);
    assert.strictEqual(policy.nextEligibleAt, 32);
    policy.onConflict({ lbd: 2, trailLength: 4, atRoot: false });
    // A re-initializing policy would read exactly 2 here; the lifetime
    // histories continue from 8 instead (exact: 8 + 0.25 * (2 - 8)).
    assert.strictEqual(policy.emaFast, 6.5);
    assert.strictEqual(policy.emaSlow, 7.88);
  });
});

describe('LubyRestartPolicy retained schedule', () => {
  it('replays the exact base-1 epoch boundaries, ignoring LBD and trail inputs', () => {
    const policy = new LubyRestartPolicy(1);
    const verdicts = [];
    for (let conflict = 1; conflict <= 20; conflict += 1) {
      // Deliberately noisy unused inputs: the schedule is conflict-count only.
      verdicts.push(
        policy.onConflict({ lbd: (conflict * 7) % 13, trailLength: conflict, atRoot: false }),
      );
    }
    // Cumulative sums of the literal prefix 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8.
    assert.deepStrictEqual(
      kinds(verdicts)
        .map((kind, index) => (kind === 'restart' ? index + 1 : 0))
        .filter(Boolean),
      [1, 2, 4, 5, 6, 8, 12, 13, 14, 16, 17, 18, 20],
    );
    assert.ok(verdicts.every((verdict) => verdict.kind !== 'restart' || verdict.actual));
  });

  it('scales epochs by the base in exact block arithmetic', () => {
    const policy = new LubyRestartPolicy(3);
    const verdicts = [];
    for (let conflict = 1; conflict <= 36; conflict += 1) {
      verdicts.push(policy.onConflict({ lbd: 2, trailLength: 1, atRoot: false }));
    }
    assert.deepStrictEqual(
      kinds(verdicts)
        .map((kind, index) => (kind === 'restart' ? index + 1 : 0))
        .filter(Boolean),
      [3, 6, 12, 15, 18, 24, 36],
    );
  });

  it('consumes root-level epochs as no-ops and restarts each search schedule fresh', () => {
    const policy = new LubyRestartPolicy(1);
    assert.deepStrictEqual(policy.onConflict({ lbd: 9, trailLength: 40, atRoot: true }), {
      kind: 'restart',
      actual: false,
    });
    assert.strictEqual(policy.restartIndex, 2, 'the epoch was consumed');
    policy.onConflict({ lbd: 9, trailLength: 40, atRoot: true });
    assert.strictEqual(policy.restartIndex, 3);
    policy.resetSearch();
    assert.strictEqual(policy.restartIndex, 1);
    assert.strictEqual(policy.blocksUntilRestart, 1);
    assert.strictEqual(policy.conflictsInBlock, 0);
    assert.deepStrictEqual(policy.onConflict({ lbd: 1, trailLength: 1, atRoot: false }), {
      kind: 'restart',
      actual: true,
    });
  });

  it('never restarts inside a huge base', () => {
    const policy = new LubyRestartPolicy(2 ** 32);
    for (let conflict = 1; conflict <= 100; conflict += 1) {
      assert.strictEqual(
        policy.onConflict({ lbd: 50, trailLength: 50, atRoot: false }).kind,
        'none',
      );
    }
    assert.strictEqual(policy.conflictsInBlock, 100);
  });
});

describe('solver wiring of the extracted policies', () => {
  // The same UNSAT instance solved under each selectable policy: the pinned
  // restart counts genuinely differ (EMA 3, Luby 6), proving the selector
  // engages distinct schedules end to end. Re-pinning these witnesses is a
  // benchmark-disclosed decision; the EMA 4→3 shift came from the
  // binary-first propagation trajectory (task-9c11, disclosed in
  // test/v3-benchmark-review.md).
  const php76 = () => compile(cnfToExpr(phpCnf(7, 6)));

  it('drives genuine restarts through the default EMA policy on a real search', () => {
    const solver = new Solver(php76(), { enablePle: true, conflictBudget: 7_230 });
    assert.strictEqual(solver.solve(), false, 'seven pigeons cannot occupy six holes');
    const policy: RestartPolicy = internals(solver).restartPolicy;
    assert.strictEqual(policy.kind, 'ema');
    assert.ok(policy.emaFast !== null, 'learned LBDs initialized the lifetime histories');
    assert.ok(solver.stats.conflicts > 32, 'the eligibility interval is genuinely reached');
    assert.strictEqual(solver.stats.restarts, 3, 'pinned EMA trajectory on PHP(7,6)');
  });

  it('drives a different, also-pinned schedule when Luby is explicitly selected', () => {
    const solver = new Solver(php76(), {
      enablePle: true,
      restartPolicy: 'luby',
      conflictBudget: 7_230,
    });
    assert.strictEqual(solver.solve(), false);
    const policy = internals(solver).restartPolicy;
    assert.strictEqual(policy.kind, 'luby');
    assert.ok(policy.restartIndex > 1, 'the Luby schedule advanced');
    assert.strictEqual(solver.stats.restarts, 6, 'pinned Luby-base-100 trajectory on PHP(7,6)');
  });
});
