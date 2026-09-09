// Mutable solver state, MiniSat-style two-watched-literal unit propagation,
// scoped pure-literal elimination, and iterative first-UIP CDCL search with
// non-chronological backjumping, provenance-aware root-literal tracking,
// recursive learned-clause minimization (ccmin_mode=2, iterative over an
// explicit stack), VSIDS branching, phase saving, pinned deterministic
// restarts (the Glucose-style EMA default with blocking, or the internally
// selectable Luby schedule), and periodic learned-clause reduction under the
// pinned two-tier (glue/reducible) retention policy with decayed clause
// activity and dynamic LBD tightening.
// See Design § Solver Core End-State.

import { compileIncremental, isNeg, litValue, neg, normalizeClauseLits, varOf } from './compile.js';
import type { Clause, CompiledCnf } from './compile.js';
import { Value } from './expr.js';
import type { BooleanExpr, Variable, VariableAssignments } from './expr.js';

export interface SolverStats {
  decisions: number;
  propagations: number;
  conflicts: number;
  restarts: number;
  /** Learned-clause admissions within the measurement scope; deletions never rewind it. */
  learnedClauses: number;
  /** Live learned clauses currently in the database, excluding permanent blockers. */
  learnedClausesCurrent: number;
  /** Post-minimization literals produced by conflict analysis in scope, before duplicate suppression. */
  learnedLiterals: number;
  /** Literals removed from learned clauses by recursive minimization in scope. */
  minimizedLiterals: number;
}

// Rich public verdicts (Design § Target Public API). `SolveResult` is
// produced by every single-shot and incremental solve; `EnumerateResult` by
// model enumeration. The 'unknown' status is produced only by conflict-budget
// exhaustion or an abort signal — both enforced exactly where they are
// exposed (no option before it is enforced). An 'unsat' core
// is a subset of the call's assumptions that suffices for UNSAT — sound, not
// necessarily minimal; `{}` only when no assumptions were supplied or UNSAT
// was proven independent of them. These types live in this internal module
// (like SolverStats) because solveAssuming produces them; index.ts
// re-exports them as public types.
export type SolveResult =
  | { status: 'sat'; model: VariableAssignments }
  | { status: 'unsat'; core: VariableAssignments }
  | { status: 'unknown'; reason: 'conflictBudget' | 'aborted' };

export type EnumerateResult =
  | { status: 'complete'; models: VariableAssignments[] } // [] = UNSAT / no models
  | { status: 'unknown'; models: VariableAssignments[]; reason: 'conflictBudget' | 'aborted' };

// Stats out-params may be sparse: the callee zeroes missing fields and then
// populates ALL fields, so a partial input object is always left complete.
export type SolverStatsInput = Partial<SolverStats>;

// A complete, all-zero SolverStats. Born with all then-current fields; any
// future counter must be added here (and to the zeroing path) in the same
// task that introduces it. Exported from this internal module and
// re-exported by the package API.
export function createSolverStats(): SolverStats {
  return {
    decisions: 0,
    propagations: 0,
    conflicts: 0,
    restarts: 0,
    learnedClauses: 0,
    learnedClausesCurrent: 0,
    learnedLiterals: 0,
    minimizedLiterals: 0,
  };
}

// Overrides heuristic choices at decision points: it receives named, unassigned
// variables only, and may return null to defer to the VSIDS default. The
// caller revalidates the returned name/preference, so the hook cannot force an
// already-assigned or unknown variable.
export type VariablePriority = (
  unassigned: Variable[],
  assignments: Partial<Record<Variable, Value>>,
) => [Variable, boolean] | null;

interface SolverOptions {
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  enablePle?: boolean | undefined;
  stats?: SolverStats | undefined;
  // Non-throwing conflict budget (Design § Target Public API, Budget
  // contract): a non-negative safe integer; undefined means unlimited. ONE
  // budget spans an entire API call — construction through the terminal
  // search for single-shot/enumeration use, or one solveAssuming call when a
  // per-call budget is passed there instead. Exhaustion never throws: it
  // surfaces through the resumable core as 'unknown'.
  conflictBudget?: number | undefined;
  // Internal restart-policy selector; never forwarded by public options.
  // 'ema' (the default) is knob-free; 'luby' explicitly selects the retained
  // Luby schedule, which restartBaseConflicts then configures. Passing the
  // base alone never selects Luby.
  restartPolicy?: 'ema' | 'luby' | undefined;
  // Internal Luby base conflict-budget calibration only; inert under the
  // default EMA policy. Never forwarded by public options.
  restartBaseConflicts?: number | undefined;
  // New learned admissions per reduction round, not a cap on protected clauses.
  // Internal only: neither this knob nor Solver is exported by the public API.
  learnedClauseReductionThreshold?: number | undefined;
}

// searchSlice results: 'paused' means the work QUANTUM is spent (resumable);
// 'unknown' means the conflict BUDGET is spent (terminal for this call — the
// budget decides whether to continue, the quantum only when the event loop
// gets control). 'unknown' is never cached in SearchState.verdict: it is not
// an established verdict, and a resumed slice re-derives it. SearchVerdict is
// exported from this internal module only (test audit subclasses override
// search()); never re-exported from the package API.
export type SearchVerdict = 'sat' | 'unsat' | 'unknown';
type SearchResult = SearchVerdict | 'paused';

// The async core verdict: searchSlice's verdicts plus the abort reason.
// Abortion is detected by the async drivers at slice checkpoints, never by
// the core; budget exhaustion is reported by the core as 'unknown'.
type AsyncVerdict =
  | { status: 'sat' }
  | { status: 'unsat' }
  | { status: 'unknown'; reason: 'conflictBudget' | 'aborted' };

// rootBasis dependency bits (Design § Learning with provenance): a level-0
// assignment's justification may depend on caller-supplied assumptions or on
// PLE pins, never on those contexts for a base-derived (zero) root fact. The
// union rule in enqueue propagates taint through root implications.
const ROOT_BASIS_ASSUMPTION = 1;
const ROOT_BASIS_PLE = 2;

interface SearchState {
  assumptions: readonly number[];
  // The current trail level is the replay cursor within assumptions. Keeping
  // the prefix phase avoids restarting propagation between dummy prefix steps.
  phase: 'startup' | 'search' | 'prefix';
  verdict: 'sat' | 'unsat' | null;
}

interface PropagationCursor {
  event: number;
  falseLit: number;
  // Binary-clause lists are drained before the long-clause lists (implicit
  // propagation first); `nextWatch` is the walk index within the active list.
  phase: 'binary' | 'long';
  nextWatch: number;
}

// Gates the trail-invariant audits in enqueue/cancelUntil/propagate. Audits
// are opt-in so default consumers pay nothing for them: the flag initializes
// from SAT_DEBUG=1 through fully guarded optional access — the library's
// single platform-specific reference, importable even where that global is
// absent (browser ESM) — and setDebugAssertions flips it at runtime. Audits
// read the flag at call time, so toggling never depends on import order. The
// test suite enables them globally through its `--import ./test/debug.ts`
// preload.
let debugAssertions = globalThis.process?.env?.SAT_DEBUG === '1';

/**
 * Runtime audit toggle for the test suite. Internal seam: exported from the
 * internal solver module only, never re-exported from the package API.
 */
export function setDebugAssertions(enabled: boolean): void {
  debugAssertions = enabled;
}

// ---------------------------------------------------------------------------
// Conflict budgets and yield quanta (Design § Budgets, Async, and
// Interruptibility)
// ---------------------------------------------------------------------------

// The public budget contract: a non-negative safe integer; undefined means
// unlimited. Anything else (negative, fractional, NaN, Infinity) is a
// descriptive validation error, raised before any cached-UNSAT short-circuit.
function validateConflictBudget(conflictBudget: number | undefined): void {
  if (
    conflictBudget !== undefined &&
    (!Number.isSafeInteger(conflictBudget) || conflictBudget < 0)
  ) {
    throw new Error(`conflictBudget must be a non-negative safe integer, got ${conflictBudget}`);
  }
}

const DEFAULT_YIELD_QUANTUM = 4096;
const MIN_YIELD_QUANTUM = 64;

// The public quantum contract: undefined selects the default; positive safe
// integers below the floor clamp up (browsers clamp nested timers to ~4 ms,
// so the quantum is a work allowance, never a wall-time promise); anything
// else is a descriptive validation error. Exported from this internal module
// for the public wrappers; never re-exported from the package API.
export function normalizeYieldQuantum(yieldQuantum: number | undefined): number {
  if (yieldQuantum === undefined) {
    return DEFAULT_YIELD_QUANTUM;
  }
  if (!Number.isSafeInteger(yieldQuantum) || yieldQuantum < 1) {
    throw new Error(`yieldQuantum must be a positive safe integer, got ${yieldQuantum}`);
  }
  return Math.max(yieldQuantum, MIN_YIELD_QUANTUM);
}

// ---------------------------------------------------------------------------
// Platform-neutral yield scheduling. Async drivers slice search work by
// `yieldQuantum` and hand the event loop control between slices through this
// fallback chain: the WHATWG `scheduler.yield()` global, then a MessageChannel
// post, then `setTimeout(0)`. Every platform global stays
// `globalThis`-qualified, so this module stays importable where any of them
// are absent. A MessageChannel yield owns exactly one channel whose ports are
// both closed when the message lands, and the timer fallback outlives nothing:
// a settled solve retains no ports or listeners and must not keep a Node
// runtime alive.
// ---------------------------------------------------------------------------

export type YieldScheduler = () => Promise<unknown>;

let injectedYieldScheduler: YieldScheduler | undefined;

/**
 * Installs the module-wide yield scheduler used by the async drivers, or
 * restores platform fallback resolution when passed undefined. Internal test
 * seam mirroring setDebugAssertions — exported from this internal module
 * only, never re-exported from the package API.
 */
export function setYieldScheduler(scheduler: YieldScheduler | undefined): void {
  injectedYieldScheduler = scheduler;
}

// The WHATWG scheduling global, structurally typed so the fallback chain
// compiles without the DOM lib.
interface GlobalWithScheduler {
  scheduler?: { yield?: (() => Promise<void>) | undefined } | undefined;
}

// The async option types name the WHATWG `AbortSignal` global, but the
// library reads only `aborted` from it. Declaring that minimal slice here
// keeps every compilation self-sufficient — no DOM lib or platform typings
// required — while interface merging composes it with the full DOM/Node
// declarations whenever a program provides them (both declare the identical
// `readonly aborted: boolean`, so the merge cannot conflict). This module
// ships, so the declaration reaches consumers through dist/solver.d.ts.
declare global {
  interface AbortSignal {
    readonly aborted: boolean;
  }
}

// Read through a function so TypeScript's property narrowing cannot freeze a
// stale non-aborted value after an early return — the whole point of an
// AbortSignal is that `aborted` flips asynchronously between checkpoints.
function signalAborted(signal: AbortSignal | undefined): boolean {
  return signal?.aborted === true;
}

// The channel's DOM-ish surface, structurally typed: Node's global
// MessageChannel honors onmessage/postMessage/close at runtime even where its
// bundled typings diverge (EventEmitter-style declarations), and browsers
// match natively.
interface YieldChannel {
  port1: { onmessage: (() => void) | null; close(): void };
  port2: { onmessage: (() => void) | null; close(): void; postMessage(message: unknown): void };
}

// Resolved once per async call; a scheduler whose Promise rejects fails that
// call, and every owned port/listener is released per yield.
function resolveYieldScheduler(): YieldScheduler {
  if (injectedYieldScheduler !== undefined) {
    return injectedYieldScheduler;
  }
  const scheduler = (globalThis as GlobalWithScheduler).scheduler;
  const yieldNow = scheduler?.yield;
  if (typeof yieldNow === 'function') {
    return () => yieldNow.call(scheduler);
  }
  const MessageChannelCtor = (
    globalThis as unknown as { MessageChannel?: (new () => YieldChannel) | undefined }
  ).MessageChannel;
  if (typeof MessageChannelCtor === 'function') {
    // One owned channel per yield: both ports close when the message lands,
    // so a settled solve leaks neither ports nor listeners.
    return () =>
      new Promise<void>((resolve) => {
        const channel = new MessageChannelCtor();
        channel.port1.onmessage = () => {
          channel.port1.onmessage = null;
          channel.port1.close();
          channel.port2.close();
          resolve();
        };
        channel.port2.postMessage(null);
      });
  }
  return () =>
    new Promise<void>((resolve) => {
      globalThis.setTimeout(resolve, 0);
    });
}

// One-based Luby sequence: S_k = S_(k-1), S_(k-1), 2^(k-1).
// Find the containing block, then descend iteratively into its two copies.
// Arithmetic, not bitwise shifts, keeps indices beyond 32 bits exact. This
// helper is exported only from the internal module, not the package API.
export function luby(index: number): number {
  if (!Number.isSafeInteger(index) || index < 1) {
    throw new Error('Luby index must be a positive safe integer');
  }
  let size = 1;
  let value = 1;
  while (size < index) {
    size = size * 2 + 1;
    value *= 2;
  }
  while (index !== size) {
    size = (size - 1) / 2;
    value /= 2;
    if (index > size) {
      index -= size;
    }
  }
  return value;
}

// ---------------------------------------------------------------------------
// Restart policies (Design § Solver Core, Restart policy: the pinned
// configuration). A policy is a self-contained decision unit — state plus
// post-transaction inputs, with no coupling to solver internals — so tests
// can drive it directly with scripted LBD and trail-length streams. The
// search calls onConflict() exactly once per learned-conflict transaction;
// resetSearch() starts each search's fresh epoch. These classes are exported
// only from this internal module, never from the package API.
// ---------------------------------------------------------------------------

// Observations handed to the policy after a conflict transaction.
export interface RestartSample {
  // LBD of the clause this conflict's analysis just learned.
  readonly lbd: number;
  // Trail length AFTER the transaction (learned assertion enqueued) and
  // BEFORE any restart cancellation — never the emptied post-cancel trail.
  readonly trailLength: number;
  // Whether the transaction's backjump already returned the trail to root.
  readonly atRoot: boolean;
}

// 'blocked' is observational (the solver treats it as 'none'); 'restart'
// consumes the epoch, and `actual` distinguishes a real positive-level
// cancellation from an already-root no-op.
export type RestartVerdict =
  | { readonly kind: 'none' }
  | { readonly kind: 'blocked' }
  | { readonly kind: 'restart'; readonly actual: boolean };

// Shared verdict singletons: the hot conflict path must not allocate. The
// policies never mutate them; callers only read `kind`/`actual`.
const VERDICT_NONE: RestartVerdict = { kind: 'none' };
const VERDICT_BLOCKED: RestartVerdict = { kind: 'blocked' };
const VERDICT_RESTART_ACTUAL: RestartVerdict = { kind: 'restart', actual: true };
const VERDICT_RESTART_NOOP: RestartVerdict = { kind: 'restart', actual: false };

// The retained Luby schedule: conflict epochs of base × luby(1..n), counted
// in base-sized blocks — this implements base * luby(index) without an unsafe
// Number product or a unit-increment counter that could stop advancing above
// 2^53. Ordinary backjumps do NOT reset the epoch. Selected explicitly via
// the internal restartPolicy knob; never the default.
export class LubyRestartPolicy {
  readonly kind = 'luby' as const;
  readonly baseConflicts: number;
  restartIndex = 1;
  blocksUntilRestart = luby(1);
  conflictsInBlock = 0;

  constructor(baseConflicts: number) {
    this.baseConflicts = baseConflicts;
  }

  resetSearch(): void {
    this.restartIndex = 1;
    this.blocksUntilRestart = luby(1);
    this.conflictsInBlock = 0;
  }

  onConflict(sample: RestartSample): RestartVerdict {
    this.conflictsInBlock += 1;
    if (this.conflictsInBlock === this.baseConflicts) {
      this.conflictsInBlock = 0;
      this.blocksUntilRestart -= 1;
      if (this.blocksUntilRestart === 0) {
        // Consume an exhausted epoch even if the normal backjump already
        // reached root. That root-level no-op is not an additional restart.
        this.restartIndex += 1;
        this.blocksUntilRestart = luby(this.restartIndex);
        return sample.atRoot ? VERDICT_RESTART_NOOP : VERDICT_RESTART_ACTUAL;
      }
    }
    return VERDICT_NONE;
  }
}

// Pinned deterministic EMA configuration (plan-d285: "EMA/retention constants
// are pinned but arbitrary"; changing them is a benchmark-disclosed decision,
// never silent tuning).
const EMA_ALPHA_FAST = 0.25;
const EMA_ALPHA_SLOW = 0.02;
const EMA_RESTART_INTERVAL = 32;
const EMA_RESTART_RATIO = 1.25;
const EMA_BLOCK_FACTOR = 1.1;

// The default restart policy: deterministic Glucose-style EMA restarts with
// blocking. The fast (α=0.25) and slow (α=0.02) LBD averages initialize to
// the FIRST learned clause's LBD, then update on every conflict over the
// solver's LIFETIME — deliberately across searches and incremental calls, so
// call N's restart timing may depend on earlier calls' LBD history (disclosed
// in the migration notes). The per-search epoch — the conflicts-since
// counter, the postponement deadline, and the blocking snapshot — resets on
// resetSearch(); the EMA histories never do.
export class EmaRestartPolicy {
  readonly kind = 'ema' as const;
  // Lifetime LBD histories; null until the first learned LBD seeds both.
  emaFast: number | null = null;
  emaSlow: number | null = null;
  // Per-search epoch state.
  conflictsSinceRestart = 0;
  nextEligibleAt = EMA_RESTART_INTERVAL;
  // Trail length sampled at this search's previous ACTUAL (positive-level)
  // restart; null until then, so a search's first triggered attempt is
  // unblocked. Root no-ops never create a snapshot.
  previousRestartTrail: number | null = null;

  resetSearch(): void {
    this.conflictsSinceRestart = 0;
    this.nextEligibleAt = EMA_RESTART_INTERVAL;
    this.previousRestartTrail = null;
  }

  onConflict(sample: RestartSample): RestartVerdict {
    let fast = this.emaFast;
    let slow = this.emaSlow;
    if (fast === null || slow === null) {
      fast = sample.lbd;
      slow = sample.lbd;
    } else {
      fast += EMA_ALPHA_FAST * (sample.lbd - fast);
      slow += EMA_ALPHA_SLOW * (sample.lbd - slow);
    }
    this.emaFast = fast;
    this.emaSlow = slow;
    this.conflictsSinceRestart += 1;
    if (this.conflictsSinceRestart < this.nextEligibleAt) {
      return VERDICT_NONE;
    }
    if (!(fast > EMA_RESTART_RATIO * slow)) {
      return VERDICT_NONE;
    }
    if (
      this.previousRestartTrail !== null &&
      sample.trailLength > EMA_BLOCK_FACTOR * this.previousRestartTrail
    ) {
      // Blocking: the trail grew past 1.1× its length at the previous actual
      // restart, so postpone the next eligible check by one full interval.
      // The epoch is NOT consumed and no new snapshot is taken.
      this.nextEligibleAt = this.conflictsSinceRestart + EMA_RESTART_INTERVAL;
      return VERDICT_BLOCKED;
    }
    // Consume the epoch. An already-root no-op neither counts as a restart
    // nor records a blocking snapshot.
    this.conflictsSinceRestart = 0;
    this.nextEligibleAt = EMA_RESTART_INTERVAL;
    if (sample.atRoot) {
      return VERDICT_RESTART_NOOP;
    }
    this.previousRestartTrail = sample.trailLength;
    return VERDICT_RESTART_ACTUAL;
  }
}

export type RestartPolicy = EmaRestartPolicy | LubyRestartPolicy;

// One watch-list entry: the watched clause plus a cached BLOCKER literal —
// the clause's current OTHER watched literal (MiniSat). When the blocker is
// currently true, the clause is satisfied and propagation skips the clause
// dereference entirely. Parity invariant: an entry's blocker always equals
// the clause's current other watch, in BOTH lists — established at attach,
// rewritten on inspection (refresh), and kept in step on relocation by
// updating the cross-linked twin entry in the other watch list. A stale
// blocker could be true where the actual other watch is not, skipping a
// relocation the unblocked loop would perform and silently changing watch
// order (and thereby potentially later counters); the invariant keeps the
// skip condition exactly equivalent to the pre-blocker other-watch check.
// Internal only: exported from this module for observation tooling, never
// re-exported from the package API.
export interface WatchEntry {
  readonly clause: Clause;
  blocker: number;
  // The entry for the same clause in the OTHER watch list. Null only
  // transiently inside attachClause while the pair is cross-linked.
  twin: WatchEntry | null;
}

// One binary-clause watch entry: the clause plus its OTHER literal. Binary
// clauses propagate implicitly — the other literal is known without
// dereferencing the clause's literal array; the clause object is needed only
// as the enqueue reason or as the returned conflict. Binary watches never
// relocate (both literals are always watched), so no blocker/twin tracking
// is required. Internal only, like WatchEntry.
export interface BinaryWatchEntry {
  readonly clause: Clause;
  readonly other: number;
}

export class Solver {
  // Per-variable state is sized numVars at construction and REALLOCATED AND
  // COPIED by ensureCapacity() when add() grows the variable count (Design §
  // Incremental Clause Addition): assigns, level, reason, rootBasis,
  // activity, polarity, seen, the named flags, and heapPosition. Observation
  // tooling must therefore re-read these fields per operation rather than
  // caching an array reference across an add().
  assigns: Int8Array;
  level: Int32Array;
  reason: Array<Clause | null>;
  // Level-0 dependency provenance per variable (ROOT_BASIS_* bits): zero marks
  // a base-derived root fact; nonzero marks assumption/PLE-tainted ancestry.
  // Meaningful only while the variable is assigned at level 0; cancellation
  // resets it with the assignment, and a root (re-)enqueue recomputes it.
  rootBasis: Uint8Array;
  activity: Float64Array;
  polarity: Int8Array;
  // Named-variable membership per GLOBAL variable index (1 = named). After
  // add(), named indices are no longer contiguous — a batch's new names are
  // appended after all existing indices, auxiliaries included — so every
  // named test (heap membership, unassignedNamed accounting, model
  // projection, blocker construction, hook inputs, the trail audit) consults
  // this flag instead of the v2 `index < numNamedVars` invariant.
  named: Uint8Array;
  readonly trail: number[] = [];
  readonly trailLim: number[] = [];
  qhead = 0;

  readonly clauses: Clause[];
  // Two-watched-literal lists for LONG clauses (3+ literals): `watches[l]`
  // holds an entry for every long clause currently watching literal `l` —
  // i.e. l is one of that clause's two watched literals, kept at
  // clause.lits[0] or clause.lits[1] (the MiniSat in-place swap convention).
  // Entries carry the clause object reference, never an index, so clause
  // deletion can never dangle a watch, plus the blocker literal and twin
  // link (see WatchEntry). Clause attachment and propagation's watch
  // relocation preserve that identity. Binary clauses live in
  // `binaryWatches` instead.
  readonly watches: WatchEntry[][];
  // Dedicated binary-clause watch lists (separately measured experiment):
  // `binaryWatches[l]` holds an entry for every 2-literal clause containing
  // `l`, keyed by the OTHER literal for implicit propagation. Drained before
  // the long-clause lists on every falsified event.
  readonly binaryWatches: BinaryWatchEntry[][];
  readonly stats: SolverStats;
  readonly variablePriority: VariablePriority | undefined;

  private readonly cnf: CompiledCnf;
  // The growable symbol table (Design § Incremental Clause Addition), copied
  // from the compiled CNF at construction so the caller-visible CompiledCnf
  // handle never changes, then extended by add(). indexToName is indexed by
  // GLOBAL variable index with holes (undefined) at auxiliary slots; the
  // `named` flag says which indices are named.
  private readonly nameToIndex: Map<Variable, number>;
  private readonly indexToName: Array<Variable | undefined>;
  private readonly enablePle: boolean;
  private readonly conflictBudget: number | undefined;
  private readonly restartBaseConflicts: number;
  private readonly restartPolicy: RestartPolicy;
  private readonly learnedClauseReductionThreshold: number;
  private learnedSinceReduction = 0;
  // Semantic clause identity must not depend on the mutable watch order.
  private readonly clauseByKey = new Map<string, Clause>();
  private seen: Uint8Array;
  // Variables marked in `seen` by the most recent analyze() call. Entry-time
  // cleanup reverts exactly these marks instead of refilling the whole array,
  // so per-conflict clearing costs O(touched) rather than O(numVars).
  private readonly seenTouched: number[] = [];
  // Trusted handoff from analyze(): the clause object it just produced plus
  // the already-normalized (sorted, deduplicated, tautology-free) literal
  // vector behind it. The search registers analyze()'s result through
  // addLearnedClause() immediately, so that path reuses this vector and
  // normalization runs exactly once per learned clause. Every other caller —
  // and any clause object that does not match this handoff — normalizes in
  // full; the handoff is consumed on first use.
  private analyzedNormalized: { clause: Clause; normalized: number[] } | null = null;
  private varInc = 1;
  // Clause-activity increment for the pinned decayed scheme (Design § Solver
  // Core, Retention policy): analysis bumps use the CURRENT increment, which
  // grows by 1/0.999 after each reduction round, so older bumps decay
  // relative to newer ones. This is LIFETIME clause-aging accounting — like
  // varInc and the reduction cadence, it is deliberately independent of the
  // resettable per-call output stats.
  private claInc = 1;
  // Indexed binary max-heap, ordered by activity then LOWER variable index.
  // Only named variables have positions; -1 means absent (which covers every
  // auxiliary slot: heapPosition is sized numVars and indexed by global
  // variable index, so the `named` flag decides heap eligibility).
  // Assignments made by propagation or the hook remain lazily in the heap
  // until popped.
  private readonly decisionHeap: number[];
  private heapPosition: Int32Array;
  // An O(1) termination check avoids scanning all named variables at every
  // decision, which would defeat the heap's logarithmic selection cost.
  private unassignedNamed: number;
  // The lifetime conflict counter, independent of any pre-existing
  // output-counter offsets; a budget scope snapshots it as its baseline.
  private conflictsSoFar = 0;
  // Call-scoped conflict budget (Design § Budget contract): ONE budget spans
  // an entire API call — construction through the terminal search for
  // enumeration (never reset per model), or one solveAssuming invocation when
  // a per-call budget is passed there. The budget-zero startup allowance
  // fires at most once per call: 'fresh' until the first startup propagation
  // pass under an already-exhausted budget, 'active' while that pass is
  // resumable, 'spent' once it settles or the search ends — it never re-arms
  // after learning or between enumeration models.
  private budget: {
    readonly cap: number;
    readonly baseline: number;
    startupAllowance: 'fresh' | 'active' | 'spent';
  } | null = null;
  private startupConflict: Clause | null = null;
  private startupConflictReported = false;
  // UNSAT-core extraction state (Design § UNSAT Cores). The FIRST constructor
  // assumption found already-false at root is recorded alongside the
  // explaining clause: that clause is SATISFIED by the existing assignment,
  // so walking it alone would produce a bogus empty core — the rejected
  // literal seeds the walk. `pleConflict` retains the clause a failed
  // pure-literal round conflicted on, and `constructorAssumptions` (the
  // validated translated literals) backs PLE-leaf widening.
  private startupRejectedAssumption: number | null = null;
  private pleConflict: Clause | null = null;
  private readonly constructorAssumptions: readonly number[];
  // The core extracted at the most recent UNSAT verdict, BEFORE any cleanup
  // cancellation. Reset by startSearch; survives finishSearch so the caller
  // can read it after solve()/solveAssuming() returns.
  private extractedCore: VariableAssignments | null = null;
  private permanentUnsat = false;
  private incrementalCallActive = false;
  private searchState: SearchState | null = null;
  // Pending propagation outlives an abandoned search. Cleanup rewinds retained
  // events before dropping this cursor, even on a root-level no-op cancellation.
  private propagationCursor: PropagationCursor | null = null;
  // Call-scoped, NOT search-scoped: short enumeration searches share a slice.
  private scheduling: { quantum: number; remaining: number } | null = null;
  private enumerationActive = false;

  constructor(cnf: CompiledCnf, opts: SolverOptions = {}) {
    validateConflictBudget(opts.conflictBudget);
    if (
      opts.restartBaseConflicts !== undefined &&
      (!Number.isSafeInteger(opts.restartBaseConflicts) || opts.restartBaseConflicts < 1)
    ) {
      throw new Error('restartBaseConflicts must be a positive safe integer');
    }
    if (
      opts.restartPolicy !== undefined &&
      opts.restartPolicy !== 'ema' &&
      opts.restartPolicy !== 'luby'
    ) {
      throw new Error("restartPolicy must be 'ema' or 'luby'");
    }
    if (
      opts.learnedClauseReductionThreshold !== undefined &&
      (!Number.isSafeInteger(opts.learnedClauseReductionThreshold) ||
        opts.learnedClauseReductionThreshold < 1)
    ) {
      throw new Error('learnedClauseReductionThreshold must be a positive safe integer');
    }

    this.cnf = cnf;
    this.assigns = new Int8Array(cnf.numVars).fill(Value.UNSET);
    this.level = new Int32Array(cnf.numVars);
    this.reason = Array<Clause | null>(cnf.numVars).fill(null);
    this.rootBasis = new Uint8Array(cnf.numVars);
    this.seen = new Uint8Array(cnf.numVars);
    this.activity = new Float64Array(cnf.numVars);
    this.polarity = new Int8Array(cnf.numVars).fill(Value.FALSE);
    // Copy the symbol table: the caller's CompiledCnf handle stays immutable
    // while add() extends these solver-owned structures. indexToName is
    // indexed by global variable index; auxiliary slots are holes.
    this.nameToIndex = new Map(cnf.nameToIndex);
    this.indexToName = Array.from({ length: cnf.numVars }, (_, index) => cnf.indexToName[index]);
    // At construction the named variables are exactly 0..numNamedVars-1; the
    // named flag takes over from that contiguous invariant so add() can later
    // append named indices past the auxiliaries.
    this.named = new Uint8Array(cnf.numVars);
    this.decisionHeap = [];
    this.heapPosition = new Int32Array(cnf.numVars).fill(-1);
    this.unassignedNamed = cnf.numNamedVars;
    // All initial activities tie, so index order is already a valid heap.
    for (let variable = 0; variable < cnf.numNamedVars; variable += 1) {
      this.named[variable] = 1;
      this.decisionHeap.push(variable);
      this.heapPosition[variable] = variable;
    }
    this.clauses = [];
    this.watches = Array.from({ length: cnf.numVars * 2 }, () => []);
    this.binaryWatches = Array.from({ length: cnf.numVars * 2 }, () => []);
    this.stats = opts.stats ?? createSolverStats();
    this.variablePriority = opts.variablePriority;
    this.enablePle = opts.enablePle ?? false;
    this.conflictBudget = opts.conflictBudget;
    this.restartBaseConflicts = opts.restartBaseConflicts ?? 100;
    this.restartPolicy =
      opts.restartPolicy === 'luby'
        ? new LubyRestartPolicy(this.restartBaseConflicts)
        : new EmaRestartPolicy();
    this.learnedClauseReductionThreshold = opts.learnedClauseReductionThreshold ?? 10_000;

    // Add clauses before assumptions. Units are deliberately absent from
    // watch lists: they are asserted once at level zero instead. Binary
    // clauses go to the dedicated binaryWatches lists; every longer clause
    // watches its first two literals (positions 0 and 1), and later
    // propagation relocates a watch by swapping it into the falsified
    // literal's slot. The empty clause short-circuits UNSAT.
    for (const clause of cnf.clauses) {
      const normalized = normalizeClauseLits(clause.lits);
      if (normalized === null) {
        continue;
      }
      const key = normalized.join(',');
      if (this.clauseByKey.has(key)) {
        continue;
      }
      // Compiled clauses are already normalized. Preserve their order and
      // object identity; use a sorted COPY only for the canonical key.
      if (normalized.length !== clause.lits.length) {
        clause.lits = normalized;
      }
      this.clauseByKey.set(key, clause);
      this.clauses.push(clause);
      if (clause.lits.length === 0) {
        this.startupConflict ??= clause;
      } else if (clause.lits.length === 1) {
        const lit = clause.lits[0];
        const wasUnset = this.assigns[varOf(lit)] === Value.UNSET;
        if (!this.enqueue(lit, clause)) {
          this.startupConflict ??= clause;
        } else if (wasUnset) {
          this.stats.propagations += 1;
        }
      } else {
        this.attachClause(clause);
      }
    }

    // Validate and translate constructor assumptions once; the translated
    // literal set backs both root installation and PLE-leaf core widening.
    this.constructorAssumptions = this.translateAssumptions(opts.assumptions);
    this.enqueueAssumptions(this.constructorAssumptions);
    this.assertTrailInvariant();
  }

  enqueue(lit: number, reason: Clause | null): boolean {
    const variable = varOf(lit);
    if (variable < 0 || variable >= this.assigns.length) {
      throw new Error(`cannot enqueue out-of-range literal: ${lit}`);
    }
    const wanted = isNeg(lit) ? Value.FALSE : Value.TRUE;
    const current = this.assigns[variable];
    if (current !== Value.UNSET) {
      this.assertTrailInvariant();
      return current === wanted;
    }

    this.assigns[variable] = wanted;
    // Save EVERY successful new assignment, including implications, root
    // units/assumptions, PLE and learned assertions — not just decisions or
    // cancelled assignments. A hook override becomes the latest phase too.
    this.polarity[variable] = wanted;
    if (this.named[variable] === 1) {
      this.unassignedNamed -= 1;
    }
    this.level[variable] = this.trailLim.length;
    this.reason[variable] = reason;
    if (this.trailLim.length === 0) {
      // Root-fact provenance: a root implication unions the dependency masks
      // of its reason's antecedents (a unit-clause reason has none, seeding
      // base-derived zero); a reason-null root enqueue starts untainted and
      // its caller (constructor assumptions, PLE) seeds the matching bit.
      let basis = 0;
      if (reason !== null) {
        for (const antecedent of reason.lits) {
          const other = varOf(antecedent);
          if (other !== variable) {
            basis |= this.rootBasis[other];
          }
        }
      }
      this.rootBasis[variable] = basis;
    }
    this.trail.push(lit);
    this.chargeWork();
    this.assertTrailInvariant();
    return true;
  }

  // A conflict discovered while root facts were installed (empty clause, unit
  // contradiction, contradictory assumption, empty blocker) is cached here.
  // The FIRST propagate() reports it and counts it once; later calls replay
  // the cached clause without re-counting, so stats and the conflict budget
  // agree with the single conflict.
  propagate(): Clause | null {
    // Preserve the uninterrupted observation seam used by internal audits.
    const result = this.propagateSlice(false);
    if (result === 'paused') throw new Error('uninterrupted propagation cannot pause');
    return result;
  }

  private propagateSlice(interruptible: boolean): Clause | null | 'paused' {
    if (this.startupConflict !== null) {
      if (!this.startupConflictReported) {
        this.recordConflict();
        this.startupConflictReported = true;
      }
      return this.startupConflict;
    }

    // Two-watched-literal propagation (MiniSat scheme), with binary clauses
    // on dedicated lists (Experiment B). The trail is drained from `qhead`;
    // dequeuing the (now true) literal `assignedLit` falsifies
    // `neg(assignedLit)`, so only entries watching `neg(assignedLit)` must be
    // examined. Binary entries are drained FIRST (implicit propagation: the
    // entry's `other` literal is the unit/conflict payload, so the clause's
    // literal array is never dereferenced on that path), then long-clause
    // entries. Per long-clause entry:
    //   1. Blocking-literal optimization: one litValue on the entry's cached
    //      blocker (the clause's current other watch). TRUE means satisfied —
    //      skip WITHOUT dereferencing the clause. The blocker parity
    //      invariant (see WatchEntry; audited per visit under debug
    //      assertions) makes this lookup's value exactly the other-watch
    //      value the pre-blocker loop computed after dereferencing.
    //   2. Normalize the falsified watched literal into slot 1 (in-place
    //      swap), so slot 0 holds the other watch; refresh the blocker.
    //   3. Scan slots 2.. for any literal that is not false; the first such
    //      literal becomes the replacement watch (in-place swap: slot 1 takes
    //      the candidate, the falsified literal moves into the vacated slot;
    //      the entry is removed from this list and appended to the
    //      candidate's list, and the TWIN entry's blocker is updated to the
    //      candidate — this entry's own blocker still names slot 0, which the
    //      swap does not change). If none exists, the clause is unit
    //      (enqueue the other watch) or conflicting (return it), decided by
    //      the already-computed other-watch value.
    // The list is mutated while iterated, so it is walked backwards: removing
    // an entry swaps the current slot with the last element and pops, and
    // every element above the current slot has already been examined, so no
    // unexamined entry can be displaced. Entries whose clause is unit or that
    // stay watching the falsified literal remain in the list.
    while (this.propagationCursor !== null || this.qhead < this.trail.length) {
      if (interruptible && this.workExhausted()) return 'paused';
      if (this.propagationCursor === null) {
        const event = this.qhead++;
        const falseLit = neg(this.trail[event]);
        this.propagationCursor = {
          event,
          falseLit,
          phase: 'binary',
          nextWatch: this.binaryWatches[falseLit].length - 1,
        };
      }
      const cursor = this.propagationCursor;
      const falseLit = cursor.falseLit;

      if (cursor.phase === 'binary') {
        const binaryList = this.binaryWatches[falseLit];
        if (binaryList === undefined) {
          throw new Error(`missing binary watch list for literal: ${falseLit}`);
        }
        while (cursor.nextWatch >= 0) {
          if (interruptible && this.workExhausted()) return 'paused';
          const index = cursor.nextWatch--;
          this.chargeWork();
          const entry = binaryList[index];
          const otherValue = litValue(entry.other, this.assigns);
          if (otherValue === Value.TRUE) {
            continue;
          }
          if (otherValue === Value.FALSE) {
            this.recordConflict();
            this.propagationCursor = null;
            return entry.clause;
          }
          if (!this.enqueue(entry.other, entry.clause)) {
            this.recordConflict();
            this.propagationCursor = null;
            return entry.clause;
          }
          this.stats.propagations += 1;
        }
        cursor.phase = 'long';
        cursor.nextWatch = this.watches[falseLit].length - 1;
      }

      const watchList = this.watches[falseLit];
      if (watchList === undefined) {
        throw new Error(`missing watch list for literal: ${falseLit}`);
      }

      while (cursor.nextWatch >= 0) {
        if (interruptible && this.workExhausted()) return 'paused';
        const index = cursor.nextWatch--;
        this.chargeWork();
        const entry = watchList[index];
        // ONE literal lookup per visit: the blocker always equals the clause's
        // current other watch (twin-kept parity invariant), so its value
        // doubles as the other-watch value after dereferencing — the previous
        // loop's second litValue call on the same literal is gone.
        const otherValue = litValue(entry.blocker, this.assigns);
        if (otherValue === Value.TRUE) {
          continue;
        }
        const clause = entry.clause;
        if (clause.lits[0] === falseLit) {
          clause.lits[0] = clause.lits[1];
          clause.lits[1] = falseLit;
        }
        const otherWatch = clause.lits[0];
        if (debugAssertions && entry.blocker !== otherWatch) {
          throw new Error(`blocker invariant violated: ${entry.blocker} is not the other watch`);
        }
        // Refresh on inspection: a no-op store while the invariant holds,
        // keeping the entry truthful even if watch slots were swapped since
        // the last visit of this list.
        entry.blocker = otherWatch;

        let relocated = false;
        for (let k = 2; k < clause.lits.length; k += 1) {
          const candidate = clause.lits[k];
          if (litValue(candidate, this.assigns) !== Value.FALSE) {
            clause.lits[1] = candidate;
            clause.lits[k] = falseLit;
            const candidateWatchList = this.watches[candidate];
            if (candidateWatchList === undefined) {
              throw new Error(`missing watch list for literal: ${candidate}`);
            }
            const twin = entry.twin;
            if (twin === null) {
              throw new Error(`watch entry is missing its twin: ${falseLit}`);
            }
            // From the twin's list the clause's other watch is the slot-1
            // literal, which this swap just replaced; keep the twin in step
            // so NO list ever holds a stale blocker.
            twin.blocker = candidate;
            candidateWatchList.push(entry);
            const lastIndex = watchList.length - 1;
            watchList[index] = watchList[lastIndex];
            watchList.pop();
            relocated = true;
            break;
          }
        }
        if (relocated) {
          continue;
        }

        if (otherValue === Value.FALSE) {
          this.recordConflict();
          this.propagationCursor = null;
          return clause;
        }
        if (!this.enqueue(otherWatch, clause)) {
          this.recordConflict();
          this.propagationCursor = null;
          return clause;
        }
        this.stats.propagations += 1;
      }
      this.propagationCursor = null;
    }

    return null;
  }

  // Analyze before cancelling: reasons and levels describe an acyclic
  // implication graph whose conflict clause is falsified. Walk ALL enqueued
  // assignments backwards, including the tail not yet processed by propagate.
  // A count of one current-level literal is the first UIP, even if its reason
  // is non-null; resolving past it would instead learn a later/decision UIP.
  // The O(clause) invariant scans (falsified conflict clause, falsified reason
  // antecedents) are debug audits, like the trail checks: they run throughout
  // the test suite and cost default consumers nothing.
  analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    const currentLevel = this.trailLim.length;
    if (currentLevel === 0) {
      throw new Error('conflict analysis requires a nonzero decision level');
    }
    if (
      debugAssertions &&
      !conflict.lits.every((lit) => litValue(lit, this.assigns) === Value.FALSE)
    ) {
      throw new Error('conflict analysis requires a falsified clause');
    }

    // Touched-only clearing: revert exactly the marks the previous analysis
    // left behind (the list survives even a throwing analysis) instead of
    // refilling the entire array once per conflict.
    for (let index = 0; index < this.seenTouched.length; index += 1) {
      this.seen[this.seenTouched[index]] = 0;
    }
    this.seenTouched.length = 0;
    const learnedLits: number[] = [];
    let currentCount = 0;
    let trailIndex = this.trail.length - 1;
    let resolvedVariable = -1;
    let clause = conflict;
    let assertingLit: number;
    while (true) {
      // Decayed clause activity: the conflict seed and every reason actually
      // consumed are bumped by the CURRENT increment. The UIP's reason is NOT
      // consumed or bumped.
      this.bumpClauseActivity(clause);
      // Dynamic LBD tightening (Design § Solver Core, Retention policy), the
      // Glucose "dynamic nblevel" rule: on analysis reuse, a REDUCIBLE-tier
      // clause's stored score tightens to the current distinct-nonzero-level
      // count when the recomputation improves it by at least two — never an
      // increase — which can promote the clause into the glue tier. The
      // one-step hysteresis keeps incidental level drift from eroding the
      // reducible tier (single-step recomputes carry no lasting signal);
      // permanent clauses (lbd 0) and current glue clauses never participate.
      if (clause.lbd > 2) {
        const tightened = this.computeClauseLbd(clause.lits);
        if (tightened + 1 < clause.lbd) {
          clause.lbd = tightened;
        }
      }
      for (const lit of clause.lits) {
        const variable = varOf(lit);
        // Reason watch slots can move, so skip the pivot by variable identity,
        // never by assuming it occupies a particular position in its reason.
        if (variable === resolvedVariable || this.seen[variable] !== 0) {
          continue;
        }
        if (debugAssertions && litValue(lit, this.assigns) !== Value.FALSE) {
          throw new Error('conflict analysis reason antecedents must be falsified');
        }
        this.seen[variable] = 1;
        this.seenTouched.push(variable);
        // Once per seen variable, including root antecedents, auxiliaries
        // and variables that disappear from the learned clause by resolution.
        this.bumpVariableActivity(variable);
        const level = this.level[variable];
        if (level === currentLevel) {
          currentCount += 1;
        } else if (level > 0 || this.rootBasis[variable] !== 0) {
          // Retain non-root antecedents, plus level-zero antecedents with
          // assumption/PLE provenance: those are not base-formula
          // consequences, so dropping them would silently make the learned
          // clause depend on that root context (breaking later core
          // extraction). A BASE-DERIVED root fact is a consequence of the
          // permanent clause database, so it drops out (MiniSat's root
          // skipping) while the learned clause stays unconditionally
          // entailed. A dropped root antecedent stays seen-marked: in
          // minimization it reads as resolving into the clause, which is
          // sound exactly because it is base-entailed.
          learnedLits.push(lit);
        }
      }
      if (currentCount === 0) {
        throw new Error('conflict must involve the current decision level');
      }

      let pivot: number | undefined;
      while (trailIndex >= 0) {
        const lit = this.trail[trailIndex--];
        const variable = varOf(lit);
        if (this.seen[variable] !== 0 && this.level[variable] === currentLevel) {
          pivot = lit;
          break;
        }
      }
      if (pivot === undefined) {
        throw new Error('conflict analysis could not find a current-level trail literal');
      }
      currentCount -= 1;
      if (currentCount === 0) {
        assertingLit = neg(pivot);
        break;
      }
      resolvedVariable = varOf(pivot);
      const reason = this.reason[resolvedVariable];
      if (reason === null) {
        throw new Error('conflict analysis reached a decision before the first UIP');
      }
      clause = reason;
    }

    // Iterative recursive minimization (ccmin_mode=2 semantics; Design §
    // Learning with provenance): a non-asserting literal is removable when
    // its reason's antecedents all resolve into the learned clause. Retained
    // tainted root literals are poison — never removed, and an unmarked
    // tainted root antecedent blocks a removal that would silently resolve
    // through it. MiniSat's abstract-level bitmask prunes the recursion.
    let abstractLevels = 0;
    for (const lit of learnedLits) {
      abstractLevels |= 1 << (this.level[varOf(lit)] & 31);
    }
    let minimized = 0;
    let keptCount = 0;
    for (let read = 0; read < learnedLits.length; read += 1) {
      const lit = learnedLits[read];
      const variable = varOf(lit);
      if (
        this.level[variable] === 0 ||
        this.reason[variable] === null ||
        !this.litRedundant(variable, abstractLevels)
      ) {
        learnedLits[keptCount] = lit;
        keptCount += 1;
      } else {
        // Removed literals stay seen-marked (MiniSat analyze_toclear
        // semantics): transitively implied by the retained remainder.
        minimized += 1;
      }
    }
    learnedLits.length = keptCount;
    learnedLits.push(assertingLit);
    this.stats.learnedLiterals += learnedLits.length;
    this.stats.minimizedLiterals += minimized;

    const normalized = normalizeClauseLits(learnedLits);
    if (normalized === null || normalized.length === 0) {
      throw new Error('first-UIP analysis must produce a nonempty, non-tautological clause');
    }
    const lits = this.orderAssertingLits(normalized, assertingLit);
    // Score the final minimized clause with the shared LBD metric: retained
    // tainted root literals (level zero) do not inflate the score, restoring
    // glue-tier (LBD<=2) protection for root-touching clauses. Computing this
    // later would be wrong: backjumping/asserting can merge the levels of the
    // remaining literals.
    const lbd = this.computeClauseLbd(lits);
    // MiniSat's relative decay: future conflicts get a larger increment.
    // This must follow ALL bumps (and any rescaling) for this conflict.
    this.varInc *= 1 / 0.95;
    const learned: Clause = { lits, learned: true, activity: 0, lbd };
    // Hand the already-normalized vector to the search's immediate
    // registration (see analyzedNormalized): addLearnedClause re-normalizing
    // it would repeat this conflict's most expensive analysis step.
    this.analyzedNormalized = { clause: learned, normalized };
    return {
      learned,
      backjumpLevel: lits.length === 1 ? 0 : this.level[varOf(lits[1])],
    };
  }

  // ccmin_mode=2 recursive redundancy test, iterative over an explicit stack
  // (no recursion in the solver core). `variable` is a learned-clause member
  // with a non-null reason. Returns true when every antecedent chain resolves
  // into the learned clause (seen-marked), into base-derived root facts, or
  // into recursively redundant literals within the clause's abstract levels.
  // Newly seen-marked variables STAY marked on success (they are implied by
  // the retained clause); on failure exactly this call's marks are reverted.
  private litRedundant(variable: number, abstractLevels: number): boolean {
    const stack: number[] = [variable];
    const marked: number[] = [];
    let current = stack.pop();
    while (current !== undefined) {
      const reason = this.reason[current];
      if (reason === null) {
        throw new Error('recursive minimization requires a non-null reason');
      }
      for (const lit of reason.lits) {
        const antecedent = varOf(lit);
        if (antecedent === current || this.seen[antecedent] !== 0) {
          continue;
        }
        const level = this.level[antecedent];
        if (level === 0) {
          if (this.rootBasis[antecedent] === 0) {
            // Base-derived root antecedents resolve away, exactly like the
            // level-zero skip in first-UIP analysis.
            continue;
          }
          // Tainted root poison: removing the literal would silently resolve
          // through an assumption/PLE-derived fact absent from the clause.
          for (const markedVariable of marked) {
            this.seen[markedVariable] = 0;
          }
          return false;
        }
        if (this.reason[antecedent] !== null && (abstractLevels & (1 << (level & 31))) !== 0) {
          this.seen[antecedent] = 1;
          this.seenTouched.push(antecedent);
          marked.push(antecedent);
          stack.push(antecedent);
        } else {
          for (const markedVariable of marked) {
            this.seen[markedVariable] = 0;
          }
          return false;
        }
      }
      current = stack.pop();
    }
    return true;
  }

  // Register a learned consequence, with its intended assertion in slot 0.
  // Search registers analyze()'s result BEFORE cancellation, while the other
  // literals' levels still identify the second watch. Return the canonical object:
  // reasons, the database and watches must never use separate equal clauses.
  // This does not enqueue, particularly not a learned unit at the OLD level.
  addLearnedClause(learned: Clause): Clause {
    let normalized: number[] | null;
    const handoff = this.analyzedNormalized;
    if (handoff !== null && handoff.clause === learned) {
      // Trusted internal path: analyze() normalized this exact vector on the
      // way out, so registration runs normalization exactly once per learned
      // clause. Consumed on use; re-registration always normalizes in full.
      normalized = handoff.normalized;
      this.analyzedNormalized = null;
    } else {
      normalized = normalizeClauseLits(learned.lits);
    }
    if (normalized === null || normalized.length === 0) {
      throw new Error('a learned clause must be nonempty and non-tautological');
    }
    const key = normalized.join(',');
    const lits = this.orderAssertingLits(normalized, learned.lits[0]);
    const existing = this.clauseByKey.get(key);
    if (existing !== undefined) {
      // An existing clause may watch different literals. Detach BEFORE
      // reordering, then reattach once; originals/blocking clauses stay
      // non-learned and retain their activity and object identity.
      this.detachClause(existing);
      existing.lits = lits;
      this.attachClause(existing);
      return existing;
    }

    learned.lits = lits;
    learned.learned = true;
    this.clauseByKey.set(key, learned);
    this.clauses.push(learned);
    this.attachClause(learned);
    // Count new learned database entries, not live duplicate rediscoveries
    // (units included). Re-deriving a deleted clause IS a new admission.
    this.stats.learnedClauses += 1;
    this.stats.learnedClausesCurrent += 1;
    this.learnedSinceReduction += 1;
    return learned;
  }

  // Permanently strengthen this instance (used for enumeration blockers, NOT
  // per-call assumptions). Undo non-root assignments BEFORE interpreting the
  // clause's truth status: a blocker is false at the just-returned model, but
  // that is not root UNSAT. Then admit through the shared permanent path.
  addPermanentClause(rawLits: readonly number[]): Clause | null {
    if (this.enablePle) {
      throw new Error('permanent clause insertion requires enablePle: false');
    }
    this.cancelUntil(0);
    return this.admitPermanentClause(rawLits);
  }

  // The permanent-path admission shared by addPermanentClause and add():
  // register the full normalized clause, retaining its canonical identity and
  // promoting a learned duplicate to permanent role. The caller must already
  // have cancelled to root: truth status is interpreted against the ROOT
  // assignment, so admission never observes a retractable decision-level
  // state. Root facts may have been processed long ago, so choose live
  // watches and explicitly enqueue a root unit / remember a root conflict at
  // admission. Batch callers (add) cancel ONCE and then admit each clause;
  // admitting must not re-cancel, so observation tooling never sees a
  // registered-but-unattached clause at a cancellation boundary.
  private admitPermanentClause(rawLits: readonly number[]): Clause | null {
    for (const lit of rawLits) {
      if (!Number.isInteger(lit) || lit < 0 || lit >= this.watches.length) {
        throw new Error(`permanent clause contains out-of-range literal: ${lit}`);
      }
    }
    const normalized = normalizeClauseLits(rawLits);
    if (normalized === null) {
      return null;
    }
    const key = normalized.join(',');
    let clause = this.clauseByKey.get(key);
    if (clause === undefined) {
      clause = { lits: normalized, learned: false, activity: 0, lbd: 0 };
      this.clauseByKey.set(key, clause);
      this.clauses.push(clause);
    } else {
      this.detachClause(clause);
      if (clause.learned) {
        clause.learned = false;
        this.stats.learnedClausesCurrent -= 1;
        // Historical admissions and the reduction cadence do not rewind.
      }
    }

    // Root assignments never get undone. Two non-false watches suffice; if
    // only one exists, watch it and a root-false literal. Keep those false
    // antecedents in the clause, including constant assumptions. Structural
    // units alone are unwatched; a longer root-unit clause still has two watches.
    const available: number[] = [];
    const falsified: number[] = [];
    for (const lit of normalized) {
      (litValue(lit, this.assigns) === Value.FALSE ? falsified : available).push(lit);
    }
    clause.lits = [...available, ...falsified];
    this.attachClause(clause);
    if (available.length === 0) {
      // Includes the empty blocker over zero named variables. propagate()
      // reports this conflict once, even with an already-drained root queue.
      this.startupConflict ??= clause;
    } else if (available.length === 1 && litValue(available[0], this.assigns) === Value.UNSET) {
      if (!this.enqueue(available[0], clause)) {
        throw new Error('new permanent root unit must enqueue an unassigned literal');
      }
      this.stats.propagations += 1;
    }
    return clause;
  }

  // Grow every per-variable structure to hold `numVars` variables
  // (reallocate-and-copy; Design § Incremental Clause Addition, Growable
  // state). New slots start UNSET/level 0/no reason/base-derived/activity 0,
  // phase FALSE, unseen, unnamed, and outside the decision heap; the caller
  // (add) then flags and inserts the batch's named variables. Watch lists
  // grow with fresh empty lists so every literal < 2*numVars stays watchable.
  private ensureCapacity(numVars: number): void {
    const current = this.assigns.length;
    if (numVars <= current) {
      return;
    }
    const assigns = new Int8Array(numVars).fill(Value.UNSET);
    assigns.set(this.assigns);
    this.assigns = assigns;
    const level = new Int32Array(numVars);
    level.set(this.level);
    this.level = level;
    const reason = Array<Clause | null>(numVars).fill(null);
    for (let index = 0; index < current; index += 1) {
      reason[index] = this.reason[index];
    }
    this.reason = reason;
    const rootBasis = new Uint8Array(numVars);
    rootBasis.set(this.rootBasis);
    this.rootBasis = rootBasis;
    const seen = new Uint8Array(numVars);
    seen.set(this.seen);
    this.seen = seen;
    const activity = new Float64Array(numVars);
    activity.set(this.activity);
    this.activity = activity;
    const polarity = new Int8Array(numVars).fill(Value.FALSE);
    polarity.set(this.polarity);
    this.polarity = polarity;
    const named = new Uint8Array(numVars);
    named.set(this.named);
    this.named = named;
    const heapPosition = new Int32Array(numVars).fill(-1);
    heapPosition.set(this.heapPosition);
    this.heapPosition = heapPosition;
    for (let lit = current * 2; lit < numVars * 2; lit += 1) {
      this.watches.push([]);
      this.binaryWatches.push([]);
    }
  }

  // Conjoin new constraints into the live handle (Design § Incremental Clause
  // Addition). Failure-atomic staged compile-then-commit: the expression is
  // validated and compiled against the current symbol table into a staged
  // delta BEFORE any solver state mutates, so any throw (malformed node,
  // internal validation) leaves the handle byte-for-byte unchanged and
  // reusable. New named variables are sorted within the batch and appended
  // after all existing indices (deterministic but history-dependent), enter
  // the heap at activity 0 with default polarity FALSE, and become valid
  // assumption/model names immediately. Admission cancels to root —
  // preserving pending retained-root propagation — then routes every clause
  // through the permanent path: normalization, clauseByKey dedupe,
  // root-aware watch selection, root units enqueued with their clause as
  // reason (base-derived mask zero), and root falsification recorded as the
  // cached startup conflict (permanentUnsat on the next verdict). Adding
  // clauses to a UNSAT base keeps it UNSAT, and learned clauses stay sound:
  // the base is only strengthened. No re-preprocessing and NO STATS SCOPE:
  // add() takes no out-param, and its root-unit enqueues land in the lifetime
  // ledger only — like constructor unit installation, they are excluded from
  // every later per-call measurement by that call's entry snapshot.
  add(expr: BooleanExpr): void {
    // A quiescent handle is required: no in-flight async solve (the busy
    // guard spans yields), no reentrant hook call, no in-flight manually
    // driven search slice, and no enumeration in progress.
    if (
      this.incrementalCallActive ||
      this.enumerationActive ||
      (this.searchState !== null && this.searchState.verdict === null)
    ) {
      throw new Error(
        'add() requires a quiescent handle: no in-flight solve or enumeration may be active',
      );
    }
    if (this.enablePle) {
      throw new Error('add() requires enablePle: false');
    }
    const baseVars = this.assigns.length;
    // STAGE: validate and compile the delta. A throw here has touched nothing.
    const delta = compileIncremental(expr, {
      nameToIndex: this.nameToIndex,
      numVars: baseVars,
    });
    // COMMIT: growth first (the heap insert below indexes the new slots),
    // then the symbol table, then clause admission. For a validated delta
    // these steps are total.
    this.ensureCapacity(delta.numVars);
    for (const [offset, name] of delta.newNames.entries()) {
      const variable = baseVars + offset;
      this.nameToIndex.set(name, variable);
      this.indexToName[variable] = name;
      this.named[variable] = 1;
      this.unassignedNamed += 1;
      // Activity 0 with the default FALSE phase; sift-up ties resolve by
      // index, so the batch keeps its sorted relative order behind every
      // pre-existing candidate.
      this.insertDecisionVariable(variable);
    }
    // Clear any completed-search state so no later slice can replay a stale
    // verdict over the strengthened formula, then cancel to root. Both
    // requeue a partially consumed propagation cursor first, so a pending
    // retained-root scan is rewound onto the queue, never discarded.
    this.finishSearch();
    this.cancelUntil(0);
    // Admit the whole batch against the root assignment: per-clause
    // cancellation would be a no-op here, and skipping it keeps cancellation
    // observers from ever seeing a registered-but-unattached clause.
    for (const clause of delta.clauses) {
      this.admitPermanentClause(clause.lits);
    }
  }

  // The shared production enumeration loop. Public getAllSolutions compiles
  // and constructs ONCE, with PLE disabled. Assumptions were installed once
  // by the constructor and remain at root. ONE call-wide conflict budget
  // spans construction through the terminal search, never reset per model;
  // exhaustion completes the in-flight atomic conflict transaction and then
  // returns the accumulated partial models as 'unknown'.
  enumerateModels(): EnumerateResult {
    const driver = this.enumerateSlices(Number.POSITIVE_INFINITY);
    const result = driver.next();
    if (!result.done) throw new Error('synchronous enumeration cannot pause');
    return result.value;
  }

  // Internal resumable driver; no public generator/streaming API. Yield only
  // after complete search operations or model materialization + blocker
  // admission. Models are pushed into the caller-visible `models` sink as
  // they materialize, so an abandoning async driver keeps the partial
  // prefix; the returned outcome wraps that same array.
  *enumerateSlices(
    workQuantum: number,
    models: VariableAssignments[] = [],
  ): Generator<'paused', EnumerateResult> {
    if (this.enablePle) {
      throw new Error('model enumeration requires enablePle: false');
    }
    this.validateQuantum(workQuantum);
    const budgetOwned = this.openBudgetScope(this.conflictBudget);
    this.enumerationActive = true;
    this.scheduling = { quantum: workQuantum, remaining: workQuantum };
    try {
      while (true) {
        let sat: boolean;
        if (workQuantum === Number.POSITIVE_INFINITY) {
          const verdict = this.search();
          if (verdict === 'unknown') {
            return { status: 'unknown', models, reason: 'conflictBudget' };
          }
          sat = verdict === 'sat';
        } else {
          this.startSearch();
          let result = this.searchSlice(workQuantum);
          while (result === 'paused') {
            yield 'paused';
            result = this.searchSlice(workQuantum);
          }
          if (result === 'unknown') {
            return { status: 'unknown', models, reason: 'conflictBudget' };
          }
          sat = result === 'sat';
          this.finishSearch();
        }
        if (!sat) return { status: 'complete', models };
        models.push(this.model());
        const blocker: number[] = [];
        for (let variable = 0; variable < this.assigns.length; variable += 1) {
          if (this.named[variable] === 1) {
            blocker.push(variable * 2 + (this.assigns[variable] === Value.TRUE ? 1 : 0));
          }
        }
        // Capture the complete named assignment before admission cancels to
        // root. Auxiliaries are never blocked or exposed. Learned consequences
        // of the growing formula (including older blockers) stay sound forever.
        this.addPermanentClause(blocker);
        this.chargeWork();
        if (this.workExhausted()) {
          yield 'paused';
          this.scheduling.remaining = workQuantum;
        }
      }
    } finally {
      this.finishSearch();
      this.cancelUntil(0);
      this.scheduling = null;
      this.enumerationActive = false;
      this.closeBudgetScope(budgetOwned);
    }
  }

  // Pinned two-tier retention (Design § Solver Core, Retention policy): the
  // GLUE tier (LBD <= 2) is NEVER a deletion candidate, so only the REDUCIBLE
  // tier (LBD > 2) is ranked — a stable activity sort, so equal activities
  // keep database/admission order — and its worse floor(n/2) is deleted,
  // skipping reason-locked clauses WITHOUT backfilling from the better half.
  // The permanent originals/blocking clauses are never candidates by role.
  reduceLearnedClauses(): void {
    // Progress the cadence even if every candidate is protected. Testing the
    // live size alone would repeatedly scan/sort on EVERY subsequent conflict.
    this.learnedSinceReduction = 0;
    const reducible = this.clauses.filter((clause) => clause.learned && clause.lbd > 2);
    reducible.sort((left, right) => left.activity - right.activity);
    // Inspect the complete reason array: root and auxiliary implications, and
    // pending assertions, all lock their clauses regardless of watch position.
    const locked = new Set(this.reason);
    const removed = new Set<Clause>();
    for (let index = 0; index < Math.floor(reducible.length / 2); index += 1) {
      const clause = reducible[index];
      if (!locked.has(clause)) {
        removed.add(clause);
      }
    }
    // Relative decay fires after EVERY round, including protected-only or
    // empty ones: the growing increment makes post-round bumps outweigh equal
    // pre-round bumps. This lifetime aging is independent of the resettable
    // output stats, so per-call measurement scopes are unaffected.
    this.claInc *= 1 / 0.999;
    if (removed.size === 0) {
      return;
    }

    let retained = 0;
    for (const clause of this.clauses) {
      if (removed.has(clause)) {
        this.detachClause(clause);
        // Watches permute literals. Delete the semantic key using a sorted
        // COPY, never by changing a live clause's watched positions.
        this.clauseByKey.delete([...clause.lits].sort((a, b) => a - b).join(','));
      } else {
        // Compact in place; neither survivor objects nor the database array
        // are replaced. Reasons, phases, root facts and VSIDS stay untouched.
        this.clauses[retained++] = clause;
      }
    }
    this.clauses.length = retained;
    this.stats.learnedClausesCurrent -= removed.size;
    // learnedClauses is total admissions and must NEVER decrease on deletion.
  }

  newDecisionLevel(): void {
    this.trailLim.push(this.trail.length);
  }

  cancelUntil(targetLevel: number): void {
    if (!Number.isInteger(targetLevel) || targetLevel < 0) {
      throw new Error('target decision level must be a non-negative integer');
    }
    this.requeuePropagation();
    if (this.trailLim.length <= targetLevel) {
      return;
    }

    const cutoff = this.trailLim[targetLevel];
    if (cutoff === undefined) {
      throw new Error(`missing trail boundary for decision level ${targetLevel + 1}`);
    }
    for (let index = this.trail.length - 1; index >= cutoff; index -= 1) {
      const variable = varOf(this.trail[index]);
      this.assigns[variable] = Value.UNSET;
      this.level[variable] = 0;
      this.reason[variable] = null;
      this.rootBasis[variable] = 0;
      if (this.named[variable] === 1) {
        this.unassignedNamed += 1;
        this.insertDecisionVariable(variable);
      }
    }
    this.trail.length = cutoff;
    this.trailLim.length = targetLevel;
    // Backtrack-safe by construction (the scheme's main payoff): watch lists
    // are left untouched — a clause is only examined when one of its
    // watched literals becomes false, and every dequeue after this point
    // re-examines exactly the clauses whose watched literal (re-)becomes
    // false. qhead is clamped to the truncated trail: entries below the
    // cutoff that were never propagated before the backtracking are still
    // pending and must be drained on the next propagate() call, while
    // entries above the cutoff are gone (their watches need no bookkeeping
    // because they were only examined at their previous dequeue).
    this.qhead = Math.min(this.qhead, cutoff);
    this.assertTrailInvariant();
  }

  // Incremental call boundary. Keep the core's lifetime ledger separate from
  // caller-owned per-call outputs:
  // resetting an output must not reset the live database or reduction cadence.
  // The ordinary search()/model() lifecycle remains available for
  // enumeration. Returns the rich verdict: a detached named model on SAT, the
  // failed-assumption core (extracted at verdict time, before the finally
  // cleanup cancels the prefix) on UNSAT, or 'unknown' when this call's
  // conflict budget is spent — never a throw.
  solveAssuming(
    assumptions?: VariableAssignments,
    stats?: SolverStatsInput,
    conflictBudget?: number | undefined,
  ): SolveResult {
    if (this.incrementalCallActive) {
      // A nested call must NOT cancel the outer call's active assumption prefix.
      throw new Error('incremental solve cannot be reentered');
    }
    if (stats === this.stats) {
      throw new Error('incremental output stats must be separate from the lifetime ledger');
    }
    this.incrementalCallActive = true;
    const before = { ...this.stats };
    let reportStats = false;
    try {
      if (stats !== undefined) {
        Object.assign(stats, createSolverStats());
        reportStats = true;
      }
      if (this.enablePle) {
        throw new Error('incremental solving requires enablePle: false');
      }
      // Budget validation precedes assumption validation and any cached-UNSAT
      // short-circuit (Design § Validation order).
      validateConflictBudget(conflictBudget);
      // Complete validation before touching the call's trail, even if search()
      // will short-circuit permanent UNSAT. Values/order are read exactly once.
      const ordered = this.translateAssumptions(assumptions);
      const budgetOwned = this.openBudgetScope(conflictBudget);
      let verdict: SearchVerdict;
      try {
        verdict = this.search(ordered);
      } finally {
        this.closeBudgetScope(budgetOwned);
      }
      if (verdict === 'sat') {
        return { status: 'sat', model: this.model() };
      }
      if (verdict === 'unknown') {
        return { status: 'unknown', reason: 'conflictBudget' };
      }
      const core = this.extractedCore;
      if (core === null) {
        throw new Error('UNSAT verdict without an extracted core');
      }
      return { status: 'unsat', core };
    } finally {
      // The model (if any) was already materialized by the try above; this
      // cleanup also runs on validation or hook errors. Publish per-call
      // stats only after root cleanup, so an early exit cannot leave the
      // caller's output half-filled.
      try {
        this.cancelUntil(0);
        if (stats !== undefined && reportStats) {
          Object.assign(stats, {
            decisions: this.stats.decisions - before.decisions,
            propagations: this.stats.propagations - before.propagations,
            conflicts: this.stats.conflicts - before.conflicts,
            restarts: this.stats.restarts - before.restarts,
            learnedClauses: this.stats.learnedClauses - before.learnedClauses,
            learnedClausesCurrent: this.stats.learnedClausesCurrent,
            learnedLiterals: this.stats.learnedLiterals - before.learnedLiterals,
            minimizedLiterals: this.stats.minimizedLiterals - before.minimizedLiterals,
          });
        }
      } finally {
        this.incrementalCallActive = false;
      }
    }
  }

  // The tri-state core driver behind every public entry point: 'unknown'
  // reports THIS call's spent conflict budget (never a throw), and identical
  // histories produce identical verdicts whether the slices ran to
  // completion synchronously or were interleaved with scheduler yields.
  search(assumptions: readonly number[] = []): SearchVerdict {
    const budgetOwned = this.openBudgetScope(this.conflictBudget);
    this.startSearch(assumptions);
    try {
      const result = this.searchSlice(Number.POSITIVE_INFINITY);
      if (result === 'paused') throw new Error('synchronous search cannot pause');
      return result;
    } finally {
      this.finishSearch();
      this.closeBudgetScope(budgetOwned);
    }
  }

  // Unbudgeted convenience wrapper over search(): with no conflict budget in
  // scope, exhaustion is unreachable, so an 'unknown' here means a budget was
  // in scope for a boolean-shaped caller — an internal usage error, mirroring
  // propagate()'s pause guard.
  solve(assumptions: readonly number[] = []): boolean {
    const verdict = this.search(assumptions);
    if (verdict === 'unknown') {
      throw new Error('boolean solve() cannot report budget exhaustion: use search()');
    }
    return verdict === 'sat';
  }

  // An UNSAT verdict established without any search work in this call: a
  // cached permanent UNSAT, a compiled empty clause, or a
  // constructor-detected root contradiction. Pre-aborted async calls consult
  // ONLY this after validation — no propagation, no preprocessing (Design §
  // Validation order). The extraction mirrors the searchSlice short-circuit.
  private establishedRootVerdict(): 'unsat' | null {
    if (this.permanentUnsat || this.cnf.levelZeroUnsat || this.startupConflict !== null) {
      this.permanentUnsat = true;
      this.extractedCore = this.extractRootCore(this.startupConflict);
      return 'unsat';
    }
    return null;
  }

  // Sliced driving shared by the async entry points: run searchSlice until a
  // verdict, yielding through the platform-neutral scheduler between slices.
  // Outcome precedence at every checkpoint (Design § Budget contract):
  // established verdict first, then abort, then budget. Scheduler failures
  // reject; the caller's finally cleanup preserves pending retained-root
  // propagation and releases the busy guard.
  private async driveSlicesAsync(
    signal: AbortSignal | undefined,
    yieldQuantum: number,
  ): Promise<AsyncVerdict> {
    const scheduler = resolveYieldScheduler();
    for (;;) {
      const result = this.searchSlice(yieldQuantum);
      if (result === 'sat' || result === 'unsat') {
        return { status: result };
      }
      if (signalAborted(signal)) {
        return { status: 'unknown', reason: 'aborted' };
      }
      if (result === 'unknown') {
        return { status: 'unknown', reason: 'conflictBudget' };
      }
      await scheduler();
      if (signalAborted(signal)) {
        return { status: 'unknown', reason: 'aborted' };
      }
    }
  }

  // Internal async analog of search() for the single-shot public wrapper:
  // construction (and hence option/assumption validation) already happened
  // synchronously in the async wrapper, so invalid inputs reject the Promise
  // before the first yield. A pre-aborted signal consults only
  // already-established verdicts — no propagation or preprocessing.
  async solveAsync(
    assumptions: readonly number[],
    signal: AbortSignal | undefined,
    yieldQuantum: number,
  ): Promise<AsyncVerdict> {
    if (signalAborted(signal)) {
      return this.establishedRootVerdict() === 'unsat'
        ? { status: 'unsat' }
        : { status: 'unknown', reason: 'aborted' };
    }
    const budgetOwned = this.openBudgetScope(this.conflictBudget);
    this.startSearch(assumptions);
    try {
      return await this.driveSlicesAsync(signal, yieldQuantum);
    } finally {
      this.finishSearch();
      this.closeBudgetScope(budgetOwned);
    }
  }

  // The async incremental call boundary, mirroring solveAssuming: the busy
  // guard and stats zeroing run synchronously at call time (async functions
  // execute their body up to the first await), so a reentrant async call
  // rejects without touching the in-flight call's stats or state, and every
  // validation error rejects the returned Promise. All exits — verdict,
  // unknown, abort, hook or scheduler failure — run the same cleanup as the
  // sync path and leave the handle reusable.
  async solveAssumingAsync(
    assumptions?: VariableAssignments,
    stats?: SolverStatsInput,
    conflictBudget?: number | undefined,
    signal?: AbortSignal | undefined,
    yieldQuantum?: number | undefined,
  ): Promise<SolveResult> {
    if (this.incrementalCallActive) {
      // A nested call must NOT cancel the outer call's active assumption prefix.
      throw new Error('incremental solve cannot be reentered');
    }
    if (stats === this.stats) {
      throw new Error('incremental output stats must be separate from the lifetime ledger');
    }
    this.incrementalCallActive = true;
    const before = { ...this.stats };
    let reportStats = false;
    try {
      if (stats !== undefined) {
        Object.assign(stats, createSolverStats());
        reportStats = true;
      }
      if (this.enablePle) {
        throw new Error('incremental solving requires enablePle: false');
      }
      // Option validation precedes assumption validation and any cached-UNSAT
      // short-circuit (Design § Validation order).
      validateConflictBudget(conflictBudget);
      const quantum = normalizeYieldQuantum(yieldQuantum);
      // Complete validation before touching the call's trail. Values/order
      // are read exactly once.
      const ordered = this.translateAssumptions(assumptions);
      if (signalAborted(signal)) {
        // Pre-aborted: validate (above) and consult established verdicts
        // only — no propagation, no preprocessing, no prefix replay.
        if (this.establishedRootVerdict() === 'unsat') {
          const core = this.extractedCore;
          if (core === null) {
            throw new Error('UNSAT verdict without an extracted core');
          }
          return { status: 'unsat', core };
        }
        return { status: 'unknown', reason: 'aborted' };
      }
      const budgetOwned = this.openBudgetScope(conflictBudget);
      this.startSearch(ordered);
      let verdict: AsyncVerdict;
      try {
        verdict = await this.driveSlicesAsync(signal, quantum);
      } finally {
        this.finishSearch();
        this.closeBudgetScope(budgetOwned);
      }
      if (verdict.status === 'sat') {
        return { status: 'sat', model: this.model() };
      }
      if (verdict.status === 'unknown') {
        return { status: 'unknown', reason: verdict.reason };
      }
      const core = this.extractedCore;
      if (core === null) {
        throw new Error('UNSAT verdict without an extracted core');
      }
      return { status: 'unsat', core };
    } finally {
      // The model (if any) was already materialized above; this cleanup also
      // runs on validation, hook, or scheduler errors. Publish per-call stats
      // only after root cleanup, so an early exit cannot leave the caller's
      // output half-filled.
      try {
        this.cancelUntil(0);
        if (stats !== undefined && reportStats) {
          Object.assign(stats, {
            decisions: this.stats.decisions - before.decisions,
            propagations: this.stats.propagations - before.propagations,
            conflicts: this.stats.conflicts - before.conflicts,
            restarts: this.stats.restarts - before.restarts,
            learnedClauses: this.stats.learnedClauses - before.learnedClauses,
            learnedClausesCurrent: this.stats.learnedClausesCurrent,
            learnedLiterals: this.stats.learnedLiterals - before.learnedLiterals,
            minimizedLiterals: this.stats.minimizedLiterals - before.minimizedLiterals,
          });
        }
      } finally {
        this.incrementalCallActive = false;
      }
    }
  }

  // The async enumeration driver: enumerateSlices supplies the partial-model
  // sink, and abort between slices abandons the generator deterministically
  // (its finally preserves pending retained-root propagation and releases the
  // enumeration scope), returning the accumulated prefix as 'unknown'.
  // Scheduler and hook failures reject after the same cleanup.
  async enumerateModelsAsync(
    signal: AbortSignal | undefined,
    yieldQuantum: number,
  ): Promise<EnumerateResult> {
    if (this.enablePle) {
      throw new Error('model enumeration requires enablePle: false');
    }
    if (signalAborted(signal)) {
      // Pre-aborted: consult established verdicts only. An established UNSAT
      // means the model set is complete and empty.
      return this.establishedRootVerdict() === 'unsat'
        ? { status: 'complete', models: [] }
        : { status: 'unknown', models: [], reason: 'aborted' };
    }
    const scheduler = resolveYieldScheduler();
    const models: VariableAssignments[] = [];
    const driver = this.enumerateSlices(yieldQuantum, models);
    let completed = false;
    try {
      let step = driver.next();
      while (!step.done) {
        // Abort outranks a budget outcome but never an established verdict;
        // the generator only yields 'paused', so verdicts/budgets arrive with
        // done: true and bypass this check.
        if (signalAborted(signal)) {
          return { status: 'unknown', models, reason: 'aborted' };
        }
        await scheduler();
        if (signalAborted(signal)) {
          return { status: 'unknown', models, reason: 'aborted' };
        }
        step = driver.next();
      }
      completed = true;
      // A budget-exhausted outcome arriving exactly when the signal has
      // fired reports 'aborted': verdict first, then abort, then budget.
      if (step.value.status === 'unknown' && signalAborted(signal)) {
        return { status: 'unknown', models, reason: 'aborted' };
      }
      return step.value;
    } finally {
      if (!completed) {
        // Abandoned mid-yield (abort, scheduler rejection): run the
        // generator's finally deterministically rather than waiting for GC.
        driver.return({ status: 'unknown', models, reason: 'aborted' });
      }
    }
  }

  // Internal lifecycle seam for finite-slice drivers. Restart epoch state is
  // fresh per search (EMA histories are lifetime state and deliberately do
  // not reset). An enumeration driver owns scheduling across model searches;
  // standalone finite searches own their allowance until finishSearch().
  startSearch(assumptions: readonly number[] = []): void {
    this.finishSearch();
    this.restartPolicy.resetSearch();
    this.extractedCore = null;
    this.searchState = {
      assumptions: [...assumptions],
      phase: 'startup',
      verdict: null,
    };
  }

  finishSearch(): void {
    this.requeuePropagation();
    this.searchState = null;
    if (!this.enumerationActive) this.scheduling = null;
  }

  private requeuePropagation(): void {
    if (this.propagationCursor !== null) {
      this.qhead = Math.min(this.qhead, this.propagationCursor.event);
      this.propagationCursor = null;
    }
  }

  private chargeWork(): void {
    if (this.scheduling !== null) this.scheduling.remaining -= 1;
  }

  private workExhausted(): boolean {
    return this.scheduling !== null && this.scheduling.remaining <= 0;
  }

  private validateQuantum(workQuantum: number): void {
    if (
      workQuantum !== Number.POSITIVE_INFINITY &&
      (!Number.isSafeInteger(workQuantum) || workQuantum < 1)
    ) {
      throw new Error('work quantum must be a positive safe integer or Infinity');
    }
  }

  searchSlice(workQuantum: number): SearchResult {
    this.validateQuantum(workQuantum);
    if (this.searchState === null) this.startSearch();
    if (this.scheduling?.quantum !== workQuantum || this.workExhausted()) {
      this.scheduling = { quantum: workQuantum, remaining: workQuantum };
    }
    const state = this.searchState as SearchState;
    if (state.verdict !== null) return state.verdict;
    // Only base-formula conflicts are permanent UNSAT: an empty clause, or a
    // conflict found by root-level propagation, means the formula has no
    // model. A falsified per-call assumption (below) is context-local and
    // must never poison permanentUnsat.
    if (this.permanentUnsat || this.cnf.levelZeroUnsat) {
      this.permanentUnsat = true;
      // A cached/compiled UNSAT: the recorded startup conflict (an empty
      // clause, a unit contradiction, or a rejected assumption's explaining
      // clause) still supports the walk; with no assumption leaves or seed
      // it yields {}, the assumption-independent core.
      this.extractedCore = this.extractRootCore(this.startupConflict);
      return (state.verdict = 'unsat');
    }

    if (state.phase === 'startup') {
      const budget = this.budget;
      if (budget !== null && this.budgetExhausted()) {
        // The explicit budget-zero startup exception (Design § Target Public
        // API, Budget contract): ONE initial level-0 propagation pass per
        // call, so cached/compiled UNSAT, an initial root conflict, or an
        // already-complete model can still return a verdict. Without it the
        // exhausted budget returns 'unknown' immediately — no propagation,
        // no PLE, no search decision. The allowance never re-arms after
        // learning or between enumeration models.
        if (budget.startupAllowance === 'spent') {
          return 'unknown';
        }
        // 'fresh' arms the pass; 'active' means a paused pass is resuming.
        budget.startupAllowance = 'active';
        const initial =
          workQuantum === Number.POSITIVE_INFINITY ? this.propagate() : this.propagateSlice(true);
        if (initial === 'paused') return 'paused';
        budget.startupAllowance = 'spent';
        if (initial !== null) {
          // A terminal root conflict establishes UNSAT without analysis and
          // takes precedence over the spent budget.
          this.permanentUnsat = true;
          this.extractedCore = this.extractRootCore(initial);
          return (state.verdict = 'unsat');
        }
        // The propagation fixpoint completed. An already-complete model (no
        // pending assumption replay — SAT requires both) is established;
        // anything else would need PLE or a search step the budget forbids.
        if (state.assumptions.length === 0 && this.namedVariablesAssigned()) {
          return (state.verdict = 'sat');
        }
        return 'unknown';
      }
      const initial =
        workQuantum === Number.POSITIVE_INFINITY ? this.propagate() : this.propagateSlice(true);
      if (initial === 'paused') return 'paused';
      if (initial !== null) {
        this.permanentUnsat = true;
        this.extractedCore = this.extractRootCore(initial);
        return (state.verdict = 'unsat');
      }
      if (this.enablePle && !this.eliminatePureLiterals()) {
        this.permanentUnsat = true;
        this.extractedCore = this.extractRootCore(this.pleConflict);
        return (state.verdict = 'unsat');
      }
      state.phase = 'search';
    }

    // Iterative CDCL (Design § Solver Core End-State). A conflict learns
    // an asserting first-UIP clause and backjumps to its assertion level,
    // instead of undoing the last decision and re-exploring. Aux variables
    // are never branched on; SAT requires every named variable to be assigned.
    // Restart timing is the extracted policy unit's decision from per-conflict
    // samples; its epoch state is per search, never shared stats. Ordinary
    // backjumps do NOT reset the epoch.
    while (true) {
      if (this.workExhausted()) return 'paused';
      // Positive budgets are HARD conflict limits: after the final atomic
      // conflict transaction, do not start another propagation pass, prefix
      // step, or decision merely to seek a verdict. Only an already
      // established verdict outranks the budget, and those returned above.
      if (this.budgetExhausted()) return 'unknown';
      const conflict =
        state.phase === 'prefix'
          ? null
          : workQuantum === Number.POSITIVE_INFINITY
            ? this.propagate()
            : this.propagateSlice(true);
      if (conflict === 'paused') return 'paused';
      if (conflict !== null) {
        if (this.trailLim.length === 0) {
          this.permanentUnsat = true;
          // A terminal root conflict, extracted BEFORE learning/cancellation
          // would touch the trail: every literal is root-assigned.
          this.extractedCore = this.extractRootCore(conflict);
          return (state.verdict = 'unsat');
        }
        const { learned, backjumpLevel } = this.analyze(conflict);
        const assertingLit = learned.lits[0];
        const registered = this.addLearnedClause(learned);
        this.cancelUntil(backjumpLevel);
        if (
          this.assigns[varOf(assertingLit)] !== Value.UNSET ||
          !this.enqueue(assertingLit, registered)
        ) {
          throw new Error(
            'learned clause must assert a newly unassigned literal after backjumping',
          );
        }
        this.stats.propagations += 1;
        // The policy observes this conflict's learned LBD and the trail as it
        // stands AFTER the transaction (assertion enqueued) and BEFORE any
        // restart cancellation — never the emptied post-cancel trail.
        const verdict = this.restartPolicy.onConflict({
          lbd: learned.lbd,
          trailLength: this.trail.length,
          atRoot: this.trailLim.length === 0,
        });
        if (verdict.kind === 'restart') {
          // Finish learning/asserting BEFORE restarting, but do not propagate
          // the assertion first: that could exceed this epoch's conflict
          // budget. A root assertion stays queued (including unwatched units);
          // a conditional assertion above root is undone, never promoted.
          this.cancelUntil(0);
          if (verdict.actual) {
            this.stats.restarts += 1;
          }
          // A consumed epoch whose backjump already reached root is a no-op
          // cancellation, never an additional restart.
        }
        // Do not reduce at registration: the learned clause must first become
        // the assertion's reason. After an optional restart, only reasons that
        // are still active are locked. This does not drain pending propagation.
        if (this.learnedSinceReduction >= this.learnedClauseReductionThreshold) {
          this.reduceLearnedClauses();
        }
        this.chargeWork();
      } else {
        // MiniSat assumption prefix (Design § Solver Core End-State). The
        // CURRENT level is the cursor, so backjumps and restarts replay
        // anything they popped automatically. Already-true assumptions still
        // consume dummy levels.
        // A false assumption is call-local UNSAT, even if falsified at root;
        // it is NOT a base conflict and must never poison permanentUnsat.
        let assumptionEnqueued = false;
        state.phase = 'prefix';
        while (this.trailLim.length < state.assumptions.length) {
          if (this.workExhausted()) return 'paused';
          const lit = state.assumptions[this.trailLim.length];
          const value = litValue(lit, this.assigns);
          this.chargeWork();
          if (value === Value.FALSE) {
            // analyzeFinal over the prefix, seeded with the rejected
            // assumption itself, BEFORE the finally cleanup cancels it.
            this.extractedCore = this.extractPrefixCore(lit, state.assumptions);
            return (state.verdict = 'unsat');
          }
          this.newDecisionLevel();
          if (value === Value.UNSET) {
            this.enqueue(lit, null);
            assumptionEnqueued = true;
            break;
          }
        }
        if (assumptionEnqueued) {
          state.phase = 'search';
          // Propagate this assumption before advancing the prefix, including
          // after the last assumption. Assumptions are not heuristic decisions
          // or propagations; their resulting implications ARE propagations.
          continue;
        }
        // Pending assumptions must be checked even on an already-total root
        // model, not just when the heuristic would otherwise need a decision.
        if (this.namedVariablesAssigned()) {
          return (state.verdict = 'sat');
        }
        if (this.workExhausted()) return 'paused';
        const [variable, preferTrue] = this.pickDecision();
        const lit = variable * 2 + (preferTrue ? 0 : 1);
        this.newDecisionLevel();
        this.enqueue(lit, null);
        this.stats.decisions += 1;
        this.chargeWork();
        state.phase = 'search';
      }
    }
  }

  // The model projects over every KNOWN named variable — construction names
  // plus every admitted add() batch, wherever their indices landed.
  model(): VariableAssignments {
    const entries: Array<[Variable, Value]> = [];
    for (let index = 0; index < this.assigns.length; index += 1) {
      if (this.named[index] !== 1) {
        continue;
      }
      const value = this.assigns[index];
      if (value === Value.UNSET) {
        throw new Error('cannot build a model before every named variable is assigned');
      }
      const name = this.indexToName[index];
      if (name === undefined) {
        throw new Error(`missing name for variable index ${index}`);
      }
      entries.push([name, value]);
    }
    return Object.fromEntries(entries);
  }

  // The globally sorted named universe known so far: construction names plus
  // every admitted add() batch. Index assignment is history-dependent (new
  // names are appended after existing indices, sorted within their batch), so
  // this sorted presentation is the only stable cross-history view.
  variables(): Variable[] {
    return [...this.nameToIndex.keys()].sort();
  }

  // The failed-assumption core extracted at the most recent UNSAT verdict
  // (extraction runs at verdict time, BEFORE any cleanup cancellation), or
  // null when the latest search was not UNSAT / no search has run. Internal
  // seam for the public wrappers; the returned record is already detached
  // from solver state. A null read after an UNSAT verdict is a bug: the
  // sound fallback for missing provenance is the full validated assumption
  // set, never an unsupported empty core (Design § UNSAT Cores).
  unsatCore(): VariableAssignments | null {
    return this.extractedCore;
  }

  private coreNameOf(variable: number): Variable {
    const name = this.indexToName[variable];
    if (name === undefined) {
      throw new Error(`missing name for variable index ${variable}`);
    }
    return name;
  }

  // The entire validated constructor-assumption set as a core. This is the
  // sound PLE-leaf widening: a pin was computed under the FULL assumption
  // context, so purity under a subset is not guaranteed; and it is the
  // documented fallback whenever finer provenance is unavailable.
  private fullAssumptionCore(): VariableAssignments {
    return Object.fromEntries(
      this.constructorAssumptions.map((lit) => [
        this.coreNameOf(varOf(lit)),
        isNeg(lit) ? Value.FALSE : Value.TRUE,
      ]),
    );
  }

  // Single-shot root walk (Design § UNSAT Cores): assumptions and PLE pins
  // sit at level 0, so resolve the root reason graph from the falsified
  // conflict — ALWAYS through a non-null reason, regardless of its taint
  // mask (a tainted implication is an implication, never a collectable
  // leaf). Only a reason-null leaf recorded as an actual call assumption
  // enters the core; an actual reason-null PLE leaf widens the core to the
  // entire validated assumption set. The recorded rejected-assumption
  // literal seeds the core even though it never entered the trail.
  private extractRootCore(conflict: Clause | null): VariableAssignments {
    const core = new Map<Variable, Value>();
    const seed = this.startupRejectedAssumption;
    if (seed !== null) {
      core.set(this.coreNameOf(varOf(seed)), isNeg(seed) ? Value.FALSE : Value.TRUE);
    }
    if (conflict !== null) {
      const visited = new Uint8Array(this.assigns.length);
      const stack: number[] = [];
      for (const lit of conflict.lits) {
        stack.push(varOf(lit));
      }
      let current = stack.pop();
      while (current !== undefined) {
        if (visited[current] === 0) {
          visited[current] = 1;
          const reason = this.reason[current];
          if (reason !== null) {
            for (const lit of reason.lits) {
              const antecedent = varOf(lit);
              if (antecedent !== current && visited[antecedent] === 0) {
                stack.push(antecedent);
              }
            }
          } else if ((this.rootBasis[current] & ROOT_BASIS_PLE) !== 0) {
            return this.fullAssumptionCore();
          } else if ((this.rootBasis[current] & ROOT_BASIS_ASSUMPTION) !== 0) {
            const value = this.assigns[current];
            if (value !== Value.TRUE && value !== Value.FALSE) {
              throw new Error('core extraction reached an unassigned assumption leaf');
            }
            if (
              debugAssertions &&
              !this.constructorAssumptions.includes(current * 2 + (value === Value.FALSE ? 1 : 0))
            ) {
              throw new Error('root core collected a leaf that is not a call assumption');
            }
            core.set(this.coreNameOf(current), value);
          }
          // Anything else would be a base-derived reason-null root fact,
          // which this solver never creates; it contributes nothing
          // assumption-dependent either way.
        }
        current = stack.pop();
      }
    }
    return Object.fromEntries(core);
  }

  // Incremental analyzeFinal (Design § UNSAT Cores): assumptions occupy
  // prefix levels 1..k, so walk the trail backwards from the final prefix
  // conflict, resolving through reasons; every reason-null literal above
  // root is an assumption (ordinary decisions are cancelled before prefix
  // replay, so none can appear here). The falsified assumption itself seeds
  // the core even though it never entered the trail: the walk starts from
  // the reasons explaining its opposite. Sound because incremental learned
  // clauses are unconditional base consequences.
  private extractPrefixCore(
    failedLit: number,
    assumptions: readonly number[],
  ): VariableAssignments {
    const core = new Map<Variable, Value>([
      [this.coreNameOf(varOf(failedLit)), isNeg(failedLit) ? Value.FALSE : Value.TRUE],
    ]);
    const marked = new Uint8Array(this.assigns.length);
    marked[varOf(failedLit)] = 1;
    const rootBoundary = this.trailLim[0] ?? this.trail.length;
    for (let index = this.trail.length - 1; index >= rootBoundary; index -= 1) {
      const lit = this.trail[index];
      const variable = varOf(lit);
      if (marked[variable] === 0) {
        continue;
      }
      marked[variable] = 0;
      const reason = this.reason[variable];
      if (reason === null) {
        if (debugAssertions && !assumptions.includes(lit)) {
          throw new Error('prefix core collected a leaf that is not a call assumption');
        }
        core.set(this.coreNameOf(variable), isNeg(lit) ? Value.FALSE : Value.TRUE);
      } else {
        for (const antecedent of reason.lits) {
          const other = varOf(antecedent);
          // Root antecedents are base-derived facts (incremental mode has no
          // root assumptions or PLE pins); only levels above root can hold
          // assumption dependencies.
          if (other !== variable && this.level[other] > 0) {
            marked[other] = 1;
          }
        }
      }
    }
    return Object.fromEntries(core);
  }

  // The sorted canonical contents determine deterministic ties. The asserting
  // literal occupies slot 0, and a maximum-other-level literal occupies slot
  // 1, so undoing the assertion level later leaves two non-false watches.
  private orderAssertingLits(normalized: number[], assertingLit: number): number[] {
    const lits = [assertingLit, ...normalized.filter((lit) => lit !== assertingLit)];
    if (lits.length >= 2) {
      let otherWatch = 1;
      for (let index = 2; index < lits.length; index += 1) {
        if (this.level[varOf(lits[index])] > this.level[varOf(lits[otherWatch])]) {
          otherWatch = index;
        }
      }
      [lits[1], lits[otherWatch]] = [lits[otherWatch], lits[1]];
    }
    return lits;
  }

  private attachClause(clause: Clause): void {
    if (clause.lits.length < 2) {
      return;
    }
    const first = clause.lits[0];
    const second = clause.lits[1];
    if (clause.lits.length === 2) {
      // Binary clauses live on the dedicated lists (implicit propagation);
      // their watches never relocate, so no blocker/twin tracking is needed.
      const firstList = this.binaryWatches[first];
      const secondList = this.binaryWatches[second];
      if (firstList === undefined || secondList === undefined) {
        throw new Error(`clause contains out-of-range watched literal: ${first}, ${second}`);
      }
      firstList.push({ clause, other: second });
      secondList.push({ clause, other: first });
      return;
    }
    const firstWatchList = this.watches[first];
    const secondWatchList = this.watches[second];
    if (firstWatchList === undefined || secondWatchList === undefined) {
      throw new Error(`clause contains out-of-range watched literal: ${first}, ${second}`);
    }
    // Cross-linked twin entries: from each list the blocker is the OTHER
    // watched literal, so either list can later keep this one's blocker in
    // step when its own watch relocates (O(1), no list scan).
    const entry: WatchEntry = { clause, blocker: second, twin: null };
    const twin: WatchEntry = { clause, blocker: first, twin: entry };
    entry.twin = twin;
    firstWatchList.push(entry);
    secondWatchList.push(twin);
  }

  private detachClause(clause: Clause): void {
    if (clause.lits.length < 2) {
      return;
    }
    for (let slot = 0; slot < 2; slot += 1) {
      const lit = clause.lits[slot];
      if (clause.lits.length === 2) {
        const binaryList = this.binaryWatches[lit];
        const binaryIndex = binaryList?.findIndex((entry) => entry.clause === clause) ?? -1;
        if (binaryList === undefined || binaryIndex < 0) {
          throw new Error(`clause is missing its watch on literal: ${lit}`);
        }
        binaryList[binaryIndex] = binaryList[binaryList.length - 1];
        binaryList.pop();
        continue;
      }
      const list = this.watches[lit];
      const index = list?.findIndex((entry) => entry.clause === clause) ?? -1;
      if (list === undefined || index < 0) {
        throw new Error(`clause is missing its watch on literal: ${lit}`);
      }
      list[index] = list[list.length - 1];
      list.pop();
    }
  }

  // `Value.UNSET` entries translate to nothing: they mean "no assumption for
  // this variable", per the uniform validation contract in index.ts. The
  // GROWABLE symbol table resolves names, so an assumption that was unknown
  // at construction becomes valid once an add() batch introduces it.
  private translateAssumptions(assumptions: VariableAssignments | undefined): number[] {
    if (assumptions === undefined) {
      return [];
    }

    const translated: number[] = [];
    for (const [name, value] of Object.entries(assumptions)) {
      const variable = this.nameToIndex.get(name);
      if (variable === undefined) {
        throw new Error(`unknown assumption variable: ${JSON.stringify(name)}`);
      }
      if (value !== Value.UNSET && value !== Value.FALSE && value !== Value.TRUE) {
        throw new Error(`invalid assumption value for ${JSON.stringify(name)}: ${String(value)}`);
      }
      if (value !== Value.UNSET) {
        translated.push(variable * 2 + (value === Value.FALSE ? 1 : 0));
      }
    }
    return translated;
  }

  // Constructor-only assumptions are constant for this instance (single-shot
  // solving / enumeration), unlike solveAssuming's retractable level prefix.
  // An assumption that contradicts an existing assignment blames that
  // assignment's explaining clause as the startup conflict, so propagate()
  // reports it exactly once. Assumption-assigned variables have no reason
  // clause, and assumptions map one literal per name so they cannot
  // contradict each other — a null reason here is a genuine invariant breach.
  // A newly enqueued root assumption seeds its assumption-taint bit; an
  // already-derived assignment keeps its existing (possibly base) basis.
  // A REJECTED assumption is also recorded as the core seed (Design § UNSAT
  // Cores): the explaining clause alone is satisfied by the existing
  // assignment and walking it would yield a bogus empty core.
  private enqueueAssumptions(assumptions: readonly number[]): void {
    for (const lit of assumptions) {
      const variable = varOf(lit);
      const wasUnset = this.assigns[variable] === Value.UNSET;
      if (!this.enqueue(lit, null)) {
        this.startupRejectedAssumption ??= lit;
        this.startupConflict ??= this.reason[variable];
        if (this.startupConflict === null) {
          throw new Error('contradictory assumptions without an explaining clause');
        }
      } else if (wasUnset) {
        this.rootBasis[variable] |= ROOT_BASIS_ASSUMPTION;
      }
    }
  }

  // Pure-literal elimination, enabled only for the single-shot
  // getSolution/getSolutionAsync entry points (Design § Design Principles
  // and Hard Constraints): a variable occurring in exactly one polarity
  // among the still-unsatisfied clauses can be pinned to
  // the other polarity without affecting satisfiability. Pins are enqueued at
  // root, which is why this mode stays off for enumeration and incremental
  // solving. Bitmask: bit 1 = positive occurrence, bit 2 = negative
  // occurrence; a value of exactly 1 or 2 marks a pure variable. Each scan
  // assigns ALL such variables in ascending index order, then propagates;
  // because a pin can newly satisfy clauses (making further variables pure),
  // the sweep repeats until a round assigns nothing.
  private eliminatePureLiterals(): boolean {
    while (true) {
      const polarities = new Uint8Array(this.assigns.length);

      for (const clause of this.clauses) {
        let satisfied = false;
        for (const lit of clause.lits) {
          if (litValue(lit, this.assigns) === Value.TRUE) {
            satisfied = true;
            break;
          }
        }
        if (satisfied) {
          continue;
        }
        for (const lit of clause.lits) {
          if (litValue(lit, this.assigns) === Value.UNSET) {
            polarities[varOf(lit)] |= isNeg(lit) ? 2 : 1;
          }
        }
      }

      let assignedPureLiteral = false;
      for (let variable = 0; variable < polarities.length; variable += 1) {
        const polarity = polarities[variable];
        if (polarity !== 1 && polarity !== 2) {
          continue;
        }
        const lit = variable * 2 + (polarity === 2 ? 1 : 0);
        if (!this.enqueue(lit, null)) {
          throw new Error(`pure-literal enqueue contradicted variable ${variable}`);
        }
        // A PLE pin satisfies every still-unsatisfied occurrence of the
        // variable, so its taint can never enter an implication antecedent;
        // the bit marks the reason-null leaf itself.
        this.rootBasis[variable] |= ROOT_BASIS_PLE;
        this.stats.propagations += 1;
        assignedPureLiteral = true;
      }

      if (!assignedPureLiteral) {
        return true;
      }
      const conflict = this.propagate();
      if (conflict !== null) {
        // Retain the falsified clause for UNSAT-core extraction: the verdict
        // is declared in searchSlice, after this method returns.
        this.pleConflict ??= conflict;
        return false;
      }
    }
  }

  private namedVariablesAssigned(): boolean {
    return this.unassignedNamed === 0;
  }

  // Select the next decision: the `variablePriority` hook first (named,
  // unassigned, defensively revalidated), else VSIDS with the saved phase.
  // Ties break by index and the default phase is FALSE, so branching is
  // deterministic. Aux variables are never decided (Design § Design
  // Principles and Hard Constraints: named-only termination).
  private pickDecision(): [number, boolean] {
    if (this.variablePriority !== undefined) {
      // Hook inputs cover the CURRENT named universe, including variables
      // introduced by add() batches: the named flag — never an index bound —
      // decides membership, so appended variables get heuristic guidance.
      const unassigned: Variable[] = [];
      const currentAssignments: Partial<Record<Variable, Value>> = {};
      for (let variable = 0; variable < this.assigns.length; variable += 1) {
        if (this.named[variable] !== 1) {
          continue;
        }
        const name = this.indexToName[variable];
        if (name === undefined) {
          throw new Error(`missing name for variable index ${variable}`);
        }
        const value = this.assigns[variable];
        if (value === Value.UNSET) {
          unassigned.push(name);
        } else {
          // Define an own data property even for names such as __proto__;
          // assignment through Object.prototype's setter would lose that key.
          Object.defineProperty(currentAssignments, name, {
            value,
            enumerable: true,
            writable: true,
            configurable: true,
          });
        }
      }

      const picked = this.variablePriority(unassigned, currentAssignments);
      if (Array.isArray(picked) && picked.length === 2) {
        const [name, preferTrue] = picked;
        const variable = this.nameToIndex.get(name);
        if (
          typeof preferTrue === 'boolean' &&
          variable !== undefined &&
          this.named[variable] === 1 &&
          this.assigns[variable] === Value.UNSET
        ) {
          return [variable, preferTrue];
        }
      }
    }

    // Do not pop a fallback before consulting the hook: an accepted override
    // must not accidentally discard some OTHER unassigned heap candidate.
    while (this.decisionHeap.length > 0) {
      const variable = this.popDecisionVariable();
      if (this.assigns[variable] === Value.UNSET) {
        return [variable, this.polarity[variable] === Value.TRUE];
      }
    }
    throw new Error('decision heap exhausted with unassigned named variables');
  }

  // The single LBD metric (MiniSat computeLBD): the number of DISTINCT
  // NONZERO assignment levels among the clause's literals. Learning-time
  // scoring and dynamic tightening share this exact computation so the two
  // uses can never drift apart; level zero never contributes.
  private computeClauseLbd(lits: readonly number[]): number {
    const levels = new Set<number>();
    for (const lit of lits) {
      const level = this.level[varOf(lit)];
      if (level !== 0) {
        levels.add(level);
      }
    }
    return levels.size;
  }

  private bumpClauseActivity(clause: Clause): void {
    clause.activity += this.claInc;
    // The rescale check belongs IN the bump, not after analyze or the decay:
    // later bumps in this SAME analysis must use the rescaled increment, and
    // rescaling the increment is mandatory — omitting it distorts all future
    // relative bump weights (the variable-side scheme argues likewise).
    if (clause.activity > 1e100) {
      for (const other of this.clauses) {
        other.activity *= 1e-100;
      }
      this.claInc *= 1e-100;
    }
  }

  private bumpVariableActivity(variable: number): void {
    this.activity[variable] += this.varInc;
    // The threshold check belongs IN the bump, not after analyze or decay:
    // later bumps in this SAME conflict must use the rescaled increment.
    if (this.activity[variable] > 1e100) {
      for (let index = 0; index < this.activity.length; index += 1) {
        this.activity[index] *= 1e-100;
      }
      this.varInc *= 1e-100;
      // Positive scaling preserves score order mathematically, but floating
      // rounding/underflow can introduce new ties. Restore index tie-breaking
      // too; Floyd heapification is O(n), like the rescale itself.
      for (let index = (this.decisionHeap.length >> 1) - 1; index >= 0; index -= 1) {
        this.siftDecisionDown(index);
      }
    } else if (this.heapPosition[variable] >= 0) {
      // heapPosition is sized numVars: auxiliaries read -1 and never sift.
      this.siftDecisionUp(this.heapPosition[variable]);
    }
  }

  private decisionPrecedes(left: number, right: number): boolean {
    return (
      this.activity[left] > this.activity[right] ||
      (this.activity[left] === this.activity[right] && left < right)
    );
  }

  private insertDecisionVariable(variable: number): void {
    // A propagated/hook-assigned variable may still be present lazily. Do not
    // duplicate it on cancellation; normal heap-selected decisions are absent.
    if (this.heapPosition[variable] >= 0) {
      return;
    }
    this.heapPosition[variable] = this.decisionHeap.length;
    this.decisionHeap.push(variable);
    this.siftDecisionUp(this.decisionHeap.length - 1);
  }

  private popDecisionVariable(): number {
    const variable = this.decisionHeap[0];
    const last = this.decisionHeap.pop();
    this.heapPosition[variable] = -1;
    if (last !== undefined && this.decisionHeap.length > 0) {
      this.decisionHeap[0] = last;
      this.heapPosition[last] = 0;
      this.siftDecisionDown(0);
    }
    return variable;
  }

  private siftDecisionUp(index: number): void {
    const variable = this.decisionHeap[index];
    while (index > 0) {
      const parent = (index - 1) >> 1;
      const parentVariable = this.decisionHeap[parent];
      if (!this.decisionPrecedes(variable, parentVariable)) {
        break;
      }
      this.decisionHeap[index] = parentVariable;
      this.heapPosition[parentVariable] = index;
      index = parent;
    }
    this.decisionHeap[index] = variable;
    this.heapPosition[variable] = index;
  }

  private siftDecisionDown(index: number): void {
    const variable = this.decisionHeap[index];
    while (index * 2 + 1 < this.decisionHeap.length) {
      let child = index * 2 + 1;
      if (
        child + 1 < this.decisionHeap.length &&
        this.decisionPrecedes(this.decisionHeap[child + 1], this.decisionHeap[child])
      ) {
        child += 1;
      }
      const childVariable = this.decisionHeap[child];
      if (!this.decisionPrecedes(childVariable, variable)) {
        break;
      }
      this.decisionHeap[index] = childVariable;
      this.heapPosition[childVariable] = index;
      index = child;
    }
    this.decisionHeap[index] = variable;
    this.heapPosition[variable] = index;
  }

  // Opens the call-scoped conflict budget (Design § Budget contract). Returns
  // true when THIS driver opened the scope and must close it: an outer driver
  // (enumeration owns its whole model loop; solveAssuming owns its call)
  // keeps ownership of an already-active scope, so nested searches share the
  // one call-wide budget. An undefined cap means unlimited — no scope state.
  private openBudgetScope(cap: number | undefined): boolean {
    if (cap === undefined || this.budget !== null) {
      return false;
    }
    this.budget = {
      cap,
      baseline: this.conflictsSoFar,
      // The explicit budget-zero exception: only a ZERO cap may ever permit
      // startup root propagation under an exhausted budget; a positive cap
      // still has unspent room at its first search.
      startupAllowance: cap === 0 ? 'fresh' : 'spent',
    };
    return true;
  }

  private closeBudgetScope(owned: boolean): void {
    if (owned) {
      this.budget = null;
    }
  }

  private budgetExhausted(): boolean {
    return this.budget !== null && this.conflictsSoFar - this.budget.baseline >= this.budget.cap;
  }

  private recordConflict(): void {
    this.stats.conflicts += 1;
    this.conflictsSoFar += 1;
    // Non-root conflicts decay at the END of analyze, after bumping. A
    // terminal root conflict has no analysis/bump but still gets its decay.
    if (this.trailLim.length === 0) {
      this.varInc *= 1 / 0.95;
      // Remember the proof BEFORE the search observes the verdict.
      // propagate() may already have advanced qhead past a falsified clause;
      // a later call must not overlook it and report SAT on that drained queue.
      // Per-call falsified assumptions never enter recordConflict().
      this.permanentUnsat = true;
    }
    // No budget throw here: a detected conflict completes its atomic
    // analysis/learning/backjump/assertion transaction (or, when terminal,
    // establishes UNSAT), and only THEN does the search report exhaustion
    // through the resumable core as 'unknown' (Design § Budget contract).
  }

  // On-demand audit of the clause database, watch lists and reasons. The
  // per-enqueue trail checks in assertTrailInvariant are cheap; this
  // database-wide scan must not run per enqueue, so it fires only when
  // explicitly asked. Safe at reduction boundaries with queued assertions: no
  // propagation fixpoint is required. Internal to Solver, not publicly exported.
  checkInvariants(): void {
    this.assertTrailInvariant();
    const live = new Set(this.clauses);
    if (live.size !== this.clauses.length || this.clauseByKey.size !== live.size) {
      throw new Error('clause database invariant violated: duplicate or stale registry entries');
    }
    for (const clause of this.clauses) {
      const normalized = normalizeClauseLits(clause.lits);
      if (
        normalized === null ||
        normalized.length !== clause.lits.length ||
        clause.lits.some((lit) => !Number.isInteger(lit) || lit < 0 || lit >= this.watches.length)
      ) {
        throw new Error('clause database invariant violated: invalid clause literals');
      }
      if (this.clauseByKey.get(normalized.join(',')) !== clause) {
        throw new Error('clause database invariant violated: non-canonical clause identity');
      }
    }

    const watchCounts = new Map<Clause, number>();
    for (let lit = 0; lit < this.watches.length; lit += 1) {
      const members = new Set<Clause>();
      for (const entry of this.watches[lit]) {
        const clause = entry.clause;
        if (!live.has(clause)) {
          throw new Error('watch invariant violated: clause is not live');
        }
        if (
          clause.lits.length < 3 ||
          (clause.lits[0] !== lit && clause.lits[1] !== lit) ||
          members.has(clause)
        ) {
          throw new Error('watch invariant violated: incorrect or duplicate membership');
        }
        members.add(clause);
        watchCounts.set(clause, (watchCounts.get(clause) ?? 0) + 1);
        // Blocker parity audit: the cached blocker is the clause's current
        // OTHER watch, and the cross-linked twin (holding this literal's
        // other-list entry) tracks it in the opposite direction.
        const other = clause.lits[0] === lit ? clause.lits[1] : clause.lits[0];
        if (
          entry.blocker !== other ||
          entry.twin === null ||
          entry.twin.clause !== clause ||
          entry.twin.blocker !== lit ||
          entry.twin.twin !== entry
        ) {
          throw new Error('watch invariant violated: stale blocker or twin link');
        }
      }
    }
    // Dedicated binary lists: each binary clause appears exactly twice, once
    // per literal, with `other` naming the opposite literal.
    const binaryCounts = new Map<Clause, number>();
    for (let lit = 0; lit < this.binaryWatches.length; lit += 1) {
      const members = new Set<Clause>();
      for (const entry of this.binaryWatches[lit]) {
        const clause = entry.clause;
        if (!live.has(clause)) {
          throw new Error('binary watch invariant violated: clause is not live');
        }
        const other = clause.lits[0] === lit ? clause.lits[1] : clause.lits[0];
        if (
          clause.lits.length !== 2 ||
          (clause.lits[0] !== lit && clause.lits[1] !== lit) ||
          entry.other !== other ||
          members.has(clause)
        ) {
          throw new Error('binary watch invariant violated: incorrect or duplicate membership');
        }
        members.add(clause);
        binaryCounts.set(clause, (binaryCounts.get(clause) ?? 0) + 1);
      }
    }
    for (const clause of this.clauses) {
      const expectedLong = clause.lits.length >= 3 ? 2 : 0;
      const expectedBinary = clause.lits.length === 2 ? 2 : 0;
      if (
        (watchCounts.get(clause) ?? 0) !== expectedLong ||
        (binaryCounts.get(clause) ?? 0) !== expectedBinary
      ) {
        throw new Error('watch invariant violated: missing clause watch');
      }
    }
    for (let variable = 0; variable < this.reason.length; variable += 1) {
      const reason = this.reason[variable];
      if (reason !== null) {
        if (!live.has(reason)) {
          throw new Error('reason invariant violated: clause is not live');
        }
        const lit = variable * 2 + (this.assigns[variable] === Value.FALSE ? 1 : 0);
        if (this.assigns[variable] === Value.UNSET || !reason.lits.includes(lit)) {
          throw new Error('reason invariant violated: clause does not explain its assignment');
        }
      }
    }
  }

  private assertTrailInvariant(): void {
    if (!debugAssertions) {
      return;
    }

    const seen = new Uint8Array(this.assigns.length);
    for (const lit of this.trail) {
      const variable = varOf(lit);
      if (variable < 0 || variable >= this.assigns.length || seen[variable] !== 0) {
        throw new Error('trail invariant violated: assigned variables must appear exactly once');
      }
      seen[variable] = 1;
      const trailValue = isNeg(lit) ? Value.FALSE : Value.TRUE;
      if (this.assigns[variable] !== trailValue) {
        throw new Error('trail invariant violated: trail polarity must match assigns');
      }
    }
    let unassignedNamed = 0;
    for (let variable = 0; variable < this.assigns.length; variable += 1) {
      const assigned = this.assigns[variable] !== Value.UNSET;
      if (assigned !== (seen[variable] === 1)) {
        throw new Error('trail invariant violated: assigns and trail membership must agree');
      }
      if (!assigned && this.named[variable] === 1) {
        unassignedNamed += 1;
      }
    }
    if (unassignedNamed !== this.unassignedNamed) {
      throw new Error('named assignment count must agree with assigns');
    }
  }
}
