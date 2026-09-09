// Public API surface. The single-shot `getSolution` compiles the formula
// once, wraps it in a fresh `Solver` per call, and projects aux variables out
// of the returned model. `getAllSolutions` enumerates every model via
// blocking clauses: the formula is compiled once and ONE persistent Solver
// retains root assumptions, learned clauses, VSIDS and saved phases across
// models. Pure-literal elimination is scoped to the single-shot entry
// points (`getSolution`/`getSolutionAsync`; Design § Design Principles and
// Hard Constraints): it is enabled there by default and deliberately unsound
// for enumeration (the (v∨a) counterexample) or incremental solving. Every
// entry point returns a rich result — `SolveResult` / `EnumerateResult` —
// never a bare model or null; an UNSAT solve carries a failed-assumption
// core (Design § UNSAT Cores), and 'unknown' reports conflict-budget
// exhaustion or an abort signal. The async entry points slice search work by
// `yieldQuantum` and yield through a platform-neutral scheduler (Design §
// Budgets, Async, and Interruptibility).
// See Design § Target Public API (v3.0).

import { compile } from './compile.js';
import type { BooleanExpr, Variable, VariableAssignments } from './expr.js';
import { createSolverStats, normalizeYieldQuantum, Solver } from './solver.js';
import type { EnumerateResult, SolveResult, SolverStatsInput, VariablePriority } from './solver.js';

export { and, or, not, implies, xor, atMostOne, atMost, atLeast, exactly, Value } from './expr.js';
export type { BooleanExpr, Variable, VariableAssignments } from './expr.js';

// `SolverStats` and `VariablePriority` are defined in solver.ts because the
// Solver constructor consumes them, and importing them from index.ts would
// create a module cycle; index.ts re-exports them as public types. The rich
// result types and the stats factory follow the same pattern (solveAssuming
// produces SolveResult). The Solver class itself stays internal.
export type {
  EnumerateResult,
  SolveResult,
  SolverStats,
  SolverStatsInput,
  VariablePriority,
} from './solver.js';
export { createSolverStats } from './solver.js';

export interface SolveOptions {
  // `| undefined` on every optional property keeps options-forwarding
  // typechecking under exactOptionalPropertyTypes.
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  /**
   * Out-param: zero-filled by the callee (sparse inputs welcome), then
   * populated with this call's complete stats.
   */
  stats?: SolverStatsInput | undefined;
  /**
   * Hard conflict limit for this call: a non-negative safe integer, or
   * `undefined` for unlimited. One budget spans the whole call — for
   * enumeration, construction plus every model search plus the terminal
   * search, never reset per model. A detected conflict completes its atomic
   * learn/backjump/assert transaction; after the final transaction the solve
   * returns `{ status: 'unknown', reason: 'conflictBudget' }` instead of
   * starting another propagation pass. `conflictBudget: 0` still permits the
   * initial root-propagation pass, so a compiled/cached UNSAT, an initial
   * root conflict, or an already-complete model returns a verdict.
   */
  conflictBudget?: number | undefined;
}

/**
 * Async single-shot/enumeration options. Validation runs before the first
 * yield, and every error — validation, hook, or scheduler — rejects the
 * returned Promise (never a synchronous throw).
 */
export interface AsyncSolveOptions extends SolveOptions {
  /**
   * Aborts the search between work slices: the result is
   * `{ status: 'unknown', reason: 'aborted' }` unless a verdict was already
   * established. A pre-aborted signal still validates and consults
   * already-established verdicts, without propagation or preprocessing.
   */
  signal?: AbortSignal | undefined;
  /**
   * Work units between event-loop yields; default 4096, clamped up to a
   * minimum of 64. A work allowance, not a wall-time guarantee.
   */
  yieldQuantum?: number | undefined;
}

// Per-call options for `SatSolver.solve`.
export interface SatSolverCallOptions {
  /** Out-param: zero-filled by the callee, then populated with this call's complete stats. */
  stats?: SolverStatsInput | undefined;
  /**
   * Hard conflict limit for THIS call: a non-negative safe integer, or
   * `undefined` for unlimited. Exhaustion returns
   * `{ status: 'unknown', reason: 'conflictBudget' }` after the final atomic
   * conflict transaction; the handle stays coherent and reusable.
   */
  conflictBudget?: number | undefined;
}

/** Async per-call options for `SatSolver.solveAsync`; errors reject the Promise. */
export interface SatSolverAsyncOptions extends SatSolverCallOptions {
  /** Abort between work slices: `{ status: 'unknown', reason: 'aborted' }` unless a verdict was already established. */
  signal?: AbortSignal | undefined;
  /** Work units between event-loop yields; default 4096, clamped up to a minimum of 64. */
  yieldQuantum?: number | undefined;
}

export interface SatSolver {
  /**
   * Solve under this call's assumptions, then discard its non-root
   * assignments. Unknown names (even UNSET) and non-Value values throw on
   * EVERY call. Returns a `SolveResult`: a complete detached model on 'sat',
   * a failed-assumption `core` on 'unsat' (a subset of this call's
   * assumptions that suffices for UNSAT; `{}` only when UNSAT was proven
   * without them), or 'unknown' when this call's `conflictBudget` is spent.
   *
   * Stats are zero-filled before validation. Work counters, including
   * learnedClauses (new admissions), cover this invocation only, also when a
   * callback throws. learnedClausesCurrent is the absolute retained live
   * learned population, NOT a delta: it can exceed this call's
   * learnedClauses. Creating the solver and enqueueing its initial units
   * precede these per-call measurements; subsequent root implications count
   * when actually enqueued, never replayed or recounted.
   */
  solve(assumptions?: VariableAssignments, options?: SatSolverCallOptions): SolveResult;
  /**
   * The async `solve`: identical semantics, driven in `yieldQuantum` work
   * slices with event-loop yields between them, honoring `signal` at slice
   * checkpoints. Validation runs before the first yield; validation,
   * reentrancy, hook, and scheduler errors reject the Promise. A sync
   * `solve` during an in-flight async call throws, and a second async call
   * rejects — the busy guard spans yields.
   */
  solveAsync(
    assumptions?: VariableAssignments,
    options?: SatSolverAsyncOptions,
  ): Promise<SolveResult>;
  /**
   * Conjoin new constraints into this handle, retaining the compiled
   * formula, learned clauses, VSIDS activity, and saved phases. The
   * expression is validated and compiled into a staged delta before any
   * state mutates, so a throwing `add` leaves the handle unchanged and
   * reusable. New variable names are sorted within the batch and appended
   * after all existing internal indices — deterministic, but history
   * dependent (`createSolver(or('z'))` then `add(and('a'))` orders `z`
   * first); `variables()` always returns the globally sorted named set.
   * Equivalence contract: a sequence of `add`+`solve` calls agrees with
   * single-shot solving of the conjunction on verdicts and model-set
   * validity, not necessarily on identical first models or work counters.
   * Adding to an UNSAT base keeps it UNSAT. Models, cores, and `variables()`
   * snapshots from earlier calls describe the pre-add formula. Throws during
   * an in-flight async solve or from a `variablePriority` hook.
   */
  add(expr: BooleanExpr): void;
  /** Every named variable known so far, globally sorted. */
  variables(): Variable[];
}

/**
 * Find a single satisfying assignment for `expr`. Compile once, solve with a
 * fresh solver per call, and project the model over named variables (aux
 * variables never leak).
 *
 * - `and()` (the empty conjunction) returns `{ status: 'sat', model: {} }`;
 *   `or()` (the empty disjunction) returns `{ status: 'unsat', core: {} }` —
 *   the empty disjunction is the empty clause, i.e. UNSAT independent of any
 *   assumptions.
 * - Assumptions follow the uniform validation contract: unknown variable
 *   names throw, `Value.UNSET` entries are ignored, and any other value
 *   throws. Assumptions propagate immediately, so an inconsistent set yields
 *   a fast 'unsat' whose `core` names the failed assumptions used by the
 *   proof (sound, not necessarily minimal).
 * - Pure-literal elimination is enabled by default in this single-shot mode
 *   only; a provided `stats` object is zero-filled before solving.
 */
export function getSolution(expr: BooleanExpr, options?: SolveOptions): SolveResult {
  const stats =
    options?.stats !== undefined ? Object.assign(options.stats, createSolverStats()) : undefined;

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: true,
    stats,
    conflictBudget: options?.conflictBudget,
  });

  const verdict = solver.search();
  if (verdict === 'unsat') {
    const core = solver.unsatCore();
    if (core === null) {
      throw new Error('UNSAT verdict without an extracted core');
    }
    return { status: 'unsat', core };
  }
  if (verdict === 'unknown') {
    return { status: 'unknown', reason: 'conflictBudget' };
  }
  return { status: 'sat', model: solver.model() };
}

/**
 * The async `getSolution`: identical semantics, driven in `yieldQuantum`
 * work slices (default 4096, minimum 64) with platform-neutral event-loop
 * yields between them. Validation and compilation run synchronously before
 * the first yield, and every error rejects the returned Promise. A
 * pre-aborted `signal` validates and consults already-established verdicts,
 * then resolves `{ status: 'unknown', reason: 'aborted' }` without
 * propagation or preprocessing; a mid-search abort returns 'unknown' with an
 * already-established verdict taking precedence. Async and sync entry points
 * agree exactly for identical non-aborted histories.
 */
export async function getSolutionAsync(
  expr: BooleanExpr,
  options?: AsyncSolveOptions,
): Promise<SolveResult> {
  const stats =
    options?.stats !== undefined ? Object.assign(options.stats, createSolverStats()) : undefined;
  const yieldQuantum = normalizeYieldQuantum(options?.yieldQuantum);

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: true,
    stats,
    conflictBudget: options?.conflictBudget,
  });

  const verdict = await solver.solveAsync([], options?.signal, yieldQuantum);
  if (verdict.status === 'unsat') {
    const core = solver.unsatCore();
    if (core === null) {
      throw new Error('UNSAT verdict without an extracted core');
    }
    return { status: 'unsat', core };
  }
  if (verdict.status === 'unknown') {
    return { status: 'unknown', reason: verdict.reason };
  }
  return { status: 'sat', model: solver.model() };
}

/**
 * Find every satisfying assignment for `expr` via blocking clauses.
 * Output-sensitive: one persistent `Solver` over the accumulated clause
 * database — no `2^n` materialization or variable-count cap. Learned clauses
 * and heuristic state survive iterations.
 *
 * - No ordering guarantee: enumeration order is solver-dependent and is
 *   deliberately unspecified; compare models order-insensitively.
 * - `and()` (the empty conjunction) yields `models: [{}]` (the empty blocking
 *   clause terminates the loop); `or()` (the empty disjunction) yields
 *   `models: []` — the empty clause makes the formula trivially UNSAT.
 * - A formula that compiles to `levelZeroUnsat` yields `models: []`
 *   immediately.
 * - Each model is excluded by a permanent named-only blocker clause.
 * - Pure-literal elimination is **disabled** in enumeration mode for the
 *   reason given in the banner above.
 * - Constant assumptions are installed once at root and hold throughout;
 *   `variablePriority` is honored at decision points. Assumptions follow the
 *   uniform validation contract (unknown names throw, `Value.UNSET` ignored,
 *   other values throw).
 * - A provided `stats` object is zero-filled once at entry and then
 *   **accumulates across all per-model iterations**;
 *   `learnedClausesCurrent` is the actual live learned database, excluding
 *   permanent blockers.
 */
export function getAllSolutions(expr: BooleanExpr, options?: SolveOptions): EnumerateResult {
  const stats =
    options?.stats !== undefined ? Object.assign(options.stats, createSolverStats()) : undefined;

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: false,
    stats,
    conflictBudget: options?.conflictBudget,
  });
  return solver.enumerateModels();
}

/**
 * The async `getAllSolutions`: identical semantics with `yieldQuantum` work
 * slices and event-loop yields between them (including between the many
 * short per-model searches). Abort returns `{ status: 'unknown',
 * reason: 'aborted', models }` with the models found so far — a non-empty
 * partial `models` still proves the formula SAT; only completeness is
 * undetermined. Every error rejects the returned Promise.
 */
export async function getAllSolutionsAsync(
  expr: BooleanExpr,
  options?: AsyncSolveOptions,
): Promise<EnumerateResult> {
  const stats =
    options?.stats !== undefined ? Object.assign(options.stats, createSolverStats()) : undefined;
  const yieldQuantum = normalizeYieldQuantum(options?.yieldQuantum);

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: false,
    stats,
    conflictBudget: options?.conflictBudget,
  });
  return solver.enumerateModelsAsync(options?.signal, yieldQuantum);
}

/**
 * Compile once and solve repeatedly with independent per-call assumptions.
 * Base clauses, sound learned clauses, saved phases and VSIDS survive calls;
 * pure-literal elimination stays off — its root-level pins are not sound when
 * assumptions change between calls (see the banner above). Returned models
 * are independent named-only records; UNSAT calls return the extracted
 * failed-assumption core. `add` conjoins further constraints into the same
 * handle (failure-atomic, retaining learned state), and `variables` reports
 * the globally sorted named universe known so far. Calls on the same handle
 * are synchronous and cannot be reentered from a hook.
 */
export function createSolver(
  expr: BooleanExpr,
  options?: { variablePriority?: VariablePriority | undefined },
): SatSolver {
  const solver = new Solver(compile(expr), {
    variablePriority: options?.variablePriority,
    enablePle: false,
  });
  return {
    // A closure, not the Solver itself: re-exporting the class would leak
    // internal fields and methods (clauses, watches, enumerateModels, the
    // enablePle knob); this wrapper exposes exactly the two solve methods
    // plus add/variables.
    solve: (assumptions, callOptions) =>
      solver.solveAssuming(assumptions, callOptions?.stats, callOptions?.conflictBudget),
    // The async method's body runs synchronously until its first await, so
    // validation and the busy guard reject the returned Promise rather than
    // throwing into this plain closure.
    solveAsync: (assumptions, callOptions) =>
      solver.solveAssumingAsync(
        assumptions,
        callOptions?.stats,
        callOptions?.conflictBudget,
        callOptions?.signal,
        callOptions?.yieldQuantum,
      ),
    add: (addExpr) => solver.add(addExpr),
    variables: () => solver.variables(),
  };
}
