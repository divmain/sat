// Public API surface. The single-shot `getSolution` compiles the formula
// once, wraps it in a fresh `Solver` per call, and projects aux variables out
// of the returned model. `getAllSolutions` enumerates every model via
// blocking clauses: the formula is compiled once and ONE persistent Solver
// retains root assumptions, learned clauses, VSIDS and saved phases across
// models. Pure-literal elimination is scoped to the single-shot `getSolution`
// entry point (Design § Solver Core State and Invariants): it is enabled
// there by default and deliberately unsound for enumeration (the (v∨a)
// counterexample) or incremental solving. See Design § Public API
// Specification.

import { compile } from './compile.js';
import type { BooleanExpr, VariableAssignments } from './expr.js';
import { Solver } from './solver.js';
import type { SolverStats, VariablePriority } from './solver.js';

export { and, or, not, implies, xor, Value } from './expr.js';
export type { BooleanExpr, Variable, VariableAssignments } from './expr.js';

// `SolverStats` and `VariablePriority` are defined in solver.ts because the
// Solver constructor consumes them, and importing them from index.ts would
// create a module cycle; index.ts re-exports them as public types. The Solver
// class itself stays internal.
export type { SolverStats, VariablePriority } from './solver.js';

export interface SolveOptions {
  // `| undefined` on every optional property keeps options-forwarding
  // typechecking under exactOptionalPropertyTypes.
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  /** Out-param: zeroed by the callee, then populated with this call's stats. */
  stats?: SolverStats | undefined;
}

export interface SatSolver {
  /**
   * Solve under this call's assumptions, then discard its non-root assignments.
   * Unknown names (even UNSET) and non-Value values throw on EVERY call.
   *
   * Stats are zeroed before validation. Work counters, including learnedClauses
   * (new admissions), cover this invocation only, also when a callback throws.
   * learnedClausesCurrent is the absolute retained live learned population, NOT
   * a delta: it can exceed this call's learnedClauses. Creating the solver and
   * enqueueing its initial units precede these per-call measurements; subsequent
   * root implications count when actually enqueued, never replayed or recounted.
   */
  solve(assumptions?: VariableAssignments, stats?: SolverStats): VariableAssignments | null;
}

const zeroStats = (stats: SolverStats): void => {
  stats.decisions = 0;
  stats.propagations = 0;
  stats.conflicts = 0;
  stats.restarts = 0;
  stats.learnedClauses = 0;
  stats.learnedClausesCurrent = 0;
  stats.learnedLiterals = 0;
  stats.minimizedLiterals = 0;
};

/**
 * Find a single satisfying assignment for `expr`, or `null` when the formula
 * is unsatisfiable. Compile once, solve with a fresh solver per call, and
 * project the model over named variables (aux variables never leak).
 *
 * - `and()` (the empty conjunction) returns `{}`; `or()` (the empty
 *   disjunction) returns `null` — the empty disjunction is the empty clause,
 *   i.e. UNSAT.
 * - Assumptions follow the uniform validation contract: unknown variable
 *   names throw, `Value.UNSET` entries are ignored, and any other value
 *   throws. Assumptions propagate immediately, so an inconsistent set yields
 *   fast `null`.
 * - Pure-literal elimination is enabled by default in this single-shot mode
 *   only; a provided `stats` object is zeroed before solving.
 */
export function getSolution(expr: BooleanExpr, options?: SolveOptions): VariableAssignments | null {
  if (options?.stats !== undefined) {
    zeroStats(options.stats);
  }

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: true,
    stats: options?.stats,
  });

  if (!solver.solve()) {
    return null;
  }
  return solver.model();
}

/**
 * Find every satisfying assignment for `expr` via blocking clauses, or `[]`
 * when the formula is unsatisfiable. Output-sensitive: one persistent `Solver`
 * over the accumulated clause database — no `2^n` materialization or
 * variable-count cap. Learned clauses and heuristic state survive iterations.
 *
 * - No ordering guarantee: enumeration order is solver-dependent and is
 *   deliberately unspecified; compare models order-insensitively.
 * - `and()` (the empty conjunction) returns `[{}]` (the empty blocking clause
 *   terminates the loop); `or()` (the empty disjunction) returns `[]` — the
 *   empty clause makes the formula trivially UNSAT.
 * - A formula that compiles to `levelZeroUnsat` returns `[]` immediately.
 * - Each model is excluded by a permanent named-only blocker clause.
 * - Pure-literal elimination is **disabled** in enumeration mode for the
 *   reason given in the banner above.
 * - Constant assumptions are installed once at root and hold throughout;
 *   `variablePriority` is honored at decision points. Assumptions follow the
 *   uniform validation contract (unknown names throw, `Value.UNSET` ignored,
 *   other values throw).
 * - A provided `stats` object is zeroed once at entry and then **accumulates
 *   across all per-model iterations**; `learnedClausesCurrent` is the actual
 *   live learned database, excluding permanent blockers.
 */
export function getAllSolutions(expr: BooleanExpr, options?: SolveOptions): VariableAssignments[] {
  if (options?.stats !== undefined) {
    zeroStats(options.stats);
  }

  const cnf = compile(expr);
  const solver = new Solver(cnf, {
    assumptions: options?.assumptions,
    variablePriority: options?.variablePriority,
    enablePle: false,
    stats: options?.stats,
  });
  return solver.enumerateModels();
}

/**
 * Compile once and solve repeatedly with independent per-call assumptions.
 * Base clauses, sound learned clauses, saved phases and VSIDS survive calls;
 * pure-literal elimination stays off — its root-level pins are not sound when
 * assumptions change between calls (see the banner above). Returned models
 * are independent named-only records. Calls on the same handle are
 * synchronous and cannot be reentered from a hook.
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
    // enablePle knob); this wrapper exposes exactly one method.
    solve: (assumptions, stats) => solver.solveAssuming(assumptions, stats),
  };
}
