// Public API surface (v2). The single-shot `getSolution` compiles the
// formula once, wraps it in a fresh `Solver` per call, and projects aux
// variables out of the returned model. `getAllSolutions` enumerates every
// model via blocking clauses: the formula is compiled once, then each
// iteration solves the accumulated clause database (original clauses plus
// every blocking clause so far) with a fresh `Solver`, records the projected
// model, and appends the blocking clause that excludes it. Pure-literal
// elimination is scoped to the single-shot `getSolution` entry point (Design
// § Solver Core State and Invariants): it is enabled there by default and
// deliberately unsound for enumeration (the (v∨a) counterexample) or
// incremental solving. See Design § Public API Specification.

import { compile, negLit, normalizeClauseLits, posLit } from './compile.js';
import type { CompiledCnf } from './compile.js';
import type { BooleanExpr, VariableAssignments } from './expr.js';
import { Value } from './expr.js';
import { Solver } from './solver.js';
import type { SolverStats, VariablePriority } from './solver.js';

export { and, or, not, implies, xor, Value } from './expr.js';
export type { BooleanExpr, Variable, VariableAssignments } from './expr.js';

// `SolverStats` and `VariablePriority` are defined in solver.ts (the Solver
// constructor needs them in Phase 1, before index.ts exists as a public face,
// and importing them from index.ts would create a module cycle); index.ts
// re-exports them as public types at this rewire. The Solver class itself
// stays internal.
export type { SolverStats, VariablePriority } from './solver.js';

export interface SolveOptions {
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  /** Out-param: zeroed by the callee, then populated with this call's stats. */
  stats?: SolverStats | undefined;
}

const zeroStats = (stats: SolverStats): void => {
  stats.decisions = 0;
  stats.propagations = 0;
  stats.conflicts = 0;
  stats.restarts = 0;
  stats.learnedClauses = 0;
  stats.learnedClausesCurrent = 0;
};

/**
 * Find a single satisfying assignment for `expr`, or `null` when the formula
 * is unsatisfiable. Compile once, solve with a fresh solver per call, and
 * project the model over named variables (aux variables never leak).
 *
 * - `and()` (the empty conjunction) returns `{}`; `or()` (the empty
 *   disjunction) returns `null`.
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

// Append the blocking clause that excludes `model` to the accumulated clause
// database: the negations of the model's named-variable literals, normalized
// (Design § Public API Specification). Aux variables are deliberately
// excluded — each auxiliary variable is fully implied by its gate clauses
// once the named variables are set, so every total model sharing this named
// part is excluded, and blocking on named variables alone is complete. Clause
// objects are shared with each fresh `Solver` (the constructor copies the
// array, never the clauses) and are treated as immutable by Phase 1, so
// appending to `cnf.clauses` is the Phase-1 design's "accumulated database".
function addBlockingClause(cnf: CompiledCnf, model: VariableAssignments): void {
  const rawLits: number[] = [];
  for (let index = 0; index < cnf.numNamedVars; index += 1) {
    const name = cnf.indexToName[index];
    if (name === undefined) {
      throw new Error(`missing name for variable index ${index}`);
    }
    const value = model[name];
    rawLits.push(value === Value.TRUE ? negLit(index) : posLit(index));
  }
  // Each named variable appears exactly once, so normalization can never
  // detect a tautology here; it sorts for determinism and keeps the empty
  // blocking clause that terminates zero-variable enumeration.
  const lits = normalizeClauseLits(rawLits);
  if (lits === null) {
    throw new Error('internal error: a blocking clause over named variables is tautological');
  }
  cnf.clauses.push({ lits, learned: false, activity: 0, lbd: 0 });
  if (lits.length === 0) {
    cnf.levelZeroUnsat = true;
  }
}

/**
 * Find every satisfying assignment for `expr` via blocking clauses, or `[]`
 * when the formula is unsatisfiable. Output-sensitive: one fresh `Solver`
 * per model over the accumulated clause database (original clauses plus every
 * blocking clause so far) — no `2^n` materialization, no variable-count cap.
 *
 * - No ordering guarantee: enumeration order is solver-dependent and is
 *   deliberately unspecified; compare models order-insensitively.
 * - `and()` (the empty conjunction) returns `[{}]` (the empty blocking clause
 *   terminates the loop); `or()` (the empty disjunction) returns `[]`.
 * - A formula that compiles to `levelZeroUnsat` returns `[]` immediately.
 * - Pure-literal elimination is **disabled** in enumeration mode: it is
 *   satisfiability-preserving but not model-preserving, and stale level-0
 *   pins interact with permanent blocking clauses to silently drop valid
 *   models (Design § Solver Core State and Invariants, the `(v∨a)`
 *   counterexample).
 * - Assumptions and `variablePriority` are honored on every internal
 *   iteration; assumptions follow the uniform validation contract (unknown
 *   names throw, `Value.UNSET` ignored, other values throw).
 * - A provided `stats` object is zeroed once at entry and then **accumulates
 *   across all per-model iterations**.
 */
export function getAllSolutions(expr: BooleanExpr, options?: SolveOptions): VariableAssignments[] {
  if (options?.stats !== undefined) {
    zeroStats(options.stats);
  }

  const cnf = compile(expr);
  const solutions: VariableAssignments[] = [];

  while (true) {
    const solver = new Solver(cnf, {
      assumptions: options?.assumptions,
      variablePriority: options?.variablePriority,
      enablePle: false,
      stats: options?.stats,
    });

    if (!solver.solve()) {
      return solutions;
    }
    const model = solver.model();
    solutions.push(model);
    addBlockingClause(cnf, model);
  }
}
