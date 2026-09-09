# @divmain/sat, a SAT solver library

Solve Boolean satisfiability problems in Node.js with a zero-runtime-dependency, TypeScript/ESM library. Version 2 compiles expressions to CNF with a Tseitin transformation and uses an iterative **conflict-driven clause learning (CDCL)** solver: two-watched-literal propagation, first-UIP learning, non-chronological backtracking, VSIDS, phase saving, deterministic Glucose-style EMA restarts with blocking, and learned-clause reduction. Find one model, enumerate all models, or compile once and solve repeatedly under different assumptions.

## Installation

To install the library, use npm or yarn:

```bash
npm install @divmain/sat
```

or

```bash
yarn add @divmain/sat
```

## Basic Usage

This is a native ESM package. Save a JavaScript example below as `example.mjs` and run `node example.mjs` after installation. TypeScript consumers can import the accompanying declarations; compile TypeScript examples with NodeNext module resolution before running the emitted JavaScript. The runnable examples include their own imports.

```javascript
import {
  and,
  or,
  not,
  implies,
  xor,
  Value,
  getSolution,
  getAllSolutions,
  createSolver,
} from '@divmain/sat';

console.log(getSolution(and('ready'))); // { status: 'sat', model: { ready: 1 } }
```

### Boolean Expressions

Variables are strings. Each constructor accepts variables or nested expressions and returns a `BooleanExpr`:

- `and(...exprs)`: All variables or subexpressions must be true.
- `or(...exprs)`: At least one variable or subexpression must be true.
- `not(expr)`: The specified variable or subexpression cannot be true.
- `implies(first, second)`: If `first` is true then `second` must also be true. If `first` is false, `second` can be true or false.
- `xor(first, second)`: Either `first` or `second` must be true, but not both.
- `atMostOne(...exprs)`: At most one operand is true (pure sugar for `atMost(1, ...)`).
- `atMost(k, ...exprs)`: At most `k` operands are true.
- `atLeast(k, ...exprs)`: At least `k` operands are true.
- `exactly(k, ...exprs)`: Exactly `k` operands are true — `atMost(k, ...)` and `atLeast(k, ...)` together.

The solving functions take an expression, not a bare string: use `and('a')` to assert one variable. `implies` and `xor` are constructor sugar over `and`/`or`/`not`; the formula shapes are unchanged from v1. Treat an expression as input, not as a live way to modify an already-created solver.

For the cardinality constructors, `k` must be a non-negative safe integer and the operands are a **multiset**: `exactly(1, 'a', 'a')` is UNSAT because a true `a` counts twice. Edge bounds fold at compile time — `atLeast(0, ...)` is always true, `atMost(k, ...)` with `k >= n` is always true, `atLeast(k, ...)` with `k > n` is always false, and `atMost(0, ...)` asserts every operand false — and variables that fold away still appear in every returned model. Prefer **conjunctive placement** (a direct conjunct of the top-level `and(...)`): conjunctive bounds compile to compact pairwise or sequential-counter clauses, while a nested occurrence (under `or`, `not`, or another constructor) is fully reified through a totalizer, which is larger.

`Value` is numeric: `UNSET = -1`, `FALSE = 0`, `TRUE = 1`. Use `Value.TRUE`/`Value.FALSE` for assumptions, **not JavaScript booleans**. Returned models contain only numeric `0`/`1`, never `UNSET`.

## Examples

### Finding a Single Solution

`getSolution` returns a `SolveResult`: `{ status: 'sat', model }` with a complete model, or `{ status: 'unsat', core }` with the failed assumptions that suffice for UNSAT:

```javascript
import { and, or, not, xor, implies, getSolution } from '@divmain/sat';

const expr = and(
  not('b'),
  or('a', 'b'),
  xor('b', 'c'),
  implies('c', and('d', 'e')),
);
const result = getSolution(expr);
console.log(result);
// { status: 'sat', model: { a: 1, b: 0, c: 1, d: 1, e: 1 } }
```

### Finding All Solutions

`getAllSolutions` returns an `EnumerateResult`: `{ status: 'complete', models }` with every model (`models: []` for UNSAT). This example has one solution; in general, **enumeration order is unspecified**.

```javascript
import { and, or, not, xor, implies, getAllSolutions, Value } from '@divmain/sat';

const expr = and(
  not('b'),
  or('a', 'b'),
  xor('b', 'c'),
  implies('c', and('d', 'e')),
);
console.log(getAllSolutions(expr));
// { status: 'complete', models: [{ a: 1, b: 0, c: 1, d: 1, e: 1 }] }

console.log(getAllSolutions(or('a', 'b'), { assumptions: { a: Value.FALSE } }));
// { status: 'complete', models: [{ a: 0, b: 1 }] }
```

### Reusing a Compiled Solver

```javascript
import { createSolver, xor, Value } from '@divmain/sat';

const solver = createSolver(xor('left', 'right'));
console.log(solver.solve({ left: Value.TRUE }));
// { status: 'sat', model: { left: 1, right: 0 } }
console.log(solver.solve({ left: Value.TRUE, right: Value.TRUE }));
// { status: 'unsat', core: { left: 1, right: 1 } }: the failed assumptions
console.log(solver.solve({ left: Value.FALSE }));
// { status: 'sat', model: { left: 0, right: 1 } }
console.log(solver.solve().status); // 'sat': earlier assumptions do not persist
```

### Adding Constraints Incrementally

`SatSolver.add(expr)` conjoins new constraints into a live solver, retaining the compiled formula, learned clauses, and heuristic state — the other half of incremental SAT (iterative deepening, CEGAR, optimization loops). The expression is validated and compiled into a staged delta before any state changes, so a throwing `add` leaves the handle unchanged and reusable. New variable names become valid assumption and model names immediately; `solver.variables()` returns the globally sorted named set known so far. A sequence of `add` + `solve` calls agrees with single-shot solving of the conjunction on verdicts and model validity, though first models and work counters may differ. Adding constraints to an unsatisfiable base keeps it UNSAT.

This example vertex-colors a graph with iterative deepening on the palette: each SAT round forbids the highest remaining color, until UNSAT proves the last model used the fewest colors.

```javascript
import { and, or, not, createSolver } from '@divmain/sat';

// Variables are named `vertex#color`: a—b—c—d—a cycle, palette of 3.
const vertices = ['a', 'b', 'c', 'd'];
const edges = [
  ['a', 'b'],
  ['b', 'c'],
  ['c', 'd'],
  ['d', 'a'],
];
const color = (vertex, k) => `${vertex}#${k}`;

const solver = createSolver(
  and(
    // Every vertex gets at least one color from the palette.
    ...vertices.map((v) => or(color(v, 0), color(v, 1), color(v, 2))),
    // Adjacent vertices never share a color.
    ...edges.flatMap(([u, v]) => [0, 1, 2].map((k) => or(not(color(u, k)), not(color(v, k))))),
  ),
);

let model = null;
for (let palette = 3; palette > 0; palette -= 1) {
  const result = solver.solve();
  console.log(`palette ${palette}: ${result.status}`);
  if (result.status !== 'sat') break;
  model = result.model;
  // Deepen: forbid the highest remaining color everywhere.
  solver.add(and(...vertices.map((v) => not(color(v, palette - 1)))));
}
console.log(solver.variables().length); // 12
console.log(model);
// a 2-coloring: { 'a#0': 0, 'a#1': 1, 'a#2': 0, 'b#0': 1, ..., 'd#1': 0 }
```

### Cardinality Constraints

`atMostOne`, `atMost`, `atLeast`, and `exactly` bound how many operands may be true, with operands as a multiset (repeated variables count repeatedly). They compose with every other constructor and with `SatSolver.add`, but conjunctive placement compiles smallest (see [Boolean Expressions](#boolean-expressions)).

```javascript
import { and, atLeast, atMostOne, exactly, getAllSolutions, getSolution, not } from '@divmain/sat';

// On-call rotation: exactly one engineer is primary, the primary cannot also
// review, and at least one reviewer covers the release.
const schedule = and(
  exactly(1, 'primary-ada', 'primary-bo', 'primary-cy'),
  atMostOne('primary-ada', 'reviewer-ada'),
  atLeast(1, 'reviewer-ada', 'reviewer-bo'),
);

console.log(getSolution(schedule).status); // 'sat'
console.log(getAllSolutions(schedule).models.length); // 7
console.log(getSolution(and(schedule, not('reviewer-ada'), not('reviewer-bo'))));
// { status: 'unsat', core: {} }: no schedule works without a reviewer
```

### Async Solving

Every entry point has an async twin — `getSolutionAsync`, `getAllSolutionsAsync`, and `SatSolver.solveAsync` — with identical semantics driven in `yieldQuantum` work slices (default 4096, clamped to a minimum of 64) and platform-neutral event-loop yields between them. Validation runs before the first yield, and every error — validation, heuristic callback, or scheduler — rejects the returned Promise. An optional `AbortSignal` aborts between slices, and `conflictBudget` bounds the conflicts one call may spend; both produce `{ status: 'unknown', reason: 'aborted' | 'conflictBudget' }` instead of a verdict. Async and sync calls agree exactly for identical histories.

```javascript
import { and, implies, getSolutionAsync } from '@divmain/sat';

const result = await getSolutionAsync(and('a', implies('a', 'b')), {
  conflictBudget: 10_000,
  yieldQuantum: 64,
});
console.log(result);
// { status: 'sat', model: { a: 1, b: 1 } }
```

## API

The complete package-root runtime exports are `and`, `or`, `not`, `implies`, `xor`, `atMostOne`, `atMost`, `atLeast`, `exactly`, `Value`, `getSolution`, `getSolutionAsync`, `getAllSolutions`, `getAllSolutionsAsync`, `createSolver`, and `createSolverStats`. The type exports are `BooleanExpr`, `Variable`, `VariableAssignments`, `VariablePriority`, `SolverStats`, `SolverStatsInput`, `SolveResult`, `EnumerateResult`, `SolveOptions`, `AsyncSolveOptions`, `SatSolverCallOptions`, `SatSolverAsyncOptions`, and `SatSolver` (use `import type { ... } from '@divmain/sat'`). There is no default export.

Type/signature reference (not an executable example):

```ts
type Variable = string;
type BooleanExpr =
  | { and: Array<Variable | BooleanExpr> }
  | { or: Array<Variable | BooleanExpr> }
  | { not: Variable | BooleanExpr }
  | { atMost: { k: number; exprs: Array<Variable | BooleanExpr> } }
  | { atLeast: { k: number; exprs: Array<Variable | BooleanExpr> } };
enum Value { UNSET = -1, FALSE = 0, TRUE = 1 }
type VariableAssignments = Record<Variable, Value>;

// k must be a non-negative safe integer; operands form a multiset.
declare function atMostOne(...exprs: Array<Variable | BooleanExpr>): BooleanExpr;
declare function atMost(k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr;
declare function atLeast(k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr;
declare function exactly(k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr;

type VariablePriority = (
  unassigned: Variable[],
  assignments: Partial<Record<Variable, Value>>,
) => [Variable, boolean] | null;

interface SolverStats {
  decisions: number;
  propagations: number;
  conflicts: number;
  restarts: number;
  learnedClauses: number;
  learnedClausesCurrent: number;
  learnedLiterals: number;
  minimizedLiterals: number;
}

type SolverStatsInput = Partial<SolverStats>;
declare function createSolverStats(): SolverStats;

type SolveResult =
  | { status: 'sat'; model: VariableAssignments }
  | { status: 'unsat'; core: VariableAssignments }       // failed assumptions; {} = assumption-independent proof
  | { status: 'unknown'; reason: 'conflictBudget' | 'aborted' }; // budget spent or signal aborted
type EnumerateResult =
  | { status: 'complete'; models: VariableAssignments[] }  // [] = UNSAT / no models
  | { status: 'unknown'; models: VariableAssignments[]; reason: 'conflictBudget' | 'aborted' };

interface SolveOptions {
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  stats?: SolverStatsInput | undefined;
  conflictBudget?: number | undefined;   // hard per-call conflict limit; undefined = unlimited
}
interface AsyncSolveOptions extends SolveOptions {
  signal?: AbortSignal | undefined;      // abort between work slices
  yieldQuantum?: number | undefined;     // work units between yields; default 4096, min 64
}
interface SatSolverCallOptions {
  stats?: SolverStatsInput | undefined;
  conflictBudget?: number | undefined;
}
interface SatSolverAsyncOptions extends SatSolverCallOptions {
  signal?: AbortSignal | undefined;
  yieldQuantum?: number | undefined;
}

declare function getSolution(expr: BooleanExpr, options?: SolveOptions): SolveResult;
declare function getSolutionAsync(expr: BooleanExpr, options?: AsyncSolveOptions): Promise<SolveResult>;
declare function getAllSolutions(expr: BooleanExpr, options?: SolveOptions): EnumerateResult;
declare function getAllSolutionsAsync(expr: BooleanExpr, options?: AsyncSolveOptions): Promise<EnumerateResult>;
declare function createSolver(
  expr: BooleanExpr,
  options?: { variablePriority?: VariablePriority | undefined },
): SatSolver;

interface SatSolver {
  solve(assumptions?: VariableAssignments, options?: SatSolverCallOptions): SolveResult;
  solveAsync(assumptions?: VariableAssignments, options?: SatSolverAsyncOptions): Promise<SolveResult>;
  add(expr: BooleanExpr): void;                 // conjoin new constraints; retains learned state
  variables(): Variable[];                      // globally sorted named variables known so far
}
```

`getVariables`, `isVariable`, the CNF/compiler helpers (including `compileCount`), `Clause`, `CompiledCnf`, the internal `Solver` class, and DIMACS tooling are **not package-root exports or supported public APIs**. Import through `@divmain/sat`, not internal `dist/` paths.

### Models, Assumptions, and Validation

- Every model is an ordinary object with an **own enumerable data property for every named variable**, including unconstrained variables. Values are numeric `Value.TRUE`/`Value.FALSE`; no auxiliary variables, missing names, or `UNSET` values leak. Results are independent objects, not views into mutable solver state. A valid first model need not match v1's first model.
- Pass only known facts in `assumptions`; you do not need a full record. Own enumerable string entries are read once per call, in `Object.entries` order. Inherited properties and symbol keys are not assumptions.
- Unknown variable names throw a descriptive `Error`, **even when their value is `Value.UNSET`**. A known variable with `UNSET` is ignored. Anything other than numeric `-1`, `0`, or `1` throws, including `true`, `false`, strings, and `undefined` values.
- These rules apply to `getSolution`, `getAllSolutions`, and every `SatSolver.solve` call, even when UNSAT is already known or cached. Valid but inconsistent assumptions yield `{ status: 'unsat', core }` (or `models: []` for enumeration), not a validation error.
- An UNSAT `core` is a subset of the call's assumptions (same values) that suffices for UNSAT: sound, not necessarily minimal. `{}` appears only when no assumptions were supplied or the base formula was proven UNSAT without them. `EnumerateResult` carries no core.
- Assumptions are propagated, rather than used as v1-style leaf filters. Returned models always extend the current assumptions. Enumeration's assumptions stay constant for the whole enumeration.
- Arbitrary string names are supported. For `__proto__`, construct own entries with `Object.fromEntries([['__proto__', Value.TRUE]])` or a computed property, not the special object-literal prototype setter. Use `Object.hasOwn(model, name)` when checking membership; `0` is a valid assigned value, not absence.

Empty formulas have these semantics (also for repeated `createSolver(expr).solve()` calls):

| Expression | `getSolution(expr)` | `getAllSolutions(expr)` | `createSolver(expr).solve()` |
| --- | --- | --- | --- |
| `and()` (true) | `{ status: 'sat', model: {} }` | `{ status: 'complete', models: [{}] }` | `{ status: 'sat', model: {} }` |
| `or()` (false) | `{ status: 'unsat', core: {} }` | `{ status: 'complete', models: [] }` | `{ status: 'unsat', core: {} }` |

### `getSolution(expr, options?)`

Compiles once and uses a fresh solver for this call. `SolveOptions` accepts `assumptions`, `variablePriority`, a writable `stats` out-parameter (sparse objects are zero-filled), and a `conflictBudget`: a non-negative safe-integer conflict limit for this call (`undefined` is unlimited). Exhaustion returns `{ status: 'unknown', reason: 'conflictBudget' }` after the final atomic conflict transaction; `conflictBudget: 0` still permits the initial root-propagation pass, so a compiled UNSAT, an initial root conflict, or an already-complete model returns a verdict. Returns a `SolveResult`: one complete model on `'sat'`, or the failed-assumption core on `'unsat'`.

Startup unit propagation is followed by **pure-literal elimination (PLE)**: each round assigns all currently pure variables in an index-ordered batch, propagates, and repeats to a fixpoint. PLE is enabled **only here**. It preserves satisfiability, not the set of models, so it can change which valid model is returned. Named don't-cares are completed by ordinary decisions.

### `getAllSolutions(expr, options?)`

Compiles once and uses one persistent solver, retaining learned clauses, VSIDS state, and saved phases between models. Each returned model adds a permanent blocking clause over named variables. PLE is **disabled**: its persistent pins could otherwise cause valid models to be missed after adding blockers. A `conflictBudget` here spans the entire call — construction, every model search, and the terminal search — never resetting per model; exhaustion returns `'unknown'` with the partial model prefix found so far (a non-empty prefix still proves the formula satisfiable).

Enumeration is **output-sensitive**, not an up-front materialization of all `2^n` assignments: one search per model plus a final UNSAT search. There is no v1 32-variable enumeration limit. However, each search has exponential worst-case cost, there may be exponentially many models, and the returned array **and permanent blockers grow with the output**. This is not a streaming or constant-memory API; learned-clause reduction does not bound total memory. Compare model sets order-insensitively, not by array position.

### `createSolver(expr, { variablePriority? }?)` / `SatSolver.solve(assumptions?, { stats?, conflictBudget? }?)`

Variable collection and compilation happen once at creation. Each synchronous `solve` call validates and snapshots its assumptions, searches, projects an independent model, and cancels non-root assignments in a `finally` cleanup, including on validation or callback errors. The base formula, sound learned clauses, VSIDS activity, saved phases, and learned-clause reduction cadence survive calls; the previous call's assumptions do not. PLE is **disabled** because pins derived under one assumption set need not hold under the next.

The shared search loop applies the assumption prefix **before ordinary decisions and before returning SAT**. Already-true assumptions consume dummy levels; backjumps or restarts that remove assumptions cause them to be replayed. A falsified assumption means UNSAT for that call, not permanent base UNSAT, and the returned `core` names the failed assumptions the proof used. For example, `(a → x) ∧ (a → ¬x)` is UNSAT under `a=TRUE` but remains satisfiable under `a=FALSE`.

A genuine root conflict proving the base formula UNSAT is cached; later valid calls return `{ status: 'unsat', core: {} }` without further search. Validation still occurs before using that cache. A satisfiable reusable solver can return a different valid model on later calls because its learned clauses and phases are retained. A per-call `conflictBudget` bounds that call's conflicts, returning `'unknown'` on exhaustion while the handle stays coherent and reusable. `solveAsync` is the async twin with `signal`/`yieldQuantum` (see [Async Solving](#async-solving)); a sync `solve` during an in-flight async call throws, and a second async call rejects, because calls on the same handle cannot be reentered from a heuristic or each other.

`SatSolver.add(expr)` conjoins further constraints into the same handle without recompiling or losing learned state: see [Adding Constraints Incrementally](#adding-constraints-incrementally). New names are sorted within each added batch and appended after all previously assigned internal indices, so the internal index order is deterministic but **history-dependent**; `variables()` returns the globally sorted named set regardless. An `add` that throws (for example, a malformed hand-built expression) is failure-atomic: the handle is byte-for-byte unchanged and stays reusable. `add` requires a quiescent handle — it throws during an in-flight async solve or from a `variablePriority` hook — and it reports no stats: like construction, its work is excluded from every per-call `stats` measurement. It invalidates derived state from earlier calls: models, cores, and `variables()` snapshots describe the pre-add formula. This handle has no enumeration, reset, or disposal method; drop it when no longer needed.

### `SolverStats`

Out-parameters are sparse (`SolverStatsInput`): the callee zero-fills missing fields, then populates all of them. `createSolverStats()` returns a complete all-zero object. Outputs are reset at entry, before compilation/assumption validation, then populated with actual work. Do not interpret an unchanged or zero counter as a satisfiability verdict.

```javascript
import { createSolver, createSolverStats, getSolution, xor, Value } from '@divmain/sat';

const stats = createSolverStats();
getSolution(xor('a', 'b'), { stats });
console.log(stats.decisions); // 1

const solver = createSolver(xor('a', 'b'));
solver.solve({ a: Value.TRUE }, { stats }); // same object, reset for this invocation
console.log(stats.decisions); // 0: assumptions and implications are not decisions
```

| Field | What it counts |
| --- | --- |
| `decisions` | Ordinary named-variable decisions, including don't-cares; not assumptions, assumption replays, dummy levels, or propagation. |
| `propagations` | New non-decision, non-assumption enqueues: units, implications (including auxiliaries), learned assertions, and single-shot PLE assignments. Already-assigned values are not recounted. |
| `conflicts` | Recorded startup/propagation conflicts, including terminal root conflicts. A compiled empty clause, cached UNSAT, or a falsified per-call assumption can return UNSAT without a new counted conflict. |
| `restarts` | Actual additional cancellations from a positive level to root at a restart boundary, not ordinary backjumps or already-root no-ops. |
| `learnedClauses` | New learned-clause admissions in the measurement scope. Live duplicate rediscoveries do not count; re-deriving a deleted clause does. Does not decrease on deletion. |
| `learnedClausesCurrent` | Absolute live learned-clause population at the end, not peak usage, a delta, or total memory. Excludes original/permanent blocking clauses and decreases on deletion or promotion to permanent status. |

Measurement scopes differ deliberately:

- `getSolution`: the whole call, including construction-time unit enqueues.
- `getAllSolutions`: reset once, then accumulate across construction, all models/blockers, and the terminal UNSAT search. The live count is the final database population, not a sum across models.
- `SatSolver.solve`: **this invocation's** work and new learned admissions, plus the **absolute retained** live count. Thus `learnedClausesCurrent` can exceed this call's `learnedClauses`. Creating the solver and enqueueing initial units occur before these measurements; later root implications count when actually enqueued. Outputs also report work done before a callback throws. Resetting the output does not reset the retained solver state or lifetime internal accounting; each search starts its own restart epoch. Restart timing follows a deterministic EMA policy over learned-clause LBDs whose fast/slow histories are **lifetime-scoped**: they persist across searches and incremental calls on the same handle, so one call's restart timing can reflect earlier calls' learning (a disclosed change from the v2 per-search Luby schedule).

## Guiding Decisions with `variablePriority`

The default is VSIDS, with sorted named-variable indices for activity ties and initially FALSE-first polarity, then phase saving. A domain heuristic is optional and **can make performance worse** by overriding that brancher.

- The hook receives **named, currently unassigned variables only**, plus a snapshot partial assignment over named variables; auxiliaries never appear. It runs only when an ordinary decision is needed, never during propagation or assumption replay. It may never be called on a fully propagated/PLE-solved problem.
- Only assigned names are own properties of the partial record. Missing ordinary names read as `undefined`, **not `Value.UNSET`**. For arbitrary names such as `toString`, use `Object.hasOwn` to exclude inherited properties before reading.
- Return `[variable, preferTrue]` with a real **boolean** polarity: `true` prefers TRUE, `false` prefers FALSE. This overrides the saved phase for that decision; it does not constrain the model. Use assumptions for facts.
- Return `null` to defer to VSIDS, not to signal that solving is complete. Unknown/already-assigned choices and malformed tuples/non-boolean polarities are defensively ignored in favor of the default brancher.
- The call cadence is not v1's once-per-recursion-node cadence. Learning, backjumps, and restarts can discard decisions, and the hook is not guaranteed to be consulted again after any particular event. Do not rely on a chosen assignment persisting. Do not reenter a `SatSolver` from its hook.

### Ported Hypergraph Heuristic

Each pair is `[target, prerequisite]`, encoded as `target → prerequisite`. This ports the v1 connected-node ranking: among `unassigned` candidates, count connected targets already TRUE, penalize FALSE ones, ignore unknowns, and prefer TRUE for a positive-ranked candidate. Ties retain the supplied order. This is a search preference, not a performance promise.

```typescript
import { and, implies, getSolution, createSolverStats, Value } from '@divmain/sat';
import type { Variable, VariablePriority } from '@divmain/sat';

const prerequisites: Array<[Variable, Variable]> = [
  ['b', 'a'], ['c', 'a'], ['e', 'd'], ['g', 'c'],
  ['f', 'c'], ['f', 'e'], ['h', 'b'], ['h', 'g'],
  ['j', 'i'], ['k', 'j'], ['l', 'k'], ['m', 'l'], ['n', 'm'],
  ['o', 'n'], ['p', 'o'], ['q', 'p'], ['r', 'q'], ['s', 'r'],
];
const relationships = new Map<Variable, Variable[]>();
for (const [target, prerequisite] of prerequisites) {
  const connected = relationships.get(prerequisite) ?? [];
  connected.push(target);
  relationships.set(prerequisite, connected);
}

const visitOrder: VariablePriority = (unassigned, assignments) => {
  let best = unassigned[0];
  if (best === undefined) return null;
  let bestRank = Number.NEGATIVE_INFINITY;
  for (const candidate of unassigned) {
    let rank = 0;
    for (const connected of relationships.get(candidate) ?? []) {
      const value = Object.hasOwn(assignments, connected) ? assignments[connected] : undefined;
      if (value === undefined) continue; // v1 checked Value.UNSET instead
      if (value === Value.TRUE) rank += 1;
      else if (value === Value.FALSE) rank = -unassigned.length;
    }
    if (rank > bestRank) {
      best = candidate;
      bestRank = rank;
    }
  }
  return [best, bestRank >= 1];
};

const expr = and(...prerequisites.map(([target, prerequisite]) => implies(target, prerequisite)));
const stats = createSolverStats();
const defaultResult = getSolution(expr, { assumptions: { h: Value.TRUE }, stats });
console.log(stats.decisions, stats.propagations, stats.conflicts); // 2 16 0
const guidedResult = getSolution(expr, {
  assumptions: { h: Value.TRUE },
  variablePriority: visitOrder,
});
console.log(defaultResult, guidedResult); // both 'sat'; their models satisfy the formula and have a,b,c,g,h = 1
```

Without a hook, unit propagation forces four variables from `h=TRUE`; index-ordered batch PLE assigns twelve more. The remaining named don't-cares `e` and `n` take **two ordinary decisions**. A supplied hook is called at those two decision points, not during the sixteen propagations. This is a deterministic work-count example, not an orders-of-magnitude timing claim.

## Migrating from v1 to v2

The formula constructors, `BooleanExpr`, `Value`, and complete numeric model shape are unchanged. Solving signatures are intentionally breaking in `2.0.0`; no legacy compatibility entry points remain.

| v1 symbol/signature | v2 migration |
| --- | --- |
| `getSolution(expr, initialAssignments?, selectNextVar?)` | `getSolution(expr, { assumptions, variablePriority })`. The second argument is an options object; the third positional argument is gone. |
| `initialAssignments` | Rename to `assumptions` inside options (or pass directly to `SatSolver.solve`). Pass known facts only; known `UNSET` entries are ignored. Assumptions now propagate, and unknown names/invalid values throw rather than acting as leaf filters. |
| `selectNextVar` | Rename and port to `variablePriority`: use the provided `unassigned` list and partial assignments; check `undefined` instead of `UNSET`. `null` now means defer to VSIDS. See the cadence/polarity contract above. |
| `SelectNextVariable` | Replace with the exported `VariablePriority` type. |
| `NextVariable` | Use `[Variable, boolean] \| null`, or `ReturnType<VariablePriority>`. The old type is removed. |
| `bruteForceAllSolutions(expr)` | Use `getAllSolutions(expr, options?)`; compare results as sets because order is unspecified. No eager `2^n` assignment array is constructed. |
| `getInitialAssignments(expr)` | Deleted. Omit assumptions or pass `{}` instead of building an UNSET-filled record. |
| `defaultSelect` (internal) | Removed; omit the hook or return `null` for the default VSIDS/phase-saving behavior. |
| `allPossibleAssignments`, `dpllSolution`, `sequence` (internal) | Removed with the brute-force implementation; use the public solving APIs, not internal helpers. |
| `expressionValue` (internal) | Retained only as a test-reference evaluator, not exported as a library API. |

`Variable` and `VariableAssignments` are now exported types, alongside `SolveOptions`, `SolverStats`, `VariablePriority`, and `SatSolver`. `getVariables`/`isVariable` remain internal, not new public helpers. Propagation, PLE, and retained heuristic state may change which valid first model is found; preserve forced-value/validity checks rather than depending on incidental v1 choices. JavaScript booleans are not numeric `Value` assignments even if a loose v1 test comparison accepted them.

The in-progress 3.0 API makes one further breaking change: every solving entry point returns a rich result object (`SolveResult`/`EnumerateResult`) instead of `model | null` or a bare model array, and `SatSolver.solve` takes an options bag — `solve(assumptions, { stats })` instead of `solve(assumptions, stats)`. UNSAT results carry a `core` of the failed assumptions used by the proof; stats out-parameters accept sparse objects and `createSolverStats()` returns a complete all-zero object. 3.0 also adds the cardinality constructors `atMostOne`/`atMost`/`atLeast`/`exactly`, the async entry points, and incremental `SatSolver.add` described above — purely additive on top of the v2 formula API.

## Environments

The runtime code is platform-neutral: it contains no `node:` imports, and its only `process` reference is a single guarded optional check, so the package imports cleanly under Node, in bundlers, and in **unbundled browser ESM** where the `process` global does not exist. Import only from the package root `@divmain/sat` — the `exports` map intentionally exposes no deep internal paths — and bundlers may tree-shake it (`sideEffects: false`).

Internal consistency audits (trail and conflict-analysis invariant checks) are **opt-in** and perform no work by default: set the `SAT_DEBUG` environment variable to `1` before the first import to enable them. The variable is read once at module load through the guarded access above; there is no public runtime toggle. The development test suite always runs with audits enabled.

The library makes **no wall-clock claims in any environment**: no timing, latency, or speedup figure is promised, and the test suite never asserts wall-clock times. Use the `SolverStats` counters to reason about the work performed. The async entry points yield through a platform-neutral chain — `scheduler.yield()`, then a `MessageChannel` post, then a zero-millisecond timer — with every platform global reached through `globalThis`; `yieldQuantum` is a work allowance, not a wall-time guarantee (browsers clamp nested timers to ~4 ms). The public declarations reference the ambient `AbortSignal` global: consumers compiling with `types: []` and no DOM lib must provide that ambient type themselves.

## Limits and Development

SAT still has exponential worst-case complexity. CDCL is not a polynomial-time guarantee, and enumeration can exhaust memory through its output and permanent blockers. The solver core is iterative, so search depth does not consume recursive JavaScript stack frames. **Variable collection and compilation recurse over expression nesting**: a pathologically deep constructor chain (for example, 100,000 nested `not`s) can overflow the stack before search starts. Flatten conjunctions/disjunctions where possible; do not interpret iterative search as unlimited input depth or memory. Internal consistency audits no longer run in the default runtime; they are opt-in via `SAT_DEBUG=1` (see [Environments](#environments)). No performance figure is attached to this change — audit cost depends on the workload, so measure your own.

For development, use a **full Git checkout with the pinned phase history**, not a shallow clone or source archive. Even `npm test` authenticates benchmark references in Git. Retain commits `7037f823d192dc3cf2dc9119c8063781e143113c` (Phase 1), `ade64e558ee47c60ae7b4b2cc29f861ccfb245cf` (Phase 2), and `53a059c761e9b3591b8513a03309699ecef0c889` (Phase 3). Missing history is an error, not grounds to substitute a local baseline. This is a test-tooling requirement, not a runtime dependency.

```bash
npm ci
npm test
npm run check
npm run build
npm run bench
```

- `npm test` runs the `node:test` suite via tsx and prints experimental coverage. The full enumeration stress has 59,049 models and can take several minutes; allow it to finish without reducing test sizes or budgets. Release validation explicitly checks at least **90% line coverage in each of `src/compile.ts` and `src/solver.ts`**; the reporter itself does not enforce a threshold. Unit tests use stats/validity oracles, never wall-clock assertions.
- `npm run check` checks Biome lint and formatting; `npm run fix` applies its fixes. `npm run build` emits ESM JavaScript, declarations, and self-contained source maps to `dist/`, with `.js` relative imports for NodeNext. Tests run through tsx and are not typechecked by that build; `npm run typecheck` strictly typechecks `src/` and `test/` separately from the build.
- `npm run bench` / `npm run bench:legacy` are **assert-only** verifications of the release implementation, not `createSolver` or enumeration benchmarks, and they **write nothing**. They authenticate the frozen Phase-1/2/3 evidence plus the Phase-4 record, report, and manifest at their pinned commit — including every embedded Phase-4 source fingerprint against those Git bytes — re-run all 8 fixtures, hash actual current source/fixture bytes, and independently check SAT models. Parity mode (the default until clause minimization) hard-fails unless all 48 recorded counters exactly match the frozen record; gates mode (`--gates`) keeps the same checks and prints non-fatal counter deltas. HEAD is context, not a substitute for source fingerprints.
- The eight benchmark fixtures are the hypergraph, PHP(5,4)/(6,5)/(7,6)/(8,7), and 20-variable/85-clause random 3-SAT with seeds 42/43/44. Original six-row conflict caps stay 200,000; the larger PHP caps stay **7,230/36,270**, from fixed historical calibrations. Exhaustion throws, never masquerades as UNSAT. These modest fixed cases do not establish general scalability, incremental speedups, default reduction engagement, or total-memory bounds.
- Counter ratios are not wall-time speedups. Phase 1 has completed small-PHP rows but **no** large-PHP measurements, not evidence of timeouts/infeasibility. The reports explicitly retain regressions as well as gains; Phase-3 restarts increased work on some PHP cases relative to Phase 2. See the [release validation review](test/phase4-benchmark-review.md) for actual results and limitations. Timing is console-only, not a test gate.
- Before packing, build from fresh source/install state: `tsc` does not remove stale `dist/` files, and `npm pack` does not build automatically. Use `npm pack --pack-destination <existing-scratch-directory>`, then install that tarball into a separate ESM consumer and run its README examples with plain Node and strict TypeScript. The package has zero runtime dependencies and intentionally no `engines` field; that is not a claim of testing every Node version.
