# @divmain/sat, a SAT solver library

This library provides tools for solving Boolean satisfiability problems (SAT). It includes functions for finding a single solution using a CDCL-style solver (v2). Model enumeration (`getAllSolutions`) and incremental solving (`createSolver`) arrive in upcoming releases.

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

The library can be imported like so:

```typescript
import {
  and,
  or,
  not,
  implies,
  xor,
  Value,
  getSolution,
} from '@divmain/sat';
import type { SolveOptions } from '@divmain/sat';
```

### Boolean Expressions

This library provides helper functions to construct Boolean expressions:

- `and(...exprs)`: All variables or subexpressions must be true.
- `or(...exprs)`: At least one variable or subexpression must be true.
- `not(expr)`: The specified variable or subexpression cannot be true.
- `implies(first, second)`: If `first` is true then `second` must also be true. If `first` is false, `second` can be true or false.
- `xor(first, second)`: Either `first` or `second` must be true, but not both.

In the above function signatures, both variables (strings) and other expressions can be provided wherever an expression is expected.

## Example

### Finding a Single Solution

To find a single solution, use `getSolution`:

```typescript
const expr = and(
  not('b'),
  or('a', 'b'),
  xor('b', 'c'),
  implies('c', and('d', 'e')),
);
const solution = getSolution(expr);
console.log(solution);
// {
//   a: 1,
//   b: 0,
//   c: 1,
//   d: 1,
//   e: 1
// }
```

### Guiding the Search

When a solution is returned, every named variable is assigned (`Value.TRUE` or `Value.FALSE`); `null` means the formula is unsatisfiable. Assumptions are passed via the options object and are propagated immediately (an inconsistent assumption set yields `null` fast). A custom branching heuristic can be supplied through `variablePriority`:

```typescript
import { getSolution, implies, Value } from '@divmain/sat';
import type { VariablePriority } from '@divmain/sat';

// Branch a=TRUE first; called only when the solver needs a decision.
const priority: VariablePriority = (unassigned, assignments) => {
  if (unassigned.includes('a')) return ['a', true];
  return null; // defer to the default heuristic
};

const solution = getSolution(implies('a', 'b'), {
  assumptions: { a: Value.TRUE },
  variablePriority: priority,
});
```

## API

### `getSolution(expression, options?)`

Finds a single satisfying assignment using a CDCL-style solver (iterative search with unit propagation and scoped pure-literal elimination).

- `expr`: a Boolean expression constructed using `and`, `or`, `not`, `implies`, and `xor`.
- `options` (optional): a `SolveOptions` object:
  - `assumptions` (optional): a partial assignment of `Variable` → `Value` describing known facts. Unknown variable names throw a descriptive `Error`; `Value.UNSET` entries are ignored; any other value throws. Assumptions propagate immediately, so a set inconsistent with the formula yields `null`.
  - `variablePriority` (optional): a custom decision heuristic with signature `(unassigned: Variable[], assignments: Partial<Record<Variable, Value>>) => [Variable, boolean] | null`. It is called only when the solver needs a decision; returning `null` defers to the default heuristic. The returned variable must still be unassigned (unknown or already-assigned picks are ignored).
  - `stats` (optional): an out-param `SolverStats` object corresponding to `{ decisions, propagations, conflicts, restarts, learnedClauses, learnedClausesCurrent }`; it is zeroed by the callee and then populated with the call's statistics.
- returns an object representing a satisfying assignment (every named variable present, no auxiliary variables), or `null` if no solution exists.

Empty formulas follow v1 semantics: `getSolution(and())` returns `{}` and `getSolution(or())` returns `null`.

### Removed in v2

The following v1 symbols were removed: `bruteForceAllSolutions`, `getInitialAssignments`, `selectNextVar` (and the `SelectNextVariable`/`NextVariable` types). `getAllSolutions` replaces brute-force enumeration in an upcoming release; the v2 API will also gain `createSolver` for incremental solving.
