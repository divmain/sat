# @divmain/sat, a SAT solver library

This library provides tools for solving Boolean satisfiability problems (SAT). It includes functions for generating all solutions to a given problem and for finding a single solution using the DPLL algorithm.

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

The library can be inported like so:

```typescript
import {
  and,
  or,
  not,
  implies,
  xor,
  bruteForceAllSolutions,
  getSolution,
} from '@divmain/sat';
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

### Finding All Solutions

To find all solutions to a given Boolean expression, use `bruteForceAllSolutions`:

```typescript
const expr = and(
  not('b'),
  or('a', 'b'),
  xor('b', 'c'),
  implies('c', and('d', 'e')),
);
const solutions = bruteForceAllSolutions(expr);
console.log(solutions);
// [
//   {
//     b: 0,
//     a: 1,
//     c: 1,
//     d: 1,
//     e: 1
//   }
// ]
```

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
//   b: 0,
//   a: 1,
//   c: 1,
//   d: 1,
//   e: 1
// }
```

## API

### `bruteForceAllSolutions(expression)`

Returns all possible assignments that satisfy the given Boolean expression.

- `expr`: a Boolean expression constructed using `and`, `or`, `not`, `implies`, and `xor`.
- returns an array of objects representing all satisfying assignments.

### `getSolution(expression, initialAssignments?, selectNextVar?):`

Finds a single solution using the DPLL algorithm.

- `expr`: a Boolean expression constructed using and, or, not, implies, and xor.
- `initialAssignments` (optional): initial assignments for the variables.
- `selectNextVar` (optional): a custom function to select the next variable to assign.
- returns an object representing a satisfying assignment, or `null` if no solution exists.

### Improving Performance with Variable Selection Heuristic

Computing a solution for complex boolean expressions can be computationally expensive. By default, the DPLL algorithm undergirding `getSolution` will recursively select variables & assign them values, doing so until all variables have a True or False assignment, and finally checking the assignments for validity against the provided boolean clause. The variable selection process is mostly random.

However, if you have some knowledge about your problem space, you may be able to significantly improve the performance of `getSolution` by providing a custom variable selection heuristic through the `selectNextVar` argument. This allows you to guide the search process by selecting which variable to assign next, potentially reducing the number of recursive calls and speeding up the solution finding process. This speedup can be multiple orders of magnitude.

The `selectNextVar` function should follow this signature:

```typescript
type SelectNextVariable = (variables: Variable[], assignments: VariableAssignments) => NextVariable;
type NextVariable = [Variable, boolean] | null;
type Variable = string;
````

- `variables`: An array of all variables in the Boolean expression.
- `assignments`: The current assignments of variables.
- returns `null` if no variables are left to assign, otherwise a tuple containing the next variable to assign and a boolean indicating whether to assign TRUE first.

#### Example

```typescript
const selectNextVar: SelectNextVariable = (variables, assignments) => {
  // Select the first unassigned variable
  const unassignedVar = variables.find((varName) => assignments[varName] === Value.UNSET);
  // If there are no unassigned variables, return null
  if (!unassignedVar) return null;
  // Return the variable and specify to check TRUE first
  return [unassignedVar, true];
};

const expr = and('a', or('b', not('c')));
const solution = getSolution(expr, {}, selectNextVar);
console.log(solution);
````
