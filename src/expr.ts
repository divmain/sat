// Formula frontend: BooleanExpr AST types, constructors, and variable
// collection. Frozen by contract: it is the foundation of the public API, so
// changing this module's types breaks every consumer.

export type Variable = string;

// Numeric values are part of the frozen public contract; UNSET (-1) doubles
// as the solver's unassigned sentinel in its Int8Array assignment arrays.
export enum Value {
  UNSET = -1,
  FALSE = 0,
  TRUE = 1,
}

export type VariableAssignments = Record<Variable, Value>;

interface AndExpr {
  and: Array<Variable | BooleanExpr>;
}
interface OrExpr {
  or: Array<Variable | BooleanExpr>;
}
interface NotExpr {
  not: Variable | BooleanExpr;
}
// Cardinality nodes carry a bound `k` and an operand MULTISET: the payload is
// an ordered array in which repeated operands count repeatedly, so
// `exactly(1, 'a', 'a')` is UNSAT. See Design § Compiler (Cardinality
// constraints).
interface AtMostExpr {
  atMost: { k: number; exprs: Array<Variable | BooleanExpr> };
}
interface AtLeastExpr {
  atLeast: { k: number; exprs: Array<Variable | BooleanExpr> };
}
// A node is a bare string (a variable leaf) or an object carrying exactly one
// of the operator keys `and`/`or`/`not`/`atMost`/`atLeast`. Those keys are
// mutually exclusive, so `'and' in expr` / `'or' in expr` / `'not' in expr` /
// `'atMost' in expr` exhaustively dispatch; compound nodes may nest
// arbitrarily.
export type BooleanExpr = AndExpr | OrExpr | NotExpr | AtMostExpr | AtLeastExpr;

// All variables or subexpressions must be true.
export const and = (...exprs: Array<Variable | BooleanExpr>): BooleanExpr => ({ and: exprs });

// At least one variable or subexpression must be true.
export const or = (...exprs: Array<Variable | BooleanExpr>): BooleanExpr => ({ or: exprs });

// The specified variable or subexpression cannot be true.
export const not = (expr: Variable | BooleanExpr): BooleanExpr => ({ not: expr });

// If `a` is true then `b` must also be true. If `a` is false, `b` can be anything.
export const implies = (a: Variable | BooleanExpr, b: Variable | BooleanExpr): BooleanExpr =>
  or(not(a), b);

// Either `a` or `b` must be true, but not both.
export const xor = (a: Variable | BooleanExpr, b: Variable | BooleanExpr): BooleanExpr =>
  or(and(a, not(b)), and(not(a), b));

// Every cardinality bound is a non-negative safe integer; the constructors
// reject anything else with a descriptive Error. The compiler re-validates
// `k` and the payload shape, because consumers may hand-build AST nodes.
const validateCardinalityBound = (constructorName: string, k: number): void => {
  if (!Number.isSafeInteger(k) || k < 0) {
    throw new Error(
      `${constructorName} requires k to be a non-negative safe integer (got ${String(k)})`,
    );
  }
};

/**
 * At most one of the operands is true. Pure sugar for `atMost(1, ...)` — the
 * ASTs are identical and compilation dispatches on the node, never the
 * constructor. Operands form a multiset: repeated operands count repeatedly.
 */
export const atMostOne = (...exprs: Array<Variable | BooleanExpr>): BooleanExpr => ({
  atMost: { k: 1, exprs },
});

/**
 * At most `k` of the operands are true. `k` must be a non-negative safe
 * integer. Operands form a multiset: `atMost(1, 'a', 'a')` forces `a` false
 * (two occurrences of a true `a` already exceed the bound). Edge cases fold
 * to constants at compile time — `atMost(k >= n, ...)` is always true and
 * `atMost(0, ...)` asserts every operand false — and variables folded away
 * stay in the named universe. Prefer conjunctive placement (a top-level
 * conjunct of `and(...)`): conjunctive bounds compile to the compact
 * pairwise/sequential-counter encodings, while a nested occurrence is fully
 * reified through a totalizer, which is larger.
 */
export const atMost = (k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr => {
  validateCardinalityBound('atMost', k);
  return { atMost: { k, exprs } };
};

/**
 * At least `k` of the operands are true. `k` must be a non-negative safe
 * integer; the multiset and folding rules of `atMost` apply
 * (`atLeast(0, ...)` is always true, `atLeast(k > n, ...)` is always false).
 * Conjunctive occurrences compile as `atMost(n - k, ...)` over negated
 * operands; prefer conjunctive placement for the same reason as `atMost`.
 */
export const atLeast = (k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr => {
  validateCardinalityBound('atLeast', k);
  return { atLeast: { k, exprs } };
};

/** Exactly `k` of the operands are true: `atMost(k, ...)` and `atLeast(k, ...)`. */
export const exactly = (k: number, ...exprs: Array<Variable | BooleanExpr>): BooleanExpr =>
  and(atMost(k, ...exprs), atLeast(k, ...exprs));

// Strings are always variable leaves and compound nodes are always objects,
// so a typeof check alone tells them apart — the AST's whole disambiguation
// rule, relied on by the compiler.
export function isVariable(x: unknown): x is Variable {
  return typeof x === 'string';
}

// Accumulates into `variables` and returns it, so callers collect the
// variable set once per formula instead of merging per-subtree results;
// the recursion mirrors expression nesting. `visited` memoizes by object
// identity within one collection: a subtree shared by several parents (xor's
// duplicated operands, or an AST assembled with structural sharing) is
// traversed once, so collecting a left-deep xor chain is linear in the object
// graph instead of exponential in the chain length. The visited set is
// scoped to a single top-level call and never survives it, so mutating an
// AST between collections is always observed correctly.
export function getVariables(
  expr: BooleanExpr,
  variables = new Set<Variable>(),
  visited = new Set<BooleanExpr>(),
): Set<Variable> {
  if (visited.has(expr)) {
    return variables;
  }
  visited.add(expr);
  if ('and' in expr) {
    for (const subExpr of expr.and) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables, visited);
      }
    }
  } else if ('or' in expr) {
    for (const subExpr of expr.or) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables, visited);
      }
    }
  } else if ('not' in expr) {
    if (isVariable(expr.not)) {
      variables.add(expr.not);
    } else {
      getVariables(expr.not, variables, visited);
    }
  } else if ('atMost' in expr) {
    for (const subExpr of expr.atMost.exprs) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables, visited);
      }
    }
  } else if ('atLeast' in expr) {
    for (const subExpr of expr.atLeast.exprs) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables, visited);
      }
    }
  }
  return variables;
}
