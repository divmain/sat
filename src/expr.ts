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
// A node is a bare string (a variable leaf) or an object carrying exactly one
// of the operator keys `and`/`or`/`not`. Those keys are mutually exclusive,
// so `'and' in expr` / `'or' in expr` / `'not' in expr` exhaustively dispatch;
// compound nodes may nest arbitrarily.
export type BooleanExpr = AndExpr | OrExpr | NotExpr;

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

// Strings are always variable leaves and compound nodes are always objects,
// so a typeof check alone tells them apart — the AST's whole disambiguation
// rule, relied on by the compiler.
export function isVariable(x: unknown): x is Variable {
  return typeof x === 'string';
}

// Accumulates into `variables` and returns it, so callers collect the
// variable set once per formula instead of merging per-subtree results;
// the recursion mirrors expression nesting.
export function getVariables(expr: BooleanExpr, variables = new Set<Variable>()): Set<Variable> {
  if ('and' in expr) {
    for (const subExpr of expr.and) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables);
      }
    }
  } else if ('or' in expr) {
    for (const subExpr of expr.or) {
      if (isVariable(subExpr)) {
        variables.add(subExpr);
      } else {
        getVariables(subExpr, variables);
      }
    }
  } else if ('not' in expr) {
    if (isVariable(expr.not)) {
      variables.add(expr.not);
    } else {
      getVariables(expr.not, variables);
    }
  }
  return variables;
}
