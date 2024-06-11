type Variable = string;

export enum Value {
  UNSET = -1,
  FALSE = 0,
  TRUE = 1,
}

type VariableAssignments = Record<Variable, Value>;

interface AndExpr {
  and: Array<Variable | BooleanExpr>;
}
interface OrExpr {
  or: Array<Variable | BooleanExpr>;
}
interface NotExpr {
  not: Variable | BooleanExpr;
}
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

function sequence(len: number, start = 0) {
  const baseReturnValue = [...Array(len).keys()];
  return start ? baseReturnValue.map((val) => val + start) : baseReturnValue;
}

function isVariable(x: unknown): x is Variable {
  return typeof x === 'string';
}

function getVariables(expr: BooleanExpr, variables = new Set<Variable>()): Set<Variable> {
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

function expressionValue(expr: BooleanExpr | Variable, assignment: VariableAssignments): Value {
  if (isVariable(expr)) {
    return assignment[expr];
  }
  if ('and' in expr) {
    return expr.and.every((subExpr) => expressionValue(subExpr, assignment) === Value.TRUE)
      ? Value.TRUE
      : Value.FALSE;
  }
  if ('or' in expr) {
    return expr.or.some((subExpr) => expressionValue(subExpr, assignment) === Value.TRUE)
      ? Value.TRUE
      : Value.FALSE;
  }
  if ('not' in expr) {
    return expressionValue(expr.not, assignment) === Value.FALSE ? Value.TRUE : Value.FALSE;
  }
  throw new Error('Invalid BooleanExpr');
}

function allPossibleAssignments(variables: Array<Variable>): Array<VariableAssignments> {
  const numVars = variables.length;
  // The number of unique assignment configurations is equal to 2 ** numVars.
  return (
    sequence(2 ** numVars)
      // Transform each number into its stringified binary representation, e.g. '101'
      .map((num: number) => (num >>> 0).toString(2).padStart(numVars, '0'))
      // Transform each stringified binary into boolean[], e.g. [Value.TRUE, Value.FALSE, Value.TRUE]
      .map((binaryStr: string) =>
        binaryStr.split('').map((zeroOrOne) => (zeroOrOne !== '0' ? Value.TRUE : Value.FALSE)),
      )
      // Transform each boolean[] into is VariableAssignments counterpart, .e.g
      // {
      //   [variables[0]]: Value.TRUE,
      //   [variables[1]]: Value.FALSE,
      //   [variables[2]]: Value.TRUE,
      // }
      .map((boolAssignments) =>
        Object.fromEntries(boolAssignments.map((val, idx) => [variables[idx], val])),
      )
  );
}

// Generate an array of all solutions the satisfy all clauses.
export function bruteForceAllSolutions(expr: BooleanExpr): Array<VariableAssignments> {
  const solutions: VariableAssignments[] = [];
  for (const assignment of allPossibleAssignments([...getVariables(expr)])) {
    if (expressionValue(expr, assignment) === Value.TRUE) {
      solutions.push(assignment);
    }
  }
  return solutions;
}

export type NextVariable = [Variable, boolean] | null;
export type SelectNextVariable = (
  variables: Variable[],
  assignments: VariableAssignments,
) => NextVariable;

const defaultSelect: SelectNextVariable = (variables, assignments) => {
  const unassignedVar = variables.find((varName) => assignments[varName] === Value.UNSET);
  return unassignedVar ? [unassignedVar, false] : null;
};

export function getInitialAssignments(expr: BooleanExpr): VariableAssignments {
  const variables = Array.from(getVariables(expr));
  return Object.fromEntries(variables.map((variableName) => [variableName, Value.UNSET]));
}

function dpllSolution(
  expr: BooleanExpr,
  assignments: VariableAssignments,
  selectNextVar: SelectNextVariable,
): VariableAssignments | null {
  const variables = Array.from(getVariables(expr));

  const nextVar = selectNextVar(variables, assignments);
  if (!nextVar) {
    return expressionValue(expr, assignments) ? assignments : null;
  }
  const [unassignedVar, checkTrueFirst] = nextVar;

  const newAssignments: VariableAssignments = { ...assignments };

  newAssignments[unassignedVar] = checkTrueFirst ? Value.TRUE : Value.FALSE;
  const setTrueSolution = dpllSolution(expr, newAssignments, selectNextVar);
  if (setTrueSolution) {
    return setTrueSolution;
  }

  newAssignments[unassignedVar] = checkTrueFirst ? Value.FALSE : Value.TRUE;
  const setFalseSolution = dpllSolution(expr, newAssignments, selectNextVar);
  if (setFalseSolution) {
    return setFalseSolution;
  }

  return null;
}

// Find one solution that satisfies all clauses.
export function getSolution(
  expr: BooleanExpr,
  initialAssignments?: VariableAssignments,
  selectNextVar: SelectNextVariable = defaultSelect,
): VariableAssignments | null {
  initialAssignments = { ...getInitialAssignments(expr), ...initialAssignments };
  return dpllSolution(expr, initialAssignments, selectNextVar);
}
