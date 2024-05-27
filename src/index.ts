type Variable = string;

type VariableConfiguration = Record<Variable, boolean>;

interface AndExpr {
  and: Array<Variable | BooleanExpr>;
}
interface OrExpr {
  or: Array<Variable | BooleanExpr>;
}
interface NotExpr {
  not: Variable | BooleanExpr;
}
type BooleanExpr = AndExpr | OrExpr | NotExpr;

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

function expressionIsTrue(
  expr: BooleanExpr | Variable,
  assignment: VariableConfiguration,
): boolean {
  if (isVariable(expr)) {
    return assignment[expr];
  }
  if ('and' in expr) {
    return expr.and.every((subExpr) => expressionIsTrue(subExpr, assignment));
  }
  if ('or' in expr) {
    return expr.or.some((subExpr) => expressionIsTrue(subExpr, assignment));
  }
  if ('not' in expr) {
    return !expressionIsTrue(expr.not, assignment);
  }
  throw new Error('Invalid BooleanExpr');
}

function allPossibleAssignments(variables: Array<Variable>): Array<VariableConfiguration> {
  const numVars = variables.length;
  // The number of unique assignment configurations is equal to 2 ** numVars.
  return (
    sequence(2 ** numVars)
      // Transform each number into its stringified binary representation, e.g. '101'
      .map((num: number) => (num >>> 0).toString(2).padStart(numVars, '0'))
      // Transform each stringified binary into boolean[], e.g. [true, false, true]
      .map((binaryStr: string) => binaryStr.split('').map((zeroOrOne) => zeroOrOne !== '0'))
      // Transform each boolean[] into is VariableConfiguration counterpart, .e.g
      // {
      //   [variables[0]]: true,
      //   [variables[1]]: false,
      //   [variables[2]]: true,
      // }
      .map((boolAssignments) =>
        Object.fromEntries(boolAssignments.map((val, idx) => [variables[idx], val])),
      )
  );
}

// Generate an array of all solutions the satisfy all clauses.
export function bruteForceAllSolutions(expr: BooleanExpr): Array<VariableConfiguration> {
  const solutions: VariableConfiguration[] = [];
  for (const assignment of allPossibleAssignments([...getVariables(expr)])) {
    if (expressionIsTrue(expr, assignment)) {
      solutions.push(assignment);
    }
  }
  return solutions;
}

// Find one solution that satisfies all clauses.
export function getDpllSolution(
  expr: BooleanExpr,
  assignment: VariableConfiguration = {},
): VariableConfiguration | null {
  const variables = getVariables(expr);

  const unassignedVars = Array.from(variables).filter((v) => !(v in assignment));
  if (unassignedVars.length === 0) {
    return expressionIsTrue(expr, assignment) ? assignment : null;
  }

  const varToTry = unassignedVars[0];

  // Try assigning True to the first unassigned variable.
  const newAssignmentTrue: VariableConfiguration = { ...assignment, [varToTry]: true };
  const setTrueSolution = getDpllSolution(expr, newAssignmentTrue);
  if (setTrueSolution) {
    return setTrueSolution;
  }

  // Try assigning False to the first unassigned variable.
  const newAssignmentFalse: VariableConfiguration = { ...assignment, [varToTry]: false };
  const setFalseSolution = getDpllSolution(expr, newAssignmentFalse);
  if (setFalseSolution) {
    return setFalseSolution;
  }

  return null;
}
