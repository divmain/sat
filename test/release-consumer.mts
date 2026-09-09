// Compiled against the installed declarations, with types: [] and no skipLibCheck.
import * as sat from '@divmain/sat';
import type {
  BooleanExpr,
  SatSolver,
  SolveOptions,
  SolverStats,
  Variable,
  VariableAssignments,
  VariablePriority,
} from '@divmain/sat';

const variable: Variable = 'typed';
const assumptions: VariableAssignments = { [variable]: sat.Value.TRUE };
const stats: SolverStats = {
  decisions: 0,
  propagations: 0,
  conflicts: 0,
  restarts: 0,
  learnedClauses: 0,
  learnedClausesCurrent: 0,
  learnedLiterals: 0,
  minimizedLiterals: 0,
};
const priority: VariablePriority = (unassigned, partial) => {
  const first = unassigned[0];
  if (first === undefined) return null;
  const assigned: sat.Value | undefined = Object.hasOwn(partial, first)
    ? partial[first]
    : undefined;
  if (assigned !== undefined) throw new Error('Hook received an assigned candidate');
  return [first, true];
};
const expr: BooleanExpr = sat.and(
  sat.or(variable, 'other'),
  sat.not('off'),
  sat.implies(variable, 'other'),
  sat.xor('left', 'right'),
);
const options: SolveOptions = { assumptions, variablePriority: priority, stats };
const forwarded: SolveOptions = {
  assumptions: options.assumptions,
  variablePriority: options.variablePriority,
  stats: options.stats,
};
const solver: SatSolver = sat.createSolver(expr, { variablePriority: options.variablePriority });
const single: VariableAssignments | null = sat.getSolution(expr, forwarded);
const all: VariableAssignments[] = sat.getAllSolutions(expr, options);
const incremental: VariableAssignments | null = solver.solve(assumptions, stats);
const models = [single, ...all, incremental];
if (all.length !== 2) throw new Error('Typed enumeration should contain both XOR models');
for (const model of models) {
  if (model === null) throw new Error('Typed consumer expected SAT');
  if (Object.keys(model).sort().join(',') !== 'left,off,other,right,typed') {
    throw new Error('Typed model keys changed');
  }
  if (model.typed !== 1 || model.other !== 1 || model.off !== 0 || model.left + model.right !== 1) {
    throw new Error('Typed model violates the formula/assumption');
  }
}
const omitted: SolveOptions = {
  assumptions: undefined,
  variablePriority: undefined,
  stats: undefined,
};
if (sat.getSolution(sat.and(), omitted) === null) throw new Error('Empty conjunction must be SAT');
if (sat.createSolver(sat.or(), { variablePriority: undefined }).solve(undefined, stats) !== null) {
  throw new Error('Empty disjunction must be UNSAT');
}
if (solver.solve({ typed: sat.Value.UNSET }) === null)
  throw new Error('Known UNSET must be ignored');

// Never invoked. Every directive must suppress a real error (unused directives
// fail tsc); all referenced bindings are used so noUnused cannot mask a removal.
function rejectedContracts(): void {
  // @ts-expect-error v1's third positional argument is removed.
  sat.getSolution(expr, assumptions, priority);
  // @ts-expect-error v1's positional assignment record is not SolveOptions.
  sat.getSolution(expr, { typed: sat.Value.TRUE });
  // @ts-expect-error Enumeration also uses an options object, not three arguments.
  sat.getAllSolutions(expr, assumptions, priority);
  // @ts-expect-error Rename initialAssignments to assumptions.
  sat.getSolution(expr, { initialAssignments: assumptions });
  // @ts-expect-error Rename selectNextVar to variablePriority.
  sat.getSolution(expr, { selectNextVar: priority });
  // @ts-expect-error Numeric Value assignments, not booleans, in single-shot calls.
  sat.getSolution(expr, { assumptions: { typed: true } });
  // @ts-expect-error Numeric Value assignments, not booleans, in enumeration.
  sat.getAllSolutions(expr, { assumptions: { typed: false } });
  // @ts-expect-error Numeric Value assignments, not booleans, in incremental calls.
  solver.solve({ typed: true });
  // @ts-expect-error Polarity is boolean, not numeric Value.
  sat.getSolution(expr, { variablePriority: () => ['typed', sat.Value.TRUE] });
  // @ts-expect-error The stats out-parameter requires all eight writable fields.
  sat.getSolution(expr, { stats: { decisions: 0 } });
  // @ts-expect-error Constructors are required at solving entry points.
  sat.getSolution('typed');
  // @ts-expect-error Factory options do not accept per-call assumptions.
  sat.createSolver(expr, { assumptions });
  // @ts-expect-error Factory options do not accept per-call stats.
  sat.createSolver(expr, { stats });
  // @ts-expect-error PLE is internal, not a public single-shot knob.
  sat.getSolution(expr, { enablePle: false });
  // @ts-expect-error Conflict caps are internal.
  sat.getSolution(expr, { maxConflicts: 1 });
  // @ts-expect-error Restart budgets are internal.
  sat.getSolution(expr, { restartBaseConflicts: 1 });
  // @ts-expect-error Learned-clause reduction thresholds are internal.
  sat.getSolution(expr, { learnedClauseReductionThreshold: 1 });
  // @ts-expect-error Enumeration must not expose PLE.
  sat.getAllSolutions(expr, { enablePle: true });
  // @ts-expect-error Reusable solvers must not expose PLE.
  sat.createSolver(expr, { enablePle: true });
  // @ts-expect-error Reusable solvers must not expose internal conflict caps.
  sat.createSolver(expr, { maxConflicts: 1 });
  // @ts-expect-error No public clause insertion method.
  solver.addClause([]);
  // @ts-expect-error Old callback type is removed.
  type OldPriority = import('@divmain/sat').SelectNextVariable;
  // @ts-expect-error Old callback result type is removed.
  type OldNext = import('@divmain/sat').NextVariable;
  // @ts-expect-error Compiler representation is not a root type export.
  type InternalCnf = import('@divmain/sat').CompiledCnf;
  // @ts-expect-error Clause representation is not a root type export.
  type InternalClause = import('@divmain/sat').Clause;
  const removedTypes: [OldPriority, OldNext, InternalCnf, InternalClause] | null = null;
  void removedTypes;
  // @ts-expect-error No default export.
  void sat.default;
  // @ts-expect-error No old enumeration helper.
  void sat.bruteForceAllSolutions;
  // @ts-expect-error No old assignment initializer.
  void sat.getInitialAssignments;
  // @ts-expect-error No old selection helper.
  void sat.defaultSelect;
  // @ts-expect-error No old brute-force helper.
  void sat.allPossibleAssignments;
  // @ts-expect-error No old DPLL entry point.
  void sat.dpllSolution;
  // @ts-expect-error No old sequence helper.
  void sat.sequence;
  // @ts-expect-error The reference evaluator is test-internal.
  void sat.expressionValue;
  // @ts-expect-error Variable collection stays internal.
  void sat.getVariables;
  // @ts-expect-error Variable discrimination stays internal.
  void sat.isVariable;
  // @ts-expect-error Instrumentation stays internal.
  void sat.compileCount;
  // @ts-expect-error The compiler stays internal.
  void sat.compile;
  // @ts-expect-error The CDCL class stays internal.
  void sat.Solver;
  // @ts-expect-error DIMACS tooling stays internal.
  void sat.parseDimacs;
}
void rejectedContracts;

console.log(
  JSON.stringify(
    {
      status: 'passed',
      types: [
        'BooleanExpr',
        'SatSolver',
        'SolveOptions',
        'SolverStats',
        'Variable',
        'VariableAssignments',
        'VariablePriority',
      ],
      models,
    },
    null,
    2,
  ),
);
