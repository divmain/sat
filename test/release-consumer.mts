// Compiled against the installed declarations, with types: [] and no skipLibCheck.
import * as sat from '@divmain/sat';
import type {
  AsyncSolveOptions,
  BooleanExpr,
  EnumerateResult,
  SatSolver,
  SatSolverAsyncOptions,
  SatSolverCallOptions,
  SolveOptions,
  SolveResult,
  SolverStats,
  SolverStatsInput,
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
const zeroed: SolverStats = sat.createSolverStats();
if (Object.values(zeroed).some((counter) => counter !== 0)) {
  throw new Error('createSolverStats must be complete and all-zero');
}
const sparse: SolverStatsInput = { decisions: 7 };
sat.getSolution(sat.and('ready'), { stats: sparse });
if (sparse.decisions !== 0 || sparse.propagations !== 1) {
  throw new Error('Sparse inputs must be zero-filled, then populated');
}
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
const callOptions: SatSolverCallOptions = { stats };
const single: SolveResult = sat.getSolution(expr, forwarded);
const all: EnumerateResult = sat.getAllSolutions(expr, options);
if (all.status !== 'complete') throw new Error('Enumeration must complete without budgets');
const incremental: SolveResult = solver.solve(assumptions, callOptions);
const results = [single, incremental];
if (all.models.length !== 2) throw new Error('Typed enumeration should contain both XOR models');
for (const model of all.models) {
  if (Object.keys(model).sort().join(',') !== 'left,off,other,right,typed') {
    throw new Error('Typed model keys changed');
  }
}
for (const result of results) {
  if (result.status !== 'sat') throw new Error('Typed consumer expected SAT');
  const model = result.model;
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
if (sat.getSolution(sat.and(), omitted).status !== 'sat') {
  throw new Error('Empty conjunction must be SAT');
}
const emptyDisjunction = sat
  .createSolver(sat.or(), { variablePriority: undefined })
  .solve(undefined, { stats });
if (emptyDisjunction.status !== 'unsat') throw new Error('Empty disjunction must be UNSAT');
// No assumptions were supplied: the only sound core is the empty one.
if (Object.keys(emptyDisjunction.core).length !== 0) {
  throw new Error('Assumption-independent UNSAT must core on {}');
}
if (solver.solve({ typed: sat.Value.UNSET }).status !== 'sat') {
  throw new Error('Known UNSET must be ignored');
}
// Sparse out-params are zero-filled, then every field is populated.
const filled: SolverStatsInput = {};
sat.getSolution(sat.and('a'), { stats: filled });
const filledComplete: SolverStats = filled as SolverStats;
if (filledComplete.propagations !== 1) throw new Error('Sparse stats must be zero-filled');

// Async entry points are first-class and typed: real yields at the minimum
// quantum, per-call budgets, and pre-aborted signal handling.
const asyncSingle: SolveResult = await sat.getSolutionAsync(expr, {
  assumptions,
  conflictBudget: 10_000,
  yieldQuantum: 64,
} satisfies AsyncSolveOptions);
if (asyncSingle.status !== 'sat') throw new Error('Typed async solve expected SAT');
if (asyncSingle.model.typed !== 1 || asyncSingle.model.other !== 1) {
  throw new Error('Typed async model violates the formula/assumption');
}
const asyncAll: EnumerateResult = await sat.getAllSolutionsAsync(expr, {
  assumptions,
  conflictBudget: 100_000,
} satisfies AsyncSolveOptions);
if (asyncAll.status !== 'complete' || asyncAll.models.length !== 2) {
  throw new Error('Typed async enumeration should contain both XOR models');
}
const asyncCallOptions = {
  stats,
  conflictBudget: 10_000,
  yieldQuantum: 64,
} satisfies SatSolverAsyncOptions;
const asyncIncremental: SolveResult = await solver.solveAsync(assumptions, asyncCallOptions);
if (asyncIncremental.status !== 'sat') throw new Error('Typed async incremental expected SAT');
const budgetedSync: SolveResult = sat.getSolution(expr, { conflictBudget: 0 });
if (budgetedSync.status !== 'unknown' || budgetedSync.reason !== 'conflictBudget') {
  throw new Error('A zero budget must answer unknown, never a verdict');
}
const preAborted = new AbortController();
preAborted.abort();
const aborted: SolveResult = await sat.getSolutionAsync(expr, { signal: preAborted.signal });
if (aborted.status !== 'unknown' || aborted.reason !== 'aborted') {
  throw new Error('A pre-aborted signal must answer unknown/aborted');
}

// Incremental addition is first-class and typed: `add` takes a BooleanExpr
// and `variables` returns the globally sorted named set.
solver.add(sat.and('added'));
const knownVariables: Variable[] = solver.variables();
if (knownVariables.join(',') !== 'added,left,off,other,right,typed') {
  throw new Error('variables() must be globally sorted across adds');
}
const afterAdd: SolveResult = solver.solve({ added: sat.Value.TRUE }, callOptions);
if (afterAdd.status !== 'sat' || afterAdd.model.added !== 1) {
  throw new Error('A newly added name must be a valid assumption and model key');
}

// Cardinality constructors are first-class and typed; operands form a
// multiset and the bound is a non-negative safe-integer number.
const card: BooleanExpr = sat.and(
  sat.exactly(1, 'card-a', 'card-b'),
  sat.atMostOne('card-c', 'card-d'),
  sat.atMost(1, 'card-a', 'card-e'),
  sat.atLeast(1, 'card-c', 'card-d', 'card-e'),
);
const cardSingle: SolveResult = sat.getSolution(card);
if (cardSingle.status !== 'sat') throw new Error('Typed cardinality solve expected SAT');
const cardAll: EnumerateResult = sat.getAllSolutions(card);
if (cardAll.status !== 'complete') throw new Error('Typed cardinality enumeration must complete');
// Hand-computed: exactly-one(a,b) × atMostOne(c,d) × atMost(1,a,e) ×
// atLeast(1,c,d,e) has 7 models (2 with card-a set, 5 with card-b set).
if (cardAll.models.length !== 7) throw new Error('Typed cardinality enumeration count changed');
for (const model of cardAll.models) {
  const on = (name: string): number => model[name] ?? -1;
  const valid =
    on('card-a') + on('card-b') === 1 &&
    on('card-c') + on('card-d') <= 1 &&
    on('card-a') + on('card-e') <= 1 &&
    on('card-c') + on('card-d') + on('card-e') >= 1;
  if (!valid) throw new Error('Typed cardinality model violates a constraint');
}
// The incremental path accepts cardinality batches too.
solver.add(sat.atLeast(1, 'added', 'typed'));
if (solver.solve({ typed: sat.Value.FALSE }, callOptions).status !== 'sat') {
  throw new Error('A cardinality batch must join the incremental handle');
}

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
  // @ts-expect-error Stats fields are numeric counters.
  sat.getSolution(expr, { stats: { decisions: '0' } });
  // @ts-expect-error Cardinality bounds are numbers, not strings.
  sat.atMost('1', 'a');
  // @ts-expect-error The options bag holds `stats`; a bare stats object is not the bag.
  solver.solve(assumptions, stats);
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
  // @ts-expect-error yieldQuantum is an async-only scheduling option.
  sat.getSolution(expr, { yieldQuantum: 64 });
  // @ts-expect-error Abort signals exist only on the async options.
  sat.getSolution(expr, { signal: undefined });
  // @ts-expect-error The sync call options bag has no scheduling slots.
  solver.solve(assumptions, { yieldQuantum: 64 });
  // @ts-expect-error The sync call options bag has no signal slot.
  solver.solve(assumptions, { signal: undefined });
  // @ts-expect-error Enumeration must not expose PLE.
  sat.getAllSolutions(expr, { enablePle: true });
  // @ts-expect-error Reusable solvers must not expose PLE.
  sat.createSolver(expr, { enablePle: true });
  // @ts-expect-error Reusable solvers must not expose internal conflict caps.
  sat.createSolver(expr, { maxConflicts: 1 });
  // @ts-expect-error The factory options bag has no budget slot; budgets are per-call.
  sat.createSolver(expr, { conflictBudget: 1 });
  // @ts-expect-error No raw-clause insertion method (add takes a BooleanExpr).
  solver.addClause([]);
  // @ts-expect-error add() requires a BooleanExpr, not a bare variable.
  solver.add('typed');
  // @ts-expect-error add() requires an argument.
  solver.add();
  // @ts-expect-error variables() takes no arguments.
  solver.variables(expr);
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
        'AsyncSolveOptions',
        'BooleanExpr',
        'EnumerateResult',
        'SatSolver',
        'SatSolverAsyncOptions',
        'SatSolverCallOptions',
        'SolveOptions',
        'SolveResult',
        'SolverStats',
        'SolverStatsInput',
        'Variable',
        'VariableAssignments',
        'VariablePriority',
      ],
      results,
    },
    null,
    2,
  ),
);
