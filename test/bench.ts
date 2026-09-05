// Benchmark runner (npm run bench) — NOT part of npm test. Phase-1 baseline:
// hypergraph, pigeon-hole PHP(5,4)/PHP(6,5), and seeded random 3-SAT. Every
// run is bounded by maxConflicts (a budget exhaustion throws instead of
// silently reporting UNSAT — see Design § Solver Core "maxConflicts knob"),
// and the phase's stats are recorded to test/baseline.json for
// phase-over-phase comparison. The recorded schema is stats only (no models):
// { decisions, propagations, conflicts, restarts, learnedClauses } per
// instance; wall time is printed but deliberately not recorded (benchmarks
// are inspected manually and never gate unit tests).
//
// Phase-1 implementation notes:
//   - Bench runs mirror the single-shot getSolution path (enablePle: true)
//     but construct the internal Solver directly so every run carries the
//     maxConflicts bound; the public API has no conflict-budget knob.
//   - PHP sizes are capped at DPLL-feasible sizes (PHP(5,4), PHP(6,5)):
//     pigeon-hole is exponentially hard for resolution-based methods, so this
//     is a regression gate, not a scalability demo.
//   - Random 3-SAT uses the fixed-width generator over 20 variables / 85
//     clauses (ratio ≈ 4.25, the phase transition) under fixed seeds; results
//     are deterministic across runs and phases.

import { readFileSync, writeFileSync } from 'node:fs';
import { performance } from 'node:perf_hooks';
import { compile } from '../src/compile.js';
import { Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import { cnfToExpr, hypergraphFormula, mulberry32, phpCnf, random3Cnf } from './helpers.js';

// Config -------------------------------------------------------------------

const MAX_CONFLICTS = 200_000;
const BASELINE_URL = new URL('./baseline.json', import.meta.url);

const SAT3_SEEDS: readonly number[] = [42, 43, 44];
const SAT3_VARS = 20;
const SAT3_CLAUSES = 85;

// A recorded benchmark entry: stats only, no models (Design § Testing).
interface BaselineEntry {
  decisions: number;
  propagations: number;
  conflicts: number;
  restarts: number;
  learnedClauses: number;
}

interface RunResult extends BaselineEntry {
  sat: boolean;
  wallMs: number;
}

const entryOf = (stats: SolverStats): BaselineEntry => ({
  decisions: stats.decisions,
  propagations: stats.propagations,
  conflicts: stats.conflicts,
  restarts: stats.restarts,
  learnedClauses: stats.learnedClauses,
});

// Mirror the single-shot getSolution path (PLE enabled) with a conflict
// budget bounding every run.
function runInstance(
  name: string,
  expr: BooleanExpr,
  assumptions: VariableAssignments | undefined,
): RunResult {
  const stats: SolverStats = {
    decisions: 0,
    propagations: 0,
    conflicts: 0,
    restarts: 0,
    learnedClauses: 0,
    learnedClausesCurrent: 0,
  };
  const start = performance.now();
  const solver = new Solver(compile(expr), {
    assumptions,
    enablePle: true,
    stats,
    maxConflicts: MAX_CONFLICTS,
  });
  const sat = solver.solve();
  const wallMs = performance.now() - start;
  return { sat, ...entryOf(stats), wallMs };
}

// Instances -----------------------------------------------------------------

const instances: ReadonlyArray<{ name: string; build: () => RunResult }> = [
  {
    name: 'hypergraph',
    build: () => runInstance('hypergraph', hypergraphFormula(), { h: Value.TRUE }),
  },
  {
    name: 'php_5_4',
    build: () => runInstance('php_5_4', cnfToExpr(phpCnf(5, 4)), undefined),
  },
  {
    name: 'php_6_5',
    build: () => runInstance('php_6_5', cnfToExpr(phpCnf(6, 5)), undefined),
  },
  ...SAT3_SEEDS.map((seed) => ({
    name: `sat3_seed${seed}`,
    build: () =>
      runInstance(
        `sat3_seed${seed}`,
        cnfToExpr(random3Cnf(mulberry32(seed), SAT3_VARS, SAT3_CLAUSES)),
        undefined,
      ),
  })),
];

// Report --------------------------------------------------------------------

const printTable = (results: ReadonlyArray<{ name: string; result: RunResult }>): void => {
  const header = [
    'instance',
    'verdict',
    'decisions',
    'propagations',
    'conflicts',
    'restarts',
    'learned',
    'wall ms',
  ];
  const cells = (result: RunResult): string[] => [
    result.sat ? 'SAT' : 'UNSAT',
    String(result.decisions),
    String(result.propagations),
    String(result.conflicts),
    String(result.restarts),
    String(result.learnedClauses),
    result.wallMs.toFixed(2),
  ];
  const widths = header.map((h, column) =>
    Math.max(
      h.length,
      ...results.map(({ name, result }) =>
        column === 0 ? name.length : cells(result)[column - 1].length,
      ),
    ),
  );
  const row = (cellsList: string[]): string =>
    cellsList
      .map((cell, column) => cell.padStart(column === 1 ? widths[column] + 8 : widths[column]))
      .join('  ');
  console.log(row(header));
  for (const { name, result } of results) {
    console.log(row([name, ...cells(result)]));
  }
};

const printComparison = (
  results: ReadonlyArray<{ name: string; result: RunResult }>,
  previous: Record<string, BaselineEntry>,
): void => {
  console.log('\nphase-over-phase comparison vs the previously recorded baseline (stats only):');
  for (const { name, result } of results) {
    const before = previous[name];
    if (before === undefined) {
      console.log(`  ${name}: no previous entry`);
      continue;
    }
    const deltas: string[] = [];
    for (const key of [
      'decisions',
      'propagations',
      'conflicts',
      'restarts',
      'learnedClauses',
    ] as const) {
      const delta = result[key] - before[key];
      deltas.push(`${key} ${delta >= 0 ? '+' : ''}${delta}`);
    }
    console.log(`  ${name}: ${deltas.join(', ')}`);
  }
};

const loadPrevious = (): Record<string, BaselineEntry> | null => {
  try {
    return JSON.parse(readFileSync(BASELINE_URL, 'utf8')) as Record<string, BaselineEntry>;
  } catch {
    return null; // no baseline checked in yet (Phase-1 first run)
  }
};

// run -----------------------------------------------------------------------

const results = instances.map(({ name, build }) => ({ name, result: build() }));

console.log('Phase-1 benchmark (stats are deterministic under fixed seeds)...\n');
printTable(results);

const previous = loadPrevious();
if (previous !== null) {
  printComparison(results, previous);
} else {
  console.log('\nno previous baseline found — recording the Phase-1 baseline.');
}

const baseline: Record<string, BaselineEntry> = {};
for (const { name, result } of results) {
  baseline[name] = entryOf({
    decisions: result.decisions,
    propagations: result.propagations,
    conflicts: result.conflicts,
    restarts: result.restarts,
    learnedClauses: result.learnedClauses,
    learnedClausesCurrent: 0,
  });
}
writeFileSync(BASELINE_URL, `${JSON.stringify(baseline, null, 2)}\n`);
console.log(`\nwrote ${BASELINE_URL.pathname.split('/').pop()} (${results.length} instances).`);
