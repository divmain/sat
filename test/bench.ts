// Manual benchmark (npm run bench), not a speedup gate. The immutable
// ORIGINAL Phase-1 Git blob is the only comparison reference. Never read or
// overwrite the working-tree baseline.json, even after new parent commits.
// All solves finish before writing separate Phase-2 evidence; budget errors
// propagate as failures, never UNSAT records. Wall time stays console-only.

import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { performance } from 'node:perf_hooks';
import { compile } from '../src/compile.js';
import { Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import { comparisonCells, COUNTERS } from './bench-comparison.js';
import { cnfToExpr, hypergraphFormula, mulberry32, phpCnf, random3Cnf } from './helpers.js';
import { PHP_REGRESSIONS } from './php-regressions.js';

const ROOT_URL = new URL('../', import.meta.url);
const PHASE1_COMMIT = '7037f823d192dc3cf2dc9119c8063781e143113c';
const PHASE1_PATH = 'test/baseline.json';
const PHASE1_BLOB = '489af8c72ed9c37befa806ccef03404d0a818e61';
const JSON_URL = new URL('./phase2-benchmark.json', import.meta.url);
const MARKDOWN_URL = new URL('./phase2-benchmark.md', import.meta.url);
const MAX_CONFLICTS = 200_000;
const SAT3_SEEDS: readonly number[] = [42, 43, 44];
const SAT3_VARS = 20;
const SAT3_CLAUSES = 85;

const sha256 = (content: string | Buffer): string =>
  createHash('sha256').update(content).digest('hex');

// Fail closed if history is unavailable or the bytes do not match the pinned
// Git blob. Its exact identity also fixes the parsed schema (five counters).
const phase1Content = execFileSync('git', ['show', `${PHASE1_COMMIT}:${PHASE1_PATH}`], {
  cwd: ROOT_URL,
});
const phase1Blob = createHash('sha1')
  .update(`blob ${phase1Content.length}\0`)
  .update(phase1Content)
  .digest('hex');
if (phase1Blob !== PHASE1_BLOB) {
  throw new Error(`Phase-1 baseline blob mismatch: expected ${PHASE1_BLOB}, got ${phase1Blob}`);
}
const phase1 = JSON.parse(phase1Content.toString('utf8')) as Record<string, Partial<SolverStats>>;
const reference = {
  commit: PHASE1_COMMIT,
  path: PHASE1_PATH,
  gitBlob: PHASE1_BLOB,
  sha256: sha256(phase1Content),
};

// HEAD alone cannot identify an uncommitted implementation. Hash the actual
// source/tooling bytes, excluding generated evidence and unrelated tests.
const sourceFiles = [
  'src/compile.ts',
  'src/expr.ts',
  'src/index.ts',
  'src/solver.ts',
  'test/bench.ts',
  'test/bench-comparison.ts',
  'test/helpers.ts',
  'test/php-regressions.ts',
  'package.json',
  'package-lock.json',
  'tsconfig.json',
];
const sourceSha256 = Object.fromEntries(
  sourceFiles.map((path) => [path, sha256(readFileSync(new URL(path, ROOT_URL)))]),
);
const implementation = {
  head: execFileSync('git', ['rev-parse', 'HEAD'], { cwd: ROOT_URL, encoding: 'utf8' }).trim(),
  sourceSha256,
  node: process.version,
  nodeEnv: process.env.NODE_ENV ?? null,
};

interface Instance {
  name: string;
  fixture: string;
  build: () => BooleanExpr;
  assumptions?: VariableAssignments | undefined;
  maxConflicts: number;
  calibratedConflicts?: number;
}

const instances: readonly Instance[] = [
  {
    name: 'hypergraph',
    fixture: 'hypergraphFormula()',
    build: hypergraphFormula,
    assumptions: { h: Value.TRUE },
    maxConflicts: MAX_CONFLICTS,
  },
  {
    name: 'php_5_4',
    fixture: 'cnfToExpr(phpCnf(5, 4))',
    build: () => cnfToExpr(phpCnf(5, 4)),
    maxConflicts: MAX_CONFLICTS,
  },
  {
    name: 'php_6_5',
    fixture: 'cnfToExpr(phpCnf(6, 5))',
    build: () => cnfToExpr(phpCnf(6, 5)),
    maxConflicts: MAX_CONFLICTS,
  },
  ...SAT3_SEEDS.map((seed) => ({
    name: `sat3_seed${seed}`,
    fixture: `cnfToExpr(random3Cnf(mulberry32(${seed}), ${SAT3_VARS}, ${SAT3_CLAUSES}))`,
    build: () => cnfToExpr(random3Cnf(mulberry32(seed), SAT3_VARS, SAT3_CLAUSES)),
    maxConflicts: MAX_CONFLICTS,
  })),
  ...PHP_REGRESSIONS.map(({ pigeons, holes, calibratedConflicts, maxConflicts }) => ({
    name: `php_${pigeons}_${holes}`,
    fixture: `cnfToExpr(phpCnf(${pigeons}, ${holes}))`,
    build: () => cnfToExpr(phpCnf(pigeons, holes)),
    calibratedConflicts,
    maxConflicts,
  })),
];
for (const name of Object.keys(phase1)) {
  if (!instances.some((instance) => instance.name === name)) {
    throw new Error(`Missing original Phase-1 instance: ${name}`);
  }
}

console.log('Phase-2 benchmark against pinned original Phase 1 (manual review).\n');
const results = instances.map((instance) => {
  const expr = instance.build();
  const assumptions = instance.assumptions ?? {};
  const fixtureSha256 = sha256(JSON.stringify({ expr, assumptions }));
  const start = performance.now();
  // Fresh compilation/solver, default brancher, same single-shot PLE path.
  const solver = new Solver(compile(expr), {
    assumptions,
    enablePle: true,
    maxConflicts: instance.maxConflicts,
  });
  const sat = solver.solve();
  const wallMs = performance.now() - start;
  return {
    wallMs,
    entry: {
      name: instance.name,
      fixture: instance.fixture,
      fixtureSha256,
      assumptions,
      maxConflicts: instance.maxConflicts,
      calibratedConflicts: instance.calibratedConflicts ?? null,
      verdict: sat ? 'SAT' : 'UNSAT',
      phase1: phase1[instance.name] ?? null,
      phase2: { ...solver.stats },
    },
  };
});
for (const [path, hash] of Object.entries(sourceSha256)) {
  if (sha256(readFileSync(new URL(path, ROOT_URL))) !== hash) {
    throw new Error(`Benchmark input changed during the run: ${path}; rerun before recording`);
  }
}

const table = (headers: string[], rows: (string | number)[][]): string =>
  [
    `| ${headers.join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...rows.map((row) => `| ${row.join(' | ')} |`),
  ].join('\n');
const entries = results.map(({ entry }) => entry);
const currentHeaders = ['instance', 'verdict', ...COUNTERS, 'maxConflicts'];
const currentRows = entries.map((entry) => [
  entry.name,
  entry.verdict,
  ...COUNTERS.map((counter) => entry.phase2[counter]),
  entry.maxConflicts,
]);
const currentTable = table(currentHeaders, currentRows);
console.log(
  table(
    [...currentHeaders, 'wall ms (compile + solve)'],
    currentRows.map((row, index) => [...row, results[index].wallMs.toFixed(2)]),
  ),
);

const comparison = table(
  [
    'instance',
    'counter',
    'Phase1',
    'Phase2',
    'delta (Phase2 - Phase1)',
    'ratio (Phase1 / Phase2)',
    'count change',
  ],
  entries.flatMap((entry) =>
    COUNTERS.map((counter) => [
      entry.name,
      counter,
      ...comparisonCells(entry.phase1?.[counter], entry.phase2[counter]),
    ]),
  ),
);
const notes = [
  'Manual review only: no automated speedup gate or task-completion claim.',
  'Owner-approved disposition: task-884f note 2026-09-06T01:56:58Z supersedes the unsupported orders-of-magnitude PHP and Phase-1-infeasibility requirements. Future substantial algorithmic improvements are tracked by independent objective objv-b2ca, which is not achieved by this benchmark or by completing plan-7748.',
  'Current task-884f performance acceptance requires authentic reproducible comparisons with honest actual numbers, learning on PHP rows, hypergraph parity at 2 decisions/16 propagations/0 conflicts, and PHP(7,6)/PHP(8,7) UNSAT within the fixed 10x-padded conflict caps. All other correctness, property, tooling, and public API requirements remain binding.',
  'Phase 1 contains six completed rows, no budget-exhausted rows, and no PHP(7,6) or PHP(8,7) measurements. Missing data is not capped, timed out, or an infinite improvement.',
  'The original six rows retain maxConflicts=200000 and the original generators. Random 3-SAT uses 20 variables, 85 clauses, and seeds 42/43/44.',
  'Every run uses fresh compilation, the default brancher (no variablePriority hook), and enablePle=true. Budget exhaustion throws; no failure is recorded as UNSAT.',
  'The larger PHP caps are pinned at exactly 10x once-at-implementation observations (723 and 3627 conflicts). UNSAT follows independently from the pigeonhole principle. Passing these caps proves only those budgets, not Phase-1 infeasibility or orders-of-magnitude improvement.',
  'Ratios are Phase1/Phase2, rounded to two decimals, not wall-time speedups. For decisions/propagations/conflicts, >1 means fewer current counts; <1 means higher current counts (regression). A zero denominator is n/a, with 0/0 explicitly labelled parity.',
  'Learning counters report activity, not speedup: higher learnedClauses can witness learning. Phase 1 did not record learnedClausesCurrent; it remains missing rather than an invented zero.',
  'HEAD is context only. sourceSha256 identifies actual working-tree bytes, including uncommitted code; fixtureSha256 hashes UTF-8 JSON.stringify({ expr, assumptions }) before compilation.',
  'The working-tree test/baseline.json and previous Phase-2 reports are neither read as references nor overwritten as baselines. Only the separate Phase-2 reports are regenerated.',
];
const markdown = [
  '# Phase-2 Benchmark Comparison',
  '',
  'Generated by `npm run bench`. No models, timestamps, or wall times are stored.',
  '',
  '## Provenance',
  '',
  `- Original Phase-1 reference: \`${reference.commit}:${reference.path}\``,
  `- Verified Git blob: \`${reference.gitBlob}\``,
  `- Reference SHA-256: \`${reference.sha256}\``,
  `- Working-tree HEAD (not the implementation fingerprint): \`${implementation.head}\``,
  `- Node: \`${implementation.node}\`; NODE_ENV: \`${implementation.nodeEnv ?? '(unset)'}\``,
  '',
  '## Interpretation And Limits',
  '',
  ...notes.map((note) => `- ${note}`),
  '',
  '## Current Counters',
  '',
  currentTable,
  '',
  '## All Counter Comparisons',
  '',
  comparison,
  '',
  '## Fixture Fingerprints',
  '',
  table(
    ['instance', 'generator', 'assumptions', 'calibratedConflicts', 'fixtureSha256'],
    entries.map((entry) => [
      entry.name,
      `\`${entry.fixture}\``,
      `\`${JSON.stringify(entry.assumptions)}\``,
      entry.calibratedConflicts ?? 'n/a',
      `\`${entry.fixtureSha256}\``,
    ]),
  ),
  '',
  '## Source Fingerprints',
  '',
  table(['file', 'SHA-256 (raw bytes)'], Object.entries(sourceSha256)),
  '',
].join('\n');
console.log(`\nReference: ${reference.commit}:${reference.path} (blob ${reference.gitBlob})`);
console.log(`\n${comparison}\n`);
for (const note of notes) {
  console.log(note);
}
writeFileSync(
  JSON_URL,
  `${JSON.stringify({ reference, implementation, notes, entries }, null, 2)}\n`,
);
writeFileSync(MARKDOWN_URL, markdown);
console.log(
  `\nWrote test/phase2-benchmark.json and test/phase2-benchmark.md (${entries.length} rows).`,
);
