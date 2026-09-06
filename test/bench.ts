// Manual single-shot benchmark (npm run bench), not a speedup gate.
// Authenticate both historical Git references; never read or overwrite their
// working-tree files. Validate every result before writing separate Phase-3
// evidence. Budget errors propagate as failures, never UNSAT records.

import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { performance } from 'node:perf_hooks';

const ROOT_URL = new URL('../', import.meta.url);
const JSON_URL = new URL('./phase3-benchmark.json', import.meta.url);
const MARKDOWN_URL = new URL('./phase3-benchmark.md', import.meta.url);

// Snapshot BEFORE loading implementation/fixture/reporting modules, not after
// their static imports. File versions also detect edits restored to the same
// bytes during module loading; only content hashes enter the artifacts.
const sourceSnapshot = () =>
  Object.fromEntries(
    [
      ...readdirSync(new URL('src/', ROOT_URL), { recursive: true, encoding: 'utf8' })
        .filter((path) => /\.(?:[cm]?[jt]s|json)$/.test(path))
        .map((path) => `src/${path}`),
      'test/bench.ts',
      'test/bench-comparison.ts',
      'test/helpers.ts',
      'test/php-regressions.ts',
      'package.json',
      'package-lock.json',
      'tsconfig.json',
    ]
      .sort()
      .map((path) => {
        const url = new URL(path, ROOT_URL);
        const { ino, mtimeNs, ctimeNs } = statSync(url, { bigint: true });
        return [
          path,
          {
            sha256: createHash('sha256').update(readFileSync(url)).digest('hex'),
            ino,
            mtimeNs,
            ctimeNs,
          },
        ] as const;
      }),
  );
const sources = sourceSnapshot();
const implementation = {
  head: execFileSync('git', ['rev-parse', 'HEAD'], { cwd: ROOT_URL, encoding: 'utf8' }).trim(),
  sourceSha256: Object.fromEntries(
    Object.entries(sources).map(([path, { sha256 }]) => [path, sha256]),
  ),
  node: process.version,
  nodeEnv: process.env.NODE_ENV ?? null,
};
const {
  assertBenchmarkResult,
  assertSourcesUnchanged,
  benchmarkFixtures,
  COUNTERS,
  createPhase3Report,
  loadReferences,
  sha256,
  table,
  verifyFixtures,
} = await import('./bench-comparison.js');
const references = loadReferences((args) => execFileSync('git', args, { cwd: ROOT_URL }));
const { compile } = await import('../src/compile.js');
const { Solver } = await import('../src/solver.js');
assertSourcesUnchanged(sources, sourceSnapshot());
const fixtures = benchmarkFixtures();
verifyFixtures(
  fixtures.map(({ fixture }) => fixture),
  references,
);

console.log('Phase-3 benchmark against pinned Phase 1 AND Phase 2 (manual review).\n');
const results = fixtures.map(({ expr, fixture }) => {
  const previous = references.phase2.entries.find(({ name }) => name === fixture.name);
  assert.ok(previous);
  const start = performance.now();
  const solver = new Solver(compile(expr), {
    // Keep validation assumptions independent of any mutation by the solver.
    assumptions: { ...fixture.assumptions },
    enablePle: true,
    maxConflicts: fixture.maxConflicts,
  });
  const sat = solver.solve();
  const wallMs = performance.now() - start;
  const model = sat ? solver.model() : null;
  assertBenchmarkResult(expr, fixture, model, solver.stats, previous.verdict);
  return {
    wallMs,
    entry: {
      ...fixture,
      verdict: sat ? ('SAT' as const) : ('UNSAT' as const),
      phase3: { ...solver.stats },
    },
  };
});
for (const { expr, fixture } of fixtures) {
  assert.equal(
    sha256(JSON.stringify({ expr, assumptions: fixture.assumptions })),
    fixture.fixtureSha256,
    `Benchmark fixture changed during the run: ${fixture.name}`,
  );
}
const { report, markdown } = createPhase3Report(
  references,
  implementation,
  results.map(({ entry }) => entry),
);
console.log(
  table(
    ['instance', 'verdict', ...COUNTERS, 'maxConflicts', 'wall ms (compile + solve)'],
    results.map(({ entry, wallMs }) => [
      entry.name,
      entry.verdict,
      ...COUNTERS.map((counter) => entry.phase3[counter]),
      entry.maxConflicts,
      wallMs.toFixed(2),
    ]),
  ),
);
console.log(`\n${markdown}`);
const json = `${JSON.stringify(report, null, 2)}\n`;
assertSourcesUnchanged(sources, sourceSnapshot());
writeFileSync(JSON_URL, json);
writeFileSync(MARKDOWN_URL, markdown);
console.log(
  `\nWrote test/phase3-benchmark.json and test/phase3-benchmark.md (${results.length} rows).`,
);
