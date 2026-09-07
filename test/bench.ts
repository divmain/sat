// Manual single-shot benchmark (npm run bench), not a speedup gate.
// Authenticate all three historical Git references; never read or overwrite their
// working-tree files. Validate every result before writing Phase-4 release
// evidence. Budget errors propagate as failures, never UNSAT records.

import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { pathToFileURL } from 'node:url';
import type { compile } from '../src/compile.js';
import type { Solver } from '../src/solver.js';
import type { benchmarkFixtures } from './bench-comparison.js';

const ROOT_URL = new URL('../', import.meta.url);
const JSON_URL = new URL('./phase4-benchmark.json', import.meta.url);
const MARKDOWN_URL = new URL('./phase4-benchmark.md', import.meta.url);

// Snapshot BEFORE loading implementation/fixture/reporting modules, not after
// their static imports. File versions also detect edits restored to the same
// bytes during module loading; only content hashes enter the artifacts.
export const sourceSnapshot = () =>
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

// Injection keeps tests on this exact orchestration/validation/write path.
// The CLI always uses real Git, snapshots, modules, fixtures, and filesystem writes.
export interface BenchmarkOptions {
  readGit?: ((args: string[]) => Buffer) | undefined;
  snapshotSources?: typeof sourceSnapshot | undefined;
  loadSolver?: (() => Promise<{ compile: typeof compile; Solver: typeof Solver }>) | undefined;
  fixtures?: typeof benchmarkFixtures | undefined;
  write?: ((url: URL, content: string) => void) | undefined;
  log?: ((message: string) => void) | undefined;
}

export async function runBenchmark({
  readGit = (args) => execFileSync('git', args, { cwd: ROOT_URL }),
  snapshotSources = sourceSnapshot,
  loadSolver = async () => {
    const { compile } = await import('../src/compile.js');
    const { Solver } = await import('../src/solver.js');
    return { compile, Solver };
  },
  fixtures: makeFixtures,
  write = writeFileSync,
  log = console.log,
}: BenchmarkOptions = {}): Promise<void> {
  const sources = snapshotSources();
  const implementation = {
    head: readGit(['rev-parse', 'HEAD']).toString('utf8').trim(),
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
    createPhase4Report,
    loadReferences,
    sha256,
    table,
    verifyFixtures,
  } = await import('./bench-comparison.js');
  const references = loadReferences(readGit);
  const { compile, Solver } = await loadSolver();
  assertSourcesUnchanged(sources, snapshotSources());
  const fixtures = (makeFixtures ?? benchmarkFixtures)();
  const verifyInputs = () => {
    verifyFixtures(
      fixtures.map(({ fixture }) => fixture),
      references,
    );
    for (const { expr, fixture } of fixtures) {
      assert.equal(
        sha256(JSON.stringify({ expr, assumptions: fixture.assumptions })),
        fixture.fixtureSha256,
        `Benchmark fixture changed during the run: ${fixture.name}`,
      );
    }
  };
  verifyInputs();

  log('Phase-4 release single-shot benchmark against pinned Phases 1, 2, and 3 (manual review).\n');
  const results = fixtures.map(({ expr, fixture }) => {
    const previous = references.phase3.entries.find(({ name }) => name === fixture.name);
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
    assert.equal(typeof sat, 'boolean', `${fixture.name}: invalid solver verdict`);
    const model = sat ? solver.model() : null;
    assert.equal(sat, model !== null, `${fixture.name}: solver verdict/model disagreement`);
    assertBenchmarkResult(expr, fixture, model, solver.stats, previous.verdict);
    return {
      wallMs,
      entry: {
        ...fixture,
        verdict: sat ? ('SAT' as const) : ('UNSAT' as const),
        phase4: { ...solver.stats },
      },
    };
  });
  verifyInputs();
  const { report, markdown } = createPhase4Report(
    references,
    implementation,
    results.map(({ entry }) => entry),
  );
  log(
    table(
      ['instance', 'verdict', ...COUNTERS, 'maxConflicts', 'wall ms (compile + solve)'],
      results.map(({ entry, wallMs }) => [
        entry.name,
        entry.verdict,
        ...COUNTERS.map((counter) => entry.phase4[counter]),
        entry.maxConflicts,
        wallMs.toFixed(2),
      ]),
    ),
  );
  log(`\n${markdown}`);
  const json = `${JSON.stringify(report, null, 2)}\n`;
  assertSourcesUnchanged(sources, snapshotSources());
  write(JSON_URL, json);
  write(MARKDOWN_URL, markdown);
  log(`\nWrote test/phase4-benchmark.json and test/phase4-benchmark.md (${results.length} rows).`);
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  await runBenchmark();
}
