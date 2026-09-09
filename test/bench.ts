// Assert-only legacy benchmark verifier (npm run bench:legacy), not a speedup
// gate. Authenticate the frozen Phase-1/2/3 references plus the Phase-4 record,
// its markdown, and the release manifest at the release commit, including every
// embedded Phase-4 source fingerprint against those Git bytes; never read or
// write the frozen working-tree artifacts. Re-run all 8 fixtures and write
// nothing. Gates mode (the permanent default since learned-clause
// minimization landed) keeps the authentication/verdict/oracle/cap checks and
// prints non-fatal counter deltas; parity mode (--parity) hard-fails unless
// all 48 counters exactly equal the frozen Phase-4 record, retained for
// explicit parity experiments. Budget errors propagate as failures, never
// UNSAT records.
// Both modes also compare the current compiler's COMPLETE canonical compiled
// snapshot (normalized clauses, numVars, the named index/name mapping, and
// levelZeroUnsat — a clause-only check would miss a lost named universe)
// against the authenticated pristine-v2 snapshots in test/legacy-compiled-cnf.json.

import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { pathToFileURL } from 'node:url';
import type { compile } from '../src/compile.js';
import type { Solver } from '../src/solver.js';
import type { benchmarkFixtures, BenchmarkFixture } from './bench-comparison.js';
import { compiledSnapshot, digest } from './bench-evidence.js';
import type { CompiledSnapshot } from './bench-evidence.js';
import { loadLegacyCompiledCnf, selectEnvironment } from './bench-v3-references.js';
import type { LegacyFixtureRecord } from './bench-v3-references.js';

const ROOT_URL = new URL('../', import.meta.url);

// Snapshot BEFORE loading implementation/fixture/reporting modules, not after
// their static imports. File versions also detect edits restored to the same
// bytes during module loading; only content hashes enter the drift checks.
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

export type VerifyMode = 'parity' | 'gates';

// The complete compiled-snapshot gate: the current compiler's canonical
// snapshot for each legacy fixture must equal the authenticated pristine-v2
// reference byte-for-byte in content (digest) and structure (deep equal). The
// reference was captured before any compiler-changing work; this gate is what
// makes later compiler sharing/flattening prove output preservation.
export function assertLegacyCompiledSnapshot(
  fixture: BenchmarkFixture,
  snapshot: CompiledSnapshot,
  record: LegacyFixtureRecord,
): void {
  assert.equal(
    record.inputSha256,
    fixture.fixtureSha256,
    `${fixture.name}: legacy compiled-snapshot input identity disagrees with the pinned fixture`,
  );
  assert.equal(
    record.cap,
    fixture.maxConflicts,
    `${fixture.name}: legacy compiled-snapshot cap disagrees with the pinned fixture`,
  );
  assert.deepEqual(
    record.assumptions,
    Object.entries(fixture.assumptions),
    `${fixture.name}: legacy compiled-snapshot assumptions disagree with the pinned fixture`,
  );
  assert.equal(
    digest(snapshot),
    record.compiledSha256,
    `${fixture.name}: compiled snapshot digest mismatch — compiler output (including numVars, the named index/name universe, normalized clauses, or levelZeroUnsat) changed`,
  );
  assert.deepEqual(
    snapshot,
    record.snapshot,
    `${fixture.name}: complete compiled snapshot mismatch against the pristine v2 reference`,
  );
}

// Injection keeps tests on this exact orchestration/validation path. The CLI
// always uses real Git, snapshots, modules, and fixtures. Verify mode writes
// nothing: there is no artifact-writing path reachable from npm scripts.
export interface BenchmarkOptions {
  readGit?: ((args: string[]) => Buffer) | undefined;
  snapshotSources?: typeof sourceSnapshot | undefined;
  loadSolver?: (() => Promise<{ compile: typeof compile; Solver: typeof Solver }>) | undefined;
  fixtures?: typeof benchmarkFixtures | undefined;
  mode?: VerifyMode | undefined;
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
  mode = 'gates',
  log = console.log,
}: BenchmarkOptions = {}): Promise<void> {
  const sources = snapshotSources();
  const {
    assertBenchmarkResult,
    assertSourcesUnchanged,
    benchmarkFixtures,
    COUNTERS,
    loadPhase4Record,
    loadReferences,
    PHASE4_REFERENCE,
    sha256,
    table,
    verifyFixtures,
  } = await import('./bench-comparison.js');
  const references = loadReferences(readGit);
  const phase4 = loadPhase4Record(readGit, references);
  // The pristine-v2 complete compiled snapshots, authenticated from their own
  // pinned artifact commit exactly like the frozen phase references above.
  const legacyCompiled = loadLegacyCompiledCnf(readGit);
  const legacyEnvironment = selectEnvironment(
    legacyCompiled.environments,
    process.env.SAT_DEBUG === '1',
    'legacy compiled snapshots',
  );
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

  // Complete-snapshot coverage: exactly the 8 pinned legacy fixtures, by name.
  const legacyByName = new Map(
    legacyEnvironment.fixtures.map((record) => [record.id, record] as const),
  );
  assert.deepEqual(
    legacyEnvironment.fixtures.map((record) => record.id).sort(),
    fixtures.map(({ fixture }) => fixture.name).sort(),
    'legacy compiled-snapshot fixture coverage disagreement',
  );

  // Current HEAD and Node version are context only, never implementation identity.
  const head = readGit(['rev-parse', 'HEAD']).toString('utf8').trim();
  log(
    `Legacy Phase-4 benchmark verifier (${mode} mode; assert-only, writes nothing).\nFrozen Phase-4 record: ${PHASE4_REFERENCE.commit}:${PHASE4_REFERENCE.path}\nComplete compiled snapshots: authenticated pristine-v2 reference, compared per fixture.\nCurrent HEAD (context, not implementation identity): ${head}; Node ${process.version}\n`,
  );
  const results = fixtures.map(({ expr, fixture }) => {
    const recorded = phase4.entries.find(({ name }) => name === fixture.name);
    assert.ok(recorded, `Missing frozen Phase-4 record instance: ${fixture.name}`);
    const legacyRecord = legacyByName.get(fixture.name);
    assert.ok(legacyRecord, `Missing legacy compiled-snapshot fixture: ${fixture.name}`);
    const start = performance.now();
    const cnf = compile(expr);
    // Snapshot before Solver construction: the complete canonical compiled
    // snapshot is a compiler-output gate, independent of the search below.
    assertLegacyCompiledSnapshot(fixture, compiledSnapshot(cnf), legacyRecord);
    const solver = new Solver(cnf, {
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
    assertBenchmarkResult(expr, fixture, model, solver.stats, recorded.verdict);
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
  assertSourcesUnchanged(sources, snapshotSources());

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

  const counterTotal = results.length * COUNTERS.length;
  const recordedFor = (name: string) => {
    const recorded = phase4.entries.find(({ name: entryName }) => entryName === name);
    assert.ok(recorded, `Missing frozen Phase-4 record instance: ${name}`);
    return recorded;
  };
  if (mode === 'parity') {
    for (const { entry } of results) {
      const recorded = recordedFor(entry.name);
      for (const counter of COUNTERS) {
        assert.equal(
          entry.phase4[counter],
          recorded.phase4[counter],
          `${entry.name}: ${counter} broke Phase-4 parity (current ${entry.phase4[counter]}, frozen ${recorded.phase4[counter]})`,
        );
      }
    }
    log(
      `\nParity verified: all ${counterTotal} counters exactly match the frozen Phase-4 record. Nothing was written.`,
    );
  } else {
    const deltas = results.flatMap(({ entry }) =>
      COUNTERS.flatMap((counter) => {
        const recorded = recordedFor(entry.name);
        const delta = entry.phase4[counter] - recorded.phase4[counter];
        return delta === 0
          ? []
          : [
              [
                entry.name,
                counter,
                recorded.phase4[counter],
                entry.phase4[counter],
                delta,
              ] as const,
            ];
      }),
    );
    if (deltas.length === 0) {
      log(`\nAll ${counterTotal} counters match the frozen Phase-4 record.`);
    } else {
      log(
        `\nCounter deltas (non-fatal in gates mode):\n${table(
          ['instance', 'counter', 'frozen Phase-4', 'current', 'delta'],
          deltas.map(([name, counter, frozen, current, delta]) => [
            name,
            counter,
            frozen,
            current,
            `${delta > 0 ? '+' : ''}${delta}`,
          ]),
        )}`,
      );
    }
    log(
      `\nGates verified: authentication, verdicts, oracles, and caps passed; ${deltas.length} of ${counterTotal} counter deltas are non-fatal. Nothing was written.`,
    );
  }
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  await runBenchmark({ mode: process.argv.includes('--parity') ? 'parity' : 'gates' });
}
