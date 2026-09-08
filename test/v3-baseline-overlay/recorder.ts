import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, readdirSync, readlinkSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { compile } from '../../src/compile.js';
import { calibrate } from './adapter.js';
import { compiledSnapshot, digest, inputIdentity, json, sha256 } from './evidence.js';
import { corpus, legacyFixtures } from './fixtures.js';

export const BASELINE = 'ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2';
const root = fileURLToPath(new URL('../../', import.meta.url));
const overlayPath = 'test/v3-baseline-overlay';
const git = (...args: string[]): Buffer =>
  execFileSync('git', args, { cwd: root, maxBuffer: 128 * 1024 * 1024 });
const gitText = (...args: string[]): string =>
  git(...args)
    .toString()
    .trim();

function authenticateFiles(commit: string, paths: string[]) {
  return paths.map((path) => {
    const historical = git('show', `${commit}:${path}`);
    assert.deepEqual(
      readFileSync(resolve(root, path)),
      historical,
      `${path}: unauthenticated bytes`,
    );
    return { path, blob: gitText('rev-parse', `${commit}:${path}`), sha256: sha256(historical) };
  });
}

function installedTree(directory: string): { path: string; sha256: string }[] {
  return readdirSync(resolve(root, directory), { withFileTypes: true })
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0))
    .flatMap((entry) => {
      const path = `${directory}/${entry.name}`;
      if (entry.isDirectory()) return installedTree(path);
      const bytes = entry.isSymbolicLink()
        ? `symlink:${readlinkSync(resolve(root, path))}`
        : readFileSync(resolve(root, path));
      return [{ path, sha256: sha256(bytes) }];
    });
}

function provenance(seal: string) {
  assert.equal(gitText('rev-parse', 'HEAD'), BASELINE, 'must run in isolated historical worktree');
  assert.match(seal, /^[0-9a-f]{40}$/);
  assert.equal(gitText('rev-parse', `${seal}^{commit}`), seal);
  assert.ok(process.env.NODE_ENV === undefined || process.env.NODE_ENV === 'production');
  assert.equal(process.env.NODE_OPTIONS, undefined, 'uncontrolled Node preloads are not allowed');
  assert.deepEqual(
    process.execArgv,
    ['--import', 'tsx'],
    'uncontrolled launch flags are not allowed',
  );
  const overlayFiles = gitText('ls-tree', '-r', '--name-only', seal, '--', overlayPath).split('\n');
  assert.deepEqual(
    readdirSync(resolve(root, overlayPath)).sort(),
    overlayFiles.map((path) => path.slice(overlayPath.length + 1)).sort(),
  );
  assert.ok(overlayFiles.every((path) => !path.endsWith('.spec.ts')));
  const sourcePaths = gitText('ls-tree', '-r', '--name-only', BASELINE, '--', 'src').split('\n');
  assert.deepEqual(
    readdirSync(resolve(root, 'src')).sort(),
    sourcePaths.map((path) => path.slice(4)).sort(),
  );
  const sources = authenticateFiles(BASELINE, sourcePaths);
  const tools = authenticateFiles(BASELINE, [
    'package.json',
    'package-lock.json',
    'tsconfig.json',
    'biome.json',
  ]);
  const overlayFilesEvidence = authenticateFiles(seal, overlayFiles);
  const installedTools = ['tsx', 'typescript', '@biomejs/biome', 'esbuild'].map((name) => {
    const bytes = readFileSync(resolve(root, 'node_modules', name, 'package.json'));
    const metadata = JSON.parse(bytes.toString()) as { version: string };
    return { name, version: metadata.version, packageSha256: sha256(bytes) };
  });
  return {
    baselineCommit: BASELINE,
    recorderSealCommit: seal,
    overlay: true,
    sources,
    tools,
    overlayFiles: overlayFilesEvidence,
    installedTools,
    installedTreeSha256: digest(installedTree('node_modules')),
    environment: {
      node: process.version,
      versions: process.versions,
      platform: process.platform,
      arch: process.arch,
      nodeEnv: process.env.NODE_ENV ?? null,
      nodeOptions: null,
      execArgv: process.execArgv,
      audits: process.env.NODE_ENV !== 'production',
    },
  };
}

function record(seal: string) {
  const before = provenance(seal);
  const scenarios = corpus();
  assert.equal(scenarios.length, 23);
  const rows = scenarios.map((scenario) => {
    console.log(
      `Recording ${scenario.id} (${process.env.NODE_ENV ?? 'unset'}): calibration + two final runs`,
    );
    const start = performance.now();
    const result = calibrate(scenario);
    if (result.final.status !== 'exhausted') {
      if (scenario.id === 'pairs8') assert.equal(result.final.modelCount, 6561);
      if (scenario.id === 'php_9_8') assert.equal(result.final.status, 'unsat');
      if (scenario.id.startsWith('xor')) assert.equal(result.final.status, 'sat');
    }
    console.log(
      `${scenario.id}: ${result.final.status}, cap ${result.finalCap}, conflicts ${
        result.final.stats.conflicts
      }, ${(performance.now() - start).toFixed(0)} ms (informational)`,
    );
    return {
      id: scenario.id,
      mode: scenario.mode,
      definition: scenario.definition,
      inputSha256: digest(inputIdentity(scenario)),
      assumptions: Object.entries(scenario.assumptions),
      calls: scenario.calls.map((call) => Object.entries(call)),
      compiledSha256: result.final.compiledSha256,
      calibration: result.trials,
      finalCap: result.finalCap,
      measurement: result.final,
      confirmationSha256: result.confirmationSha256,
    };
  });
  const historicalFixtures = JSON.parse(
    git('show', `${BASELINE}:test/phase4-benchmark.json`).toString(),
  ) as {
    entries: { name: string; fixtureSha256: string; maxConflicts: number; assumptions: unknown }[];
  };
  const fixtures = legacyFixtures().map((fixture, index) => {
    const snapshot = compiledSnapshot(compile(fixture.expr));
    const inputSha256 = digest({ expr: fixture.expr, assumptions: fixture.assumptions });
    assert.equal(historicalFixtures.entries[index].name, fixture.id);
    assert.equal(historicalFixtures.entries[index].fixtureSha256, inputSha256);
    assert.equal(historicalFixtures.entries[index].maxConflicts, fixture.maxConflicts);
    assert.deepEqual(historicalFixtures.entries[index].assumptions, fixture.assumptions);
    return {
      id: fixture.id,
      inputSha256,
      assumptions: Object.entries(fixture.assumptions),
      cap: fixture.maxConflicts,
      compiledSha256: digest(snapshot),
      snapshot,
    };
  });
  assert.deepEqual(provenance(seal), before, 'source/overlay/tool bytes drifted during recording');
  return {
    baseline: { schema: 1, provenance: before, rows },
    legacy: { schema: 1, provenance: before, fixtures },
  };
}

const [mode, seal, destination] = process.argv.slice(2);
assert.ok(
  mode === 'measure' || mode === 'replay',
  'usage: recorder.ts measure <seal> <output> | replay <seal> <artifact-commit>',
);
assert.ok(seal && destination);
if (mode === 'measure') {
  const result = record(seal);
  writeFileSync(destination, json(result), { flag: 'wx' });
} else {
  assert.match(destination, /^[0-9a-f]{40}$/);
  assert.equal(gitText('rev-parse', `${destination}^{commit}`), destination);
  git('merge-base', '--is-ancestor', seal, destination);
  // References come exclusively from authenticated commit bytes, never mutable
  // working-tree artifacts. Print commit/blob/content identities for the audit.
  const references = ['test/v3-baseline.json', 'test/legacy-compiled-cnf.json'].map((path) => {
    const bytes = git('show', `${destination}:${path}`);
    console.log(
      json({
        commit: destination,
        path,
        blob: gitText('rev-parse', `${destination}:${path}`),
        sha256: sha256(bytes),
      }),
    );
    const reference = JSON.parse(bytes.toString()) as {
      schema: number;
      environments: { provenance: { environment: { nodeEnv: string | null } } }[];
    };
    assert.equal(reference.schema, 1);
    assert.equal(reference.environments.length, 2);
    assert.deepEqual(
      reference.environments.map((item) => item.provenance.environment.nodeEnv),
      [null, 'production'],
    );
    assert.equal(json(reference), bytes.toString(), 'reference JSON is not canonical');
    return reference.environments.find(
      (item) => item.provenance.environment.nodeEnv === (process.env.NODE_ENV ?? null),
    );
  });
  const result = record(seal);
  assert.equal(json(result.baseline), json(references[0]), 'baseline replay differs');
  assert.equal(json(result.legacy), json(references[1]), 'legacy snapshot replay differs');
  console.log('Authenticated replay: both reference environment payloads are byte-identical.');
}
