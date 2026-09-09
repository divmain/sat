// Authentication and decoding of the sealed v3 benchmark references. Both
// artifacts are read exclusively from pinned Git commits/blobs/SHA-256s — never
// from mutable working-tree files — and their embedded historical
// source/tool/overlay provenance is re-verified against Git bytes at the
// pristine v2 baseline commit and the frozen recorder seal commit. There is no
// fallback: unavailable or modified history fails closed.

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import type { SolverStats } from '../src/solver.js';
import { json, sha256 } from './bench-evidence.js';
import type { CompiledSnapshot } from './bench-evidence.js';

// The pristine v2.0.0 release commit the frozen recorder measured against.
export const V3_BASELINE_COMMIT = 'ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2';
// The frozen recorder overlay seal (test/v3-baseline-overlay/* at this commit).
export const V3_RECORDER_SEAL_COMMIT = '2ba0a394b534fb64449a832ce95da4e81ee50ba6';
// The commit sealing both reference artifacts (test/v3-baseline.json and
// test/legacy-compiled-cnf.json), a descendant of the recorder seal.
export const V3_ARTIFACT_COMMIT = 'cd44ed11d0e6abf1bf2b61d94dd995d4d6a04438';

export interface ReferenceIdentity {
  commit: string;
  path: string;
  gitBlob: string;
  sha256: string;
}

export const V3_BASELINE_REFERENCE: ReferenceIdentity = {
  commit: V3_ARTIFACT_COMMIT,
  path: 'test/v3-baseline.json',
  gitBlob: '6fc09b5e01d1f2851a1a643a93b61278f372b2a1',
  sha256: '517d894090d15a11cfa8bd3ba80ac03d4db4895eeb0d21392b81e652eb1d411c',
};

export const LEGACY_COMPILED_CNF_REFERENCE: ReferenceIdentity = {
  commit: V3_ARTIFACT_COMMIT,
  path: 'test/legacy-compiled-cnf.json',
  gitBlob: '876115a1994d75d6afc3bf9e26f249e8d3a7f94b',
  sha256: '7dceb3df7dba1a0047728283cc468179761f48467772b8af5ab60f89d175d560',
};

export interface ProvenanceFile {
  path: string;
  blob: string;
  sha256: string;
}

export interface RecordedProvenance {
  baselineCommit: string;
  recorderSealCommit: string;
  overlay: boolean;
  sources: ProvenanceFile[];
  tools: ProvenanceFile[];
  overlayFiles: ProvenanceFile[];
  installedTools: { name: string; version: string; packageSha256: string }[];
  installedTreeSha256: string;
  environment: {
    node: string;
    versions: Record<string, string>;
    platform: string;
    arch: string;
    nodeEnv: string | null;
    nodeOptions: string | null;
    execArgv: string[];
    audits: boolean;
  };
}

export interface RecordedCall {
  index: number;
  status: 'sat' | 'unsat' | 'exhausted';
  modelDigest: string | null;
  stats: SolverStats;
}

export interface RecordedMeasurement {
  id: string;
  mode: 'single' | 'incremental' | 'enumeration';
  inputSha256: string;
  compiledSha256: string;
  cap: number;
  status: 'sat' | 'unsat' | 'complete' | 'exhausted';
  construction: SolverStats;
  stats: SolverStats;
  calls: RecordedCall[];
  completedCalls: number;
  unexecutedCalls: number;
  orderedCallDigest: string;
  modelCount: number;
  modelDigest: string | null;
  modelSetDigest: string;
  orderedModelPrefixDigest: string;
  modelDigests: string[];
}

export interface BaselineRow {
  id: string;
  mode: 'single' | 'incremental' | 'enumeration';
  definition: Record<string, unknown>;
  inputSha256: string;
  assumptions: [string, number][];
  calls: [string, number][][];
  compiledSha256: string;
  calibration: RecordedMeasurement[];
  finalCap: number;
  measurement: RecordedMeasurement;
  confirmationSha256: string;
}

export interface BaselineEnvironment {
  schema: number;
  provenance: RecordedProvenance;
  rows: BaselineRow[];
}

export interface V3BaselineArtifact {
  schema: number;
  environments: BaselineEnvironment[];
}

export interface LegacyFixtureRecord {
  id: string;
  inputSha256: string;
  assumptions: [string, number][];
  cap: number;
  compiledSha256: string;
  snapshot: CompiledSnapshot;
}

export interface LegacyCompiledEnvironment {
  schema: number;
  provenance: RecordedProvenance;
  fixtures: LegacyFixtureRecord[];
}

export interface LegacyCompiledArtifact {
  schema: number;
  environments: LegacyCompiledEnvironment[];
}

const gitBlobSha1 = (content: Buffer): string =>
  createHash('sha1').update(`blob ${content.length}\0`).update(content).digest('hex');

// Git is the only reference reader. No fallback to HEAD, working files, or new measurements.
export function authenticateV3Artifact(
  readGit: (args: string[]) => Buffer,
  reference: ReferenceIdentity,
  label: string,
): string {
  assert.equal(
    readGit(['rev-parse', '--verify', `${reference.commit}^{commit}`])
      .toString('utf8')
      .trim(),
    reference.commit,
    `${label} reference commit mismatch: ${reference.commit}`,
  );
  const content = readGit(['show', `${reference.commit}:${reference.path}`]);
  assert.equal(
    gitBlobSha1(content),
    reference.gitBlob,
    `${label} reference blob mismatch: ${reference.path}`,
  );
  assert.equal(
    sha256(content),
    reference.sha256,
    `${label} reference SHA-256 mismatch: ${reference.path}`,
  );
  const text = content.toString('utf8');
  assert.equal(
    json(JSON.parse(text)),
    text,
    `${label} reference is not canonical JSON.stringify(…, null, 2) + '\\n': ${reference.path}`,
  );
  return text;
}

// Every embedded provenance entry is checked against Git bytes at the pinned
// historical commits: sources/tools at the pristine v2 baseline, overlay files
// at the recorder seal. Installed-tree metadata was authenticated by the
// recorder at measurement time and remains recorded context here.
export function assertV3Provenance(
  readGit: (args: string[]) => Buffer,
  provenance: RecordedProvenance,
  artifactCommit: string,
  label: string,
): void {
  assert.equal(
    provenance.baselineCommit,
    V3_BASELINE_COMMIT,
    `${label}: baseline commit disagreement`,
  );
  assert.equal(
    provenance.recorderSealCommit,
    V3_RECORDER_SEAL_COMMIT,
    `${label}: recorder seal disagreement`,
  );
  assert.equal(provenance.overlay, true, `${label}: overlaid provenance must be declared`);
  for (const commit of [V3_BASELINE_COMMIT, V3_RECORDER_SEAL_COMMIT]) {
    assert.equal(
      readGit(['rev-parse', '--verify', `${commit}^{commit}`])
        .toString('utf8')
        .trim(),
      commit,
      `${label}: required historical commit is unavailable: ${commit} (full checkout required)`,
    );
  }
  // The artifact commit must descend from the recorder seal: references were
  // measured by the sealed recorder, never the reverse.
  readGit(['merge-base', '--is-ancestor', V3_RECORDER_SEAL_COMMIT, artifactCommit]);
  const groups: [string, ProvenanceFile[]][] = [
    [V3_BASELINE_COMMIT, [...provenance.sources, ...provenance.tools]],
    [V3_RECORDER_SEAL_COMMIT, provenance.overlayFiles],
  ];
  for (const [commit, entries] of groups) {
    for (const { path, blob, sha256: recorded } of entries) {
      const bytes = readGit(['show', `${commit}:${path}`]);
      assert.equal(gitBlobSha1(bytes), blob, `${label}: ${path} blob mismatch at ${commit}`);
      assert.equal(sha256(bytes), recorded, `${label}: ${path} SHA-256 mismatch at ${commit}`);
    }
  }
}

function assertEnvironmentShape(
  environments: { provenance: RecordedProvenance }[],
  label: string,
): void {
  assert.equal(environments.length, 2, `${label}: expected exactly two recorded environments`);
  assert.deepEqual(
    environments.map((environment) => environment.provenance.environment.nodeEnv),
    [null, 'production'],
    `${label}: environments must be NODE_ENV unset then production`,
  );
  assert.deepEqual(
    environments.map((environment) => environment.provenance.environment.audits),
    [true, false],
    `${label}: environment audit states must be on (unset) then off (production)`,
  );
}

export function loadV3Baseline(
  readGit: (args: string[]) => Buffer,
  reference: ReferenceIdentity = V3_BASELINE_REFERENCE,
  // The sealed version-1 corpus has exactly 23 rows; append-only supplements
  // are measured at their then-current checkpoint and update the expectation
  // in the same task. Tests pass smaller counts for synthetic references.
  expectedRowCount = 23,
): V3BaselineArtifact {
  const artifact = JSON.parse(
    authenticateV3Artifact(readGit, reference, 'v3 baseline'),
  ) as V3BaselineArtifact;
  assert.equal(artifact.schema, 1, 'v3 baseline: schema disagreement');
  assertEnvironmentShape(artifact.environments, 'v3 baseline');
  for (const environment of artifact.environments) {
    assert.equal(environment.schema, 1, 'v3 baseline: environment schema disagreement');
    assertV3Provenance(readGit, environment.provenance, reference.commit, 'v3 baseline');
    assert.equal(
      environment.rows.length,
      expectedRowCount,
      'v3 baseline: corpus coverage disagreement',
    );
  }
  // The two environments measured identical deterministic inputs and outcomes;
  // audits never change counters. Environment selection below is labeling, not
  // evidence selection, and this check keeps it that way.
  assert.deepEqual(
    artifact.environments[1].rows,
    artifact.environments[0].rows,
    'v3 baseline: environments disagree on rows',
  );
  return artifact;
}

export function loadLegacyCompiledCnf(
  readGit: (args: string[]) => Buffer,
  reference: ReferenceIdentity = LEGACY_COMPILED_CNF_REFERENCE,
): LegacyCompiledArtifact {
  const artifact = JSON.parse(
    authenticateV3Artifact(readGit, reference, 'legacy compiled snapshots'),
  ) as LegacyCompiledArtifact;
  assert.equal(artifact.schema, 1, 'legacy compiled snapshots: schema disagreement');
  assertEnvironmentShape(artifact.environments, 'legacy compiled snapshots');
  for (const environment of artifact.environments) {
    assert.equal(
      environment.schema,
      1,
      'legacy compiled snapshots: environment schema disagreement',
    );
    assertV3Provenance(
      readGit,
      environment.provenance,
      reference.commit,
      'legacy compiled snapshots',
    );
    assert.equal(
      environment.fixtures.length,
      8,
      'legacy compiled snapshots: fixture coverage disagreement',
    );
  }
  assert.deepEqual(
    artifact.environments[1].fixtures,
    artifact.environments[0].fixtures,
    'legacy compiled snapshots: environments disagree on fixtures',
  );
  return artifact;
}

// Select the recorded environment whose audit state matches the candidate's
// (baseline audits were gated by NODE_ENV; the candidate's by SAT_DEBUG). Rows
// and fixtures are proven identical across environments, so this is a truthful
// provenance label, never evidence selection.
export function selectEnvironment<T extends { provenance: RecordedProvenance }>(
  environments: T[],
  audits: boolean,
  label: string,
): T {
  const matches = environments.filter(
    (environment) => environment.provenance.environment.audits === audits,
  );
  assert.equal(matches.length, 1, `${label}: no recorded environment matches the audit state`);
  const selected = matches[0];
  assert.ok(selected !== undefined);
  return selected;
}
