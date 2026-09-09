// v3 candidate benchmark harness (npm run bench). Authenticates the sealed v3
// baseline and the legacy compiled snapshots exclusively from pinned Git
// commits/blobs/SHA-256s — never from mutable working-tree files — then
// regenerates the pinned 23-row corpus, verifies immutable scenario identities
// and caps before any result comparison, and measures the candidate once per
// scenario at the baseline's calibrated cap.
//
// Two distinct projections (Design § Benchmarking):
// - same-implementation replay: a deterministic byte-compared projection with
//   authenticated reference/input/compiled-output identities, actual candidate
//   source hashes, Node/audit/environment metadata, budgets, outcomes,
//   counters, and model digests. Two runs of one implementation/environment
//   must be byte-identical.
// - cross-implementation behavioral parity: only the shared input/scenario
//   configuration, budgets, outcomes, recorded counters, and model evidence.
//   Differing source/environment provenance is retained and authenticated
//   independently on each side, never copied to manufacture equality.
//
// Gates mode (the default since learned-clause minimization ended the initial
// counter/model-parity window) keeps the immutable-input, outcome, cap, and
// per-call verdict checks and discloses algorithmic counter/model/
// compiler-output deltas. Parity mode (--parity) hard-fails on any behavioral
// mismatch, including compiled snapshots, and is retained for explicit parity
// experiments. A candidate must complete every completed baseline row within
// its cap; a recorded-exhausted row may remain exhausted at that cap or
// complete as a disclosed improvement, and its completed prefix is always
// compared. Absent historical counters stay unrecorded, never zero.
//
// Writes only test/v3-benchmark.json (canonical JSON.stringify(…, null, 2) +
// '\n') and test/v3-benchmark.md (data and comparison tables; wall times are
// informational here and on console, never in the JSON). The prose narrative
// lives in the committed test/v3-benchmark-review.md, which harness runs never
// rewrite. Frozen references and the recorder overlay are never written.

import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { pathToFileURL } from 'node:url';
import type { SolverStats } from '../src/solver.js';
import { comparisonCells, COUNTERS, table } from './bench-comparison.js';
import { digest, inputIdentity, json, sha256 } from './bench-evidence.js';
import { runScenario } from './bench-v3-adapter.js';
import type { Measurement } from './bench-v3-adapter.js';
import { corpus } from './bench-v3-corpus.js';
import type { Scenario } from './bench-v3-corpus.js';
import {
  LEGACY_COMPILED_CNF_REFERENCE,
  loadLegacyCompiledCnf,
  loadV3Baseline,
  selectEnvironment,
  V3_ARTIFACT_COMMIT,
  V3_BASELINE_COMMIT,
  V3_BASELINE_REFERENCE,
  V3_RECORDER_SEAL_COMMIT,
} from './bench-v3-references.js';
import type { BaselineRow, ReferenceIdentity } from './bench-v3-references.js';

const ROOT_URL = new URL('../', import.meta.url);

export const V3_JSON_ARTIFACT = 'test/v3-benchmark.json';
export const V3_MARKDOWN_ARTIFACT = 'test/v3-benchmark.md';

// Counters compared against the sealed v2 baseline: the legacy six plus the
// Phase-2 analysis-work counters. Fields absent from the v2-measured baseline
// (learnedLiterals/minimizedLiterals) are "not recorded", never zero; the
// zeroing path changed in the same task, and Phase 3's createSolverStats must
// include them when it lands.
export const V3_COUNTERS = [
  ...COUNTERS,
  'learnedLiterals',
  'minimizedLiterals',
] as const satisfies readonly (keyof SolverStats)[];

export type V3VerifyMode = 'parity' | 'gates';

// Actual candidate implementation identity: raw working bytes of the sources
// and the harness machinery itself, hashed before the run and re-checked
// after. These hashes truthfully differ from the baseline's recorded v2
// provenance; parity never copies provenance across implementations.
export const snapshotCandidateSources = (): Record<string, string> =>
  Object.fromEntries(
    [
      ...readdirSync(new URL('src/', ROOT_URL), { recursive: true, encoding: 'utf8' })
        .filter((path) => /\.(?:[cm]?[jt]s|json)$/.test(path))
        .map((path) => `src/${path}`),
      'test/bench-evidence.ts',
      'test/bench-v3-adapter.ts',
      'test/bench-v3-corpus.ts',
      'test/bench-v3-references.ts',
      'test/bench-v3.ts',
      'test/helpers.ts',
      'package.json',
      'package-lock.json',
      'tsconfig.json',
      'biome.json',
    ]
      .sort()
      .map((path) => [path, sha256(readFileSync(new URL(path, ROOT_URL)))]),
  );

export interface CandidateEnvironment {
  node: string;
  versions: Record<string, string | undefined>;
  platform: string;
  arch: string;
  nodeEnv: string | null;
  nodeOptions: string | null;
  execArgv: string[];
  // Candidate audits are gated by SAT_DEBUG; the recorded baseline environments
  // were gated by NODE_ENV. The environment selector matches on audit state.
  audits: boolean;
}

export const candidateEnvironment = (): CandidateEnvironment => ({
  node: process.version,
  versions: { ...process.versions },
  platform: process.platform,
  arch: process.arch,
  nodeEnv: process.env.NODE_ENV ?? null,
  nodeOptions: process.env.NODE_OPTIONS ?? null,
  execArgv: [...process.execArgv],
  audits: process.env.SAT_DEBUG === '1',
});

export interface CandidateProvenance {
  sourceSha256: Record<string, string>;
  environment: CandidateEnvironment;
}

// Cross-implementation behavioral parity projection: only the shared
// input/scenario configuration, budgets, outcomes, recorded counters, and
// model evidence. Provenance is absent by construction.
export interface ParityProjection {
  id: string;
  mode: 'single' | 'incremental' | 'enumeration';
  inputSha256: string;
  assumptions: [string, number][];
  callHistory: [string, number][][];
  cap: number;
  compiledSha256: string;
  measurement: Measurement;
}

export function baselineParityProjection(row: BaselineRow): ParityProjection {
  return {
    id: row.id,
    mode: row.mode,
    inputSha256: row.inputSha256,
    assumptions: row.assumptions,
    callHistory: row.calls,
    cap: row.finalCap,
    compiledSha256: row.compiledSha256,
    measurement: row.measurement as Measurement,
  };
}

export function candidateParityProjection(
  scenario: Scenario,
  measurement: Measurement,
): ParityProjection {
  return {
    id: scenario.id,
    mode: scenario.mode,
    inputSha256: digest(inputIdentity(scenario)),
    assumptions: Object.entries(scenario.assumptions),
    callHistory: scenario.calls.map((call) => Object.entries(call)),
    cap: measurement.cap,
    compiledSha256: measurement.compiledSha256,
    measurement,
  };
}

// Same-implementation replay projection: everything deterministic, including
// the candidate's own (truthfully differing) source hashes and environment
// metadata. Byte-compared between runs of one implementation/environment.
export interface ReplayProjection {
  references: {
    baselineCommit: string;
    recorderSealCommit: string;
    artifactCommit: string;
    baseline: ReferenceIdentity;
    legacyCompiledCnf: ReferenceIdentity;
    baselineEnvironment: { nodeEnv: string | null; audits: boolean };
  };
  implementation: CandidateProvenance;
  rows: {
    id: string;
    mode: 'single' | 'incremental' | 'enumeration';
    inputSha256: string;
    compiledSha256: string;
    cap: number;
    measurement: Measurement;
  }[];
}

export interface FieldDelta {
  id: string;
  field: string;
  baseline: unknown;
  candidate: unknown;
}

export interface RowComparison {
  id: string;
  mode: 'single' | 'incremental' | 'enumeration';
  cap: number;
  baselineStatus: string;
  candidateStatus: string;
  construction: Record<
    string,
    { baseline: number | null; candidate: number; delta: number | null }
  >;
  stats: Record<string, { baseline: number | null; candidate: number; delta: number | null }>;
  completedCalls: { baseline: number; candidate: number };
  modelCount: { baseline: number; candidate: number };
  compiledEqual: boolean;
  prefixEqual: boolean;
  failures: FieldDelta[];
  disclosures: FieldDelta[];
}

const counterCells = (
  baseline: SolverStats,
  candidate: SolverStats,
): Record<string, { baseline: number | null; candidate: number; delta: number | null }> =>
  Object.fromEntries(
    V3_COUNTERS.map((counter) => {
      const recorded = baseline[counter] as number | undefined;
      const current = candidate[counter];
      assert.ok(
        Number.isSafeInteger(current) && current >= 0,
        `candidate counter must be a non-negative safe integer: ${counter}`,
      );
      // Absent historical counters stay unrecorded, never zero.
      return [
        counter,
        recorded === undefined
          ? { baseline: null, candidate: current, delta: null }
          : { baseline: recorded, candidate: current, delta: current - recorded },
      ];
    }),
  );

// Compare one candidate measurement against one sealed baseline row under the
// two-projection rules. `parity`-classified fields fail in parity mode and are
// disclosed in gates mode; the rest are hard in every mode.
export function compareRow(
  baseline: ParityProjection,
  candidate: ParityProjection,
  mode: V3VerifyMode,
): RowComparison {
  const failures: FieldDelta[] = [];
  const disclosures: FieldDelta[] = [];
  const record = (parityOnly: boolean, field: string, reference: unknown, current: unknown) => {
    if (JSON.stringify(reference) === JSON.stringify(current)) return;
    const delta: FieldDelta = { id: baseline.id, field, baseline: reference, candidate: current };
    if (parityOnly && mode === 'gates') disclosures.push(delta);
    else failures.push(delta);
  };
  // Stats bags compare per counter, never whole-object: counters absent from
  // the v2-measured baseline stay unrecorded (never zero) and cannot
  // disclose, so a stats-schema addition alone never manufactures a delta.
  const recordStats = (field: string, reference: SolverStats, current: SolverStats) => {
    for (const counter of V3_COUNTERS) {
      const recorded = reference[counter] as number | undefined;
      if (recorded === undefined) continue;
      record(true, `${field}.${counter}`, recorded, current[counter]);
    }
  };
  // Immutable input/scenario configuration and budgets: hard in every mode.
  record(false, 'id', baseline.id, candidate.id);
  record(false, 'mode', baseline.mode, candidate.mode);
  record(false, 'inputSha256', baseline.inputSha256, candidate.inputSha256);
  record(false, 'assumptions', baseline.assumptions, candidate.assumptions);
  record(false, 'callHistory', baseline.callHistory, candidate.callHistory);
  record(false, 'cap', baseline.cap, candidate.cap);
  // Compiler output: parity-compared while compilation is unchanged, disclosed
  // as a compiler-output delta in gates mode — never confused with input drift.
  record(true, 'compiledSha256', baseline.compiledSha256, candidate.compiledSha256);

  const reference = baseline.measurement;
  const current = candidate.measurement;
  const baselineExhausted = reference.status === 'exhausted';
  const candidateExhausted = current.status === 'exhausted';
  if (!baselineExhausted && candidateExhausted) {
    // A candidate must complete every completed baseline within its cap.
    failures.push({
      id: baseline.id,
      field: 'status',
      baseline: reference.status,
      candidate: current.status,
    });
  } else if (baselineExhausted) {
    // The baseline's completed prefix must survive intact; further progress is
    // a disclosed improvement, never a silent parity claim or UNSAT evidence.
    if (
      current.completedCalls < reference.completedCalls ||
      current.modelDigests.length < reference.modelDigests.length
    ) {
      failures.push({
        id: baseline.id,
        field: 'exhausted-prefix coverage',
        baseline: {
          completedCalls: reference.completedCalls,
          models: reference.modelDigests.length,
        },
        candidate: {
          completedCalls: current.completedCalls,
          models: current.modelDigests.length,
        },
      });
    }
    const sameExtent =
      candidateExhausted &&
      current.completedCalls === reference.completedCalls &&
      current.modelDigests.length === reference.modelDigests.length;
    if (!candidateExhausted) {
      disclosures.push({
        id: baseline.id,
        field: 'status (baseline exhausted at its cap)',
        baseline: reference.status,
        candidate: current.status,
      });
    } else if (!sameExtent) {
      disclosures.push({
        id: baseline.id,
        field: 'exhausted-prefix extent',
        baseline: {
          completedCalls: reference.completedCalls,
          models: reference.modelDigests.length,
        },
        candidate: {
          completedCalls: current.completedCalls,
          models: current.modelDigests.length,
        },
      });
    }
    if (sameExtent) {
      recordStats('construction', reference.construction, current.construction);
      recordStats('stats', reference.stats, current.stats);
      record(true, 'orderedCallDigest', reference.orderedCallDigest, current.orderedCallDigest);
      record(true, 'modelSetDigest', reference.modelSetDigest, current.modelSetDigest);
      record(
        true,
        'orderedModelPrefixDigest',
        reference.orderedModelPrefixDigest,
        current.orderedModelPrefixDigest,
      );
    }
  } else {
    record(false, 'status', reference.status, current.status);
    recordStats('construction', reference.construction, current.construction);
    recordStats('stats', reference.stats, current.stats);
    record(false, 'completedCalls', reference.completedCalls, current.completedCalls);
    record(false, 'unexecutedCalls', reference.unexecutedCalls, current.unexecutedCalls);
    record(true, 'orderedCallDigest', reference.orderedCallDigest, current.orderedCallDigest);
    record(false, 'modelCount', reference.modelCount, current.modelCount);
    record(true, 'modelDigest', reference.modelDigest, current.modelDigest);
    // The order-insensitive model SET is semantic (hard) only for a completed
    // enumeration, where it covers every model. A single-shot set is the
    // singleton first model and an incremental set derives from per-call
    // first models — algorithmic choices already disclosed via the modelDigest
    // fields, never a semantic verdict.
    if (baseline.mode === 'enumeration') {
      record(false, 'modelSetDigest', reference.modelSetDigest, current.modelSetDigest);
    } else {
      record(true, 'modelSetDigest', reference.modelSetDigest, current.modelSetDigest);
    }
    record(
      true,
      'orderedModelPrefixDigest',
      reference.orderedModelPrefixDigest,
      current.orderedModelPrefixDigest,
    );
  }
  // Completed-prefix evidence in every case: per-call verdicts are semantic
  // (hard in every mode); per-call counters and model digests follow the mode.
  // An interrupted call (status 'exhausted', always last) carries no verdict or
  // model to compare; the candidate's corresponding call may legitimately
  // complete, so only the baseline's completed calls pin the prefix.
  let prefixEqual = true;
  for (const [index, call] of reference.calls.entries()) {
    if (call.status === 'exhausted') continue;
    const candidateCall = current.calls[index];
    if (candidateCall === undefined) {
      failures.push({
        id: baseline.id,
        field: `calls[${index}]`,
        baseline: call,
        candidate: null,
      });
      prefixEqual = false;
      continue;
    }
    const before = failures.length + disclosures.length;
    record(false, `calls[${index}].status`, call.status, candidateCall.status);
    record(true, `calls[${index}].modelDigest`, call.modelDigest, candidateCall.modelDigest);
    recordStats(`calls[${index}].stats`, call.stats, candidateCall.stats);
    if (failures.length + disclosures.length !== before) prefixEqual = false;
  }
  for (const [index, modelDigest] of reference.modelDigests.entries()) {
    const before = failures.length + disclosures.length;
    record(true, `modelDigests[${index}]`, modelDigest, current.modelDigests[index] ?? null);
    if (failures.length + disclosures.length !== before) prefixEqual = false;
  }
  return {
    id: baseline.id,
    mode: baseline.mode,
    cap: baseline.cap,
    baselineStatus: reference.status,
    candidateStatus: current.status,
    construction: counterCells(reference.construction, current.construction),
    stats: counterCells(reference.stats, current.stats),
    completedCalls: { baseline: reference.completedCalls, candidate: current.completedCalls },
    modelCount: { baseline: reference.modelCount, candidate: current.modelCount },
    compiledEqual: baseline.compiledSha256 === candidate.compiledSha256,
    prefixEqual,
    failures,
    disclosures,
  };
}

// Immutable scenario identities and caps, verified for the whole corpus before
// any scenario runs. Input drift is never a result comparison.
export function verifyScenarioInputs(scenarios: Scenario[], rows: BaselineRow[]): void {
  assert.equal(
    scenarios.length,
    rows.length,
    `v3 corpus coverage disagreement: ${scenarios.length} scenarios vs ${rows.length} baseline rows`,
  );
  for (const [index, scenario] of scenarios.entries()) {
    const row = rows[index];
    assert.ok(row !== undefined);
    assert.equal(scenario.id, row.id, `v3 corpus order disagreement at position ${index}`);
    assert.equal(scenario.mode, row.mode, `${row.id}: scenario mode disagreement`);
    assert.equal(
      digest(inputIdentity(scenario)),
      row.inputSha256,
      `${row.id}: input identity drift (definition, AST, assumptions, or call history)`,
    );
    assert.deepEqual(
      Object.entries(scenario.assumptions),
      row.assumptions,
      `${row.id}: ordered assumption entries drifted`,
    );
    assert.deepEqual(
      scenario.calls.map((call) => Object.entries(call)),
      row.calls,
      `${row.id}: ordered call history drifted`,
    );
    assert.ok(
      Number.isSafeInteger(row.finalCap) && row.finalCap > 0,
      `${row.id}: baseline cap must be a positive safe integer`,
    );
  }
}

export interface V3HarnessOptions {
  readGit?: ((args: string[]) => Buffer) | undefined;
  identities?:
    | {
        baseline?: ReferenceIdentity | undefined;
        legacyCompiledCnf?: ReferenceIdentity | undefined;
      }
    | undefined;
  corpus?: (() => Scenario[]) | undefined;
  run?: ((scenario: Scenario, cap: number) => Measurement) | undefined;
  environment?: (() => CandidateEnvironment) | undefined;
  snapshotSources?: (() => Record<string, string>) | undefined;
  mode?: V3VerifyMode | undefined;
  expectedRows?: number | undefined;
  now?: (() => number) | undefined;
  write?: ((path: string, content: string) => void) | undefined;
  log?: ((message: string) => void) | undefined;
}

export interface V3HarnessResult {
  artifact: unknown;
  markdown: string;
  comparisons: RowComparison[];
  replay: ReplayProjection;
}

export function runV3Benchmark({
  readGit = (args) => execFileSync('git', args, { cwd: ROOT_URL, maxBuffer: 128 * 1024 * 1024 }),
  identities = {},
  corpus: makeCorpus = corpus,
  run = runScenario,
  environment = candidateEnvironment,
  snapshotSources = snapshotCandidateSources,
  mode = 'gates',
  expectedRows,
  now = () => performance.now(),
  write,
  log = console.log,
}: V3HarnessOptions = {}): V3HarnessResult {
  const baselineIdentity = identities.baseline ?? V3_BASELINE_REFERENCE;
  const legacyIdentity = identities.legacyCompiledCnf ?? LEGACY_COMPILED_CNF_REFERENCE;
  const sourcesBefore = snapshotSources();
  const candidateEnv = environment();

  // References come exclusively from authenticated commit bytes, never mutable
  // working-tree artifacts.
  // Expected coverage defaults to the sealed version-1 corpus size; the option
  // exists for tests with synthetic references.
  const baselineArtifact = loadV3Baseline(readGit, baselineIdentity, expectedRows ?? 23);
  loadLegacyCompiledCnf(readGit, legacyIdentity);
  const baselineEnvironment = selectEnvironment(
    baselineArtifact.environments,
    candidateEnv.audits,
    'v3 baseline',
  );
  const baselineRows = baselineEnvironment.rows;

  const head = readGit(['rev-parse', 'HEAD']).toString('utf8').trim();
  log(
    `v3 candidate benchmark harness (${mode} mode).\n` +
      `Sealed baseline: ${baselineIdentity.commit}:${baselineIdentity.path} ` +
      `(blob ${baselineIdentity.gitBlob}, SHA-256 ${baselineIdentity.sha256})\n` +
      `Legacy compiled snapshots: ${legacyIdentity.commit}:${legacyIdentity.path} ` +
      `(blob ${legacyIdentity.gitBlob}, SHA-256 ${legacyIdentity.sha256})\n` +
      `Recorded baseline environment: NODE_ENV ${
        baselineEnvironment.provenance.environment.nodeEnv ?? '(unset)'
      } (audits ${baselineEnvironment.provenance.environment.audits}); ` +
      `candidate audits ${candidateEnv.audits}\n` +
      `Current HEAD (context, not implementation identity): ${head}; Node ${candidateEnv.node}\n`,
  );

  const scenarios = makeCorpus();
  verifyScenarioInputs(scenarios, baselineRows);

  const rows: ReplayProjection['rows'] = [];
  const comparisons: RowComparison[] = [];
  const wallMs: { id: string; wallMs: number }[] = [];
  for (const [index, scenario] of scenarios.entries()) {
    const row = baselineRows[index];
    assert.ok(row !== undefined);
    const start = now();
    const measurement = run(scenario, row.finalCap);
    wallMs.push({ id: scenario.id, wallMs: now() - start });
    assert.equal(measurement.id, row.id);
    assert.equal(measurement.inputSha256, row.inputSha256, `${row.id}: input identity drift`);
    const comparison = compareRow(
      baselineParityProjection(row),
      candidateParityProjection(scenario, measurement),
      mode,
    );
    comparisons.push(comparison);
    rows.push({
      id: scenario.id,
      mode: scenario.mode,
      inputSha256: measurement.inputSha256,
      compiledSha256: measurement.compiledSha256,
      cap: row.finalCap,
      measurement,
    });
    log(
      `${scenario.id}: ${measurement.status}, cap ${row.finalCap}, conflicts ` +
        `${measurement.stats.conflicts}, ${wallMs[index]?.wallMs.toFixed(0)} ms (informational)`,
    );
  }
  assert.deepEqual(
    snapshotSources(),
    sourcesBefore,
    'candidate implementation changed during the run; rerun before comparing',
  );

  const replay: ReplayProjection = {
    references: {
      baselineCommit: V3_BASELINE_COMMIT,
      recorderSealCommit: V3_RECORDER_SEAL_COMMIT,
      artifactCommit: V3_ARTIFACT_COMMIT,
      baseline: baselineIdentity,
      legacyCompiledCnf: legacyIdentity,
      baselineEnvironment: {
        nodeEnv: baselineEnvironment.provenance.environment.nodeEnv,
        audits: baselineEnvironment.provenance.environment.audits,
      },
    },
    implementation: { sourceSha256: sourcesBefore, environment: candidateEnv },
    rows,
  };
  const failures = comparisons.flatMap((comparison) => comparison.failures);
  const disclosures = comparisons.flatMap((comparison) => comparison.disclosures);
  const comparisonSection = comparisons.map(({ failures: _f, disclosures: _d, ...rest }) => rest);
  const artifact = {
    schema: 1,
    generatedBy: 'test/bench-v3.ts (npm run bench)',
    mode,
    context: {
      head,
      note: 'Machine-generated data and comparison tables only; the narrative lives in the committed test/v3-benchmark-review.md, never rewritten by harness runs. Timing is console/Markdown information only.',
    },
    replay,
    comparison: { rows: comparisonSection, disclosures },
  };
  const markdown = createV3Markdown({
    mode,
    head,
    candidateEnv,
    baselineIdentity,
    legacyIdentity,
    baselineEnvironmentNodeEnv: baselineEnvironment.provenance.environment.nodeEnv,
    comparisons,
    disclosures,
    wallMs,
  });

  const summary = (delta: FieldDelta) =>
    `${delta.id}: ${delta.field} (baseline ${JSON.stringify(delta.baseline)?.slice(0, 200)}, ` +
    `candidate ${JSON.stringify(delta.candidate)?.slice(0, 200)})`;
  if (disclosures.length > 0) {
    log(`\nDisclosed deltas (${disclosures.length}):\n${disclosures.map(summary).join('\n')}`);
  }
  if (failures.length > 0) {
    throw new Error(
      `v3 candidate benchmark failed in ${mode} mode (${
        failures.length
      } mismatches); nothing was written:\n${failures.map(summary).join('\n')}`,
    );
  }
  log(
    mode === 'parity'
      ? `\nParity verified: all ${rows.length} scenarios match the sealed v2 baseline on inputs, caps, outcomes, counters, model evidence, and compiled snapshots.`
      : `\nGates verified: immutable inputs, outcomes, caps, and per-call verdicts passed; ${disclosures.length} disclosed deltas are non-fatal.`,
  );
  if (write !== undefined) {
    write(V3_JSON_ARTIFACT, json(artifact));
    write(V3_MARKDOWN_ARTIFACT, markdown);
    log(`Wrote ${V3_JSON_ARTIFACT} and ${V3_MARKDOWN_ARTIFACT}.`);
  } else {
    log('Nothing was written.');
  }
  return { artifact, markdown, comparisons, replay };
}

function createV3Markdown({
  mode,
  head,
  candidateEnv,
  baselineIdentity,
  legacyIdentity,
  baselineEnvironmentNodeEnv,
  comparisons,
  disclosures,
  wallMs,
}: {
  mode: V3VerifyMode;
  head: string;
  candidateEnv: CandidateEnvironment;
  baselineIdentity: ReferenceIdentity;
  legacyIdentity: ReferenceIdentity;
  baselineEnvironmentNodeEnv: string | null;
  comparisons: RowComparison[];
  disclosures: FieldDelta[];
  wallMs: { id: string; wallMs: number }[];
}): string {
  const notes = [
    'v3 candidate evidence only: behavioral comparison against the sealed v2 baseline, not a speedup gate. The v2 baseline was measured by the frozen recorder overlay at ae1a4fe in an intentionally overlaid worktree; this candidate runs the current tree directly.',
    'References are authenticated exclusively from pinned Git commits/blobs/SHA-256s; mutable working-tree reference files are never read. Embedded historical source/tool/overlay provenance is re-verified against Git bytes at the baseline and recorder-seal commits.',
    'Immutable scenario identities (definition, AST, ordered assumptions, ordered call history) and calibrated caps are verified before any result comparison. Input drift is a failure in every mode; legitimate compiler-output changes are disclosed separately from inputs.',
    'Same-implementation replay byte-compares the deterministic replay projection (reference/input/compiled-output identities, actual source hashes, Node/audit/environment metadata, budgets, outcomes, counters, model digests). Cross-implementation parity compares only shared behavior; candidate provenance truthfully differs and is never copied from the baseline.',
    'A candidate must complete every completed baseline row within its cap. A recorded-exhausted baseline row may remain exhausted at that cap or complete as a disclosed improvement; its completed prefix is always compared, and exhaustion is never UNSAT evidence.',
    'Fields absent from the v2-measured baseline are unrecorded, never zero: the Phase-2 analysis-work counters (learnedLiterals, minimizedLiterals) report candidate values only. The other six counters are the complete v2 counter set.',
    'learnedClausesCurrent is the final live learned-clause gauge. Incremental construction stats are recorded separately; per-call work counters sum with construction to scenario totals.',
    'Ratios are baseline/candidate, rounded to two decimals, not wall-time speedups. Wall times are informational only and never enter the JSON artifact or byte-compared projections.',
  ];
  const counterRows = comparisons.flatMap((comparison) =>
    V3_COUNTERS.map((counter) => {
      const cell = comparison.stats[counter];
      return [
        comparison.id,
        counter,
        // Absent historical counters stay "not recorded", never zero.
        ...comparisonCells(cell?.baseline ?? undefined, cell?.candidate, 'candidate'),
      ];
    }),
  );
  return `${[
    '# v3 Candidate Benchmark Comparison',
    '',
    `Generated by \`npm run bench\` (test/bench-v3.ts) in ${mode} mode. Machine-generated data and`,
    'comparison tables only; the prose narrative lives in `test/v3-benchmark-review.md`, which harness',
    'runs never rewrite. No timestamps are stored; wall times below are informational only.',
    '',
    '## Provenance',
    '',
    `- v3 baseline reference: \`${baselineIdentity.commit}:${baselineIdentity.path}\``,
    `- Verified Git blob: \`${baselineIdentity.gitBlob}\`; SHA-256: \`${baselineIdentity.sha256}\``,
    `- Legacy compiled snapshots: \`${legacyIdentity.commit}:${legacyIdentity.path}\``,
    `- Verified Git blob: \`${legacyIdentity.gitBlob}\`; SHA-256: \`${legacyIdentity.sha256}\``,
    `- Pristine v2 baseline commit: \`${V3_BASELINE_COMMIT}\`; recorder seal: \`${V3_RECORDER_SEAL_COMMIT}\``,
    `- Recorded baseline environment: NODE_ENV \`${
      baselineEnvironmentNodeEnv ?? '(unset)'
    }\` (audit-state matched)`,
    `- Current HEAD (context, not implementation identity): \`${head}\``,
    `- Candidate Node: \`${candidateEnv.node}\`; NODE_ENV: \`${
      candidateEnv.nodeEnv ?? '(unset)'
    }\`; SAT_DEBUG audits: \`${candidateEnv.audits}\``,
    '',
    '## Interpretation And Limits',
    '',
    ...notes.map((note) => `- ${note}`),
    '',
    '## Scenario Outcomes',
    '',
    table(
      [
        'scenario',
        'mode',
        'cap',
        'baseline status',
        'candidate status',
        'models (baseline/candidate)',
      ],
      comparisons.map((comparison) => [
        comparison.id,
        comparison.mode,
        comparison.cap,
        comparison.baselineStatus,
        comparison.candidateStatus,
        `${comparison.modelCount.baseline}/${comparison.modelCount.candidate}`,
      ]),
    ),
    '',
    '## Counters: Sealed Baseline Vs Candidate',
    '',
    table(
      [
        'scenario',
        'counter',
        'baseline',
        'candidate',
        'delta (candidate - baseline)',
        'ratio (baseline / candidate)',
        'count change',
      ],
      counterRows,
    ),
    '',
    '## Disclosed Deltas',
    '',
    disclosures.length === 0
      ? 'No disclosed deltas: behavior matches the sealed baseline exactly under the compared projections.'
      : table(
          ['scenario', 'field', 'baseline', 'candidate'],
          disclosures.map((delta) => [
            delta.id,
            delta.field,
            `\`${JSON.stringify(delta.baseline)?.slice(0, 120)}\``,
            `\`${JSON.stringify(delta.candidate)?.slice(0, 120)}\``,
          ]),
        ),
    '',
    '## Wall Times (Informational Only)',
    '',
    table(
      ['scenario', 'candidate wall ms'],
      wallMs.map(({ id, wallMs: ms }) => [id, ms.toFixed(0)]),
    ),
    '',
  ].join('\n')}`;
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  runV3Benchmark({
    mode: process.argv.includes('--parity') ? 'parity' : 'gates',
    write: (path, content) => writeFileSync(new URL(`../${path}`, import.meta.url), content),
  });
}
