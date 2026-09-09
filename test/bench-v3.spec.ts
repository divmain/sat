// Tests for the v3 candidate harness (test/bench-v3.ts) and its supporting
// evidence/corpus/adapter/reference modules. Synthetic references are built by
// self-recording tiny scenarios through the REAL candidate adapter, then served
// from in-memory "Git bytes" with recomputed identities; historical source and
// overlay provenance entries are the real sealed ones, authenticated against
// this repository's actual Git history. Nothing here writes repo artifacts or
// mutates frozen references.

import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { describe, it } from 'node:test';
import { compile } from '../src/compile.js';
import type { CompiledCnf } from '../src/compile.js';
import { not, or, Value } from '../src/expr.js';
import type { VariableAssignments } from '../src/expr.js';
import { benchmarkFixtures } from './bench-comparison.js';
import {
  compiledSnapshot,
  digest,
  inputIdentity,
  json,
  modelEvidence,
  sha256,
} from './bench-evidence.js';
import { runScenario } from './bench-v3-adapter.js';
import type { Measurement } from './bench-v3-adapter.js';
import { corpus, pairs } from './bench-v3-corpus.js';
import type { Scenario } from './bench-v3-corpus.js';
import {
  LEGACY_COMPILED_CNF_REFERENCE,
  loadLegacyCompiledCnf,
  loadV3Baseline,
  V3_ARTIFACT_COMMIT,
  V3_BASELINE_COMMIT,
  V3_BASELINE_REFERENCE,
  V3_RECORDER_SEAL_COMMIT,
} from './bench-v3-references.js';
import type {
  BaselineRow,
  LegacyCompiledArtifact,
  RecordedMeasurement,
  ReferenceIdentity,
  V3BaselineArtifact,
} from './bench-v3-references.js';
import {
  baselineParityProjection,
  candidateParityProjection,
  runV3Benchmark,
  verifyScenarioInputs,
} from './bench-v3.js';
import type { V3HarnessOptions } from './bench-v3.js';
import { cnfToExpr, mulberry32, phpCnf, random3Cnf } from './helpers.js';

const ROOT_URL = new URL('../', import.meta.url);
const realGit = (args: string[]): Buffer =>
  execFileSync('git', args, { cwd: ROOT_URL, maxBuffer: 128 * 1024 * 1024 });

const REAL_BASELINE = JSON.parse(
  realGit(['show', `${V3_ARTIFACT_COMMIT}:test/v3-baseline.json`]).toString(),
) as V3BaselineArtifact;
const REAL_LEGACY = JSON.parse(
  realGit(['show', `${V3_ARTIFACT_COMMIT}:test/legacy-compiled-cnf.json`]).toString(),
) as LegacyCompiledArtifact;

// ---------------------------------------------------------------------------
// Synthetic reference construction
// ---------------------------------------------------------------------------

const tinyCorpus = (): Scenario[] => [
  {
    id: 'tiny_sat',
    mode: 'single',
    definition: { version: 1, note: 'two independent pairs' },
    expr: pairs(2),
    assumptions: {},
    calls: [],
  },
  {
    id: 'tiny_unsat',
    mode: 'single',
    definition: { version: 1, note: 'php(3,2) via legacy cnfToExpr' },
    expr: cnfToExpr(phpCnf(3, 2)),
    assumptions: {},
    calls: [],
  },
  {
    id: 'tiny_incremental',
    mode: 'incremental',
    definition: { version: 1, note: 'three assumption calls on one persistent core' },
    expr: cnfToExpr(random3Cnf(mulberry32(7), 8, 20)),
    assumptions: {},
    calls: [
      { v1: Value.TRUE, v2: Value.FALSE },
      { v3: Value.FALSE, v5: Value.TRUE },
      { v8: Value.TRUE },
    ],
  },
  {
    id: 'tiny_enum',
    mode: 'enumeration',
    definition: { version: 1, note: 'pairs(2) has 9 models' },
    expr: pairs(2),
    assumptions: {},
    calls: [],
  },
];

// Record a well-formed synthetic baseline row with the same calibration shape
// the frozen recorder used: one C0 trial, then two agreeing final-cap runs.
const recordRow = (scenario: Scenario): BaselineRow => {
  const trial = runScenario(scenario, 100_000);
  assert.notEqual(trial.status, 'exhausted', `synthetic scenario must complete: ${scenario.id}`);
  const finalCap = Math.max(10 * trial.stats.conflicts, 1_000);
  const measurement = runScenario(scenario, finalCap);
  const confirmation = runScenario(scenario, finalCap);
  assert.equal(json(confirmation), json(measurement), 'synthetic recording must be deterministic');
  return {
    id: scenario.id,
    mode: scenario.mode,
    definition: scenario.definition,
    inputSha256: digest(inputIdentity(scenario)),
    assumptions: Object.entries(scenario.assumptions),
    calls: scenario.calls.map((call) => Object.entries(call)),
    compiledSha256: measurement.compiledSha256,
    calibration: [trial],
    finalCap,
    measurement,
    confirmationSha256: digest(confirmation),
  };
};

const syntheticBaselineText = (rows: BaselineRow[]): string =>
  json({
    schema: 1,
    environments: [0, 1].map((index) => ({
      schema: 1,
      provenance: REAL_BASELINE.environments[index]?.provenance,
      rows,
    })),
  });

const syntheticLegacyText = (): string =>
  json({
    schema: 1,
    environments: [0, 1].map((index) => ({
      schema: 1,
      provenance: REAL_LEGACY.environments[index]?.provenance,
      fixtures: benchmarkFixtures().map(({ expr, fixture }) => {
        const snapshot = compiledSnapshot(compile(expr));
        return {
          id: fixture.name,
          inputSha256: fixture.fixtureSha256,
          assumptions: Object.entries(fixture.assumptions),
          cap: fixture.maxConflicts,
          compiledSha256: digest(snapshot),
          snapshot,
        };
      }),
    })),
  });

const identityFor = (text: string, path: string): ReferenceIdentity => ({
  commit: V3_ARTIFACT_COMMIT,
  path,
  gitBlob: createHash('sha1')
    .update(`blob ${Buffer.byteLength(text)}\0`)
    .update(text)
    .digest('hex'),
  sha256: sha256(text),
});

// Intercept exactly the two artifact reads; every other Git query (commit
// verification, provenance bytes, ancestry, HEAD) goes to the real repository.
const servingGit =
  (files: Record<string, string | Error>) =>
  (args: string[]): Buffer => {
    if (args[0] === 'show' && args[1] !== undefined && Object.hasOwn(files, args[1])) {
      const served = files[args[1]];
      if (served instanceof Error) throw served;
      return Buffer.from(served);
    }
    return realGit(args);
  };

interface HarnessControl {
  options: V3HarnessOptions;
  scenarios: Scenario[];
  rows: BaselineRow[];
  writes: Map<string, string>;
  logs: string[];
  runCalls: { scenario: Scenario; cap: number }[];
}

function harnessControl({
  mutateRows,
  mutateArtifact,
  ...overrides
}: {
  mutateRows?: ((rows: BaselineRow[]) => void) | undefined;
  mutateArtifact?: ((artifact: V3BaselineArtifact) => void) | undefined;
} & Partial<V3HarnessOptions> = {}): HarnessControl {
  const scenarios = tinyCorpus();
  const rows = scenarios.map(recordRow);
  mutateRows?.(rows);
  const artifact = JSON.parse(syntheticBaselineText(rows)) as V3BaselineArtifact;
  mutateArtifact?.(artifact);
  const baselineText = json(artifact);
  const legacyText = syntheticLegacyText();
  const options: V3HarnessOptions = {
    readGit: servingGit({
      [`${V3_ARTIFACT_COMMIT}:test/v3-baseline.json`]: baselineText,
      [`${V3_ARTIFACT_COMMIT}:test/legacy-compiled-cnf.json`]: legacyText,
    }),
    identities: {
      baseline: identityFor(baselineText, 'test/v3-baseline.json'),
      legacyCompiledCnf: identityFor(legacyText, 'test/legacy-compiled-cnf.json'),
    },
    corpus: () => scenarios,
    expectedRows: scenarios.length,
    environment: () => ({
      node: 'v0.0.0-synthetic',
      versions: { node: '0.0.0' },
      platform: 'synthetic',
      arch: 'synthetic',
      nodeEnv: null,
      nodeOptions: null,
      execArgv: [],
      audits: false,
    }),
    snapshotSources: () => ({ 'candidate.ts': 'f'.repeat(64) }),
    now: () => 0,
    ...overrides,
  };
  const writes = new Map<string, string>();
  const logs: string[] = [];
  const runCalls: { scenario: Scenario; cap: number }[] = [];
  options.write = (path, content) => {
    writes.set(path, content);
  };
  options.log = (message) => {
    logs.push(message);
  };
  const innerRun = options.run ?? runScenario;
  options.run = (scenario, cap) => {
    runCalls.push({ scenario, cap });
    return innerRun(scenario, cap);
  };
  return { options, scenarios, rows, writes, logs, runCalls };
}

// Fabricate an exhausted incremental baseline row from a completed recording:
// the first call completed; the second was interrupted by the cap; the rest
// never executed. The interrupted call carries partial counters, no verdict.
const exhaustIncrementalRow = (row: BaselineRow): void => {
  const measurement = structuredClone(row.measurement) as RecordedMeasurement;
  const [first, second] = measurement.calls;
  assert.ok(first !== undefined && second !== undefined);
  measurement.status = 'exhausted';
  measurement.calls = [
    first,
    { index: second.index, status: 'exhausted', modelDigest: null, stats: { ...second.stats } },
  ];
  measurement.completedCalls = 1;
  measurement.unexecutedCalls = row.calls.length - 2;
  measurement.orderedCallDigest = digest(
    measurement.calls.map(({ index, status, modelDigest }) => ({ index, status, modelDigest })),
  );
  measurement.stats = { ...measurement.stats, conflicts: row.finalCap };
  measurement.cap = row.finalCap;
  row.measurement = measurement;
};

// ---------------------------------------------------------------------------

describe('v3 reference authentication', () => {
  it('accepts the real sealed references from Git bytes', () => {
    const baseline = loadV3Baseline(realGit);
    assert.equal(baseline.environments.length, 2);
    assert.equal(baseline.environments[0]?.rows.length, 23);
    const legacy = loadLegacyCompiledCnf(realGit);
    assert.equal(legacy.environments[0]?.fixtures.length, 8);
  });

  it('rejects modified artifact bytes against the pinned blob before parsing', () => {
    const control = harnessControl();
    const readGit = servingGit({
      [`${V3_ARTIFACT_COMMIT}:test/v3-baseline.json`]: '{}',
      [`${V3_ARTIFACT_COMMIT}:test/legacy-compiled-cnf.json`]: '{}',
    });
    assert.throws(
      () => loadV3Baseline(readGit, control.options.identities?.baseline),
      /v3 baseline reference blob mismatch/,
    );
  });

  it('rejects non-canonical reference JSON even with recomputed identity', () => {
    const control = harnessControl();
    const rowsText = json(control.rows);
    const artifact = {
      schema: 1,
      environments: [0, 1].map((index) => ({
        schema: 1,
        provenance: REAL_BASELINE.environments[index]?.provenance,
        rows: JSON.parse(rowsText) as BaselineRow[],
      })),
    };
    const sloppy = `${JSON.stringify(artifact)}\n`;
    const identity = identityFor(sloppy, 'test/v3-baseline.json');
    const readGit = servingGit({ [`${V3_ARTIFACT_COMMIT}:test/v3-baseline.json`]: sloppy });
    assert.throws(() => loadV3Baseline(readGit, identity), /not canonical/);
  });

  it('rejects tampered embedded source provenance against baseline-commit Git bytes', () => {
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const provenance = artifact.environments[0]?.provenance;
              assert.ok(provenance !== undefined);
              const source = provenance.sources[0];
              assert.ok(source !== undefined);
              source.sha256 = '0'.repeat(64);
            },
          }).options,
        ),
      /v3 baseline: src\/compile\.ts SHA-256 mismatch at ae1a4fe/,
    );
  });

  it('rejects tampered overlay provenance against the recorder seal commit', () => {
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const overlayFile = artifact.environments[0]?.provenance.overlayFiles[0];
              assert.ok(overlayFile !== undefined);
              overlayFile.blob = '0'.repeat(40);
            },
          }).options,
        ),
      /v3 baseline: test\/v3-baseline-overlay\/README\.md blob mismatch at 2ba0a39/,
    );
  });

  it('requires declared overlay provenance and the pinned historical commits', () => {
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const provenance = artifact.environments[0]?.provenance;
              assert.ok(provenance !== undefined);
              provenance.overlay = false;
            },
          }).options,
        ),
      /overlaid provenance must be declared/,
    );
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const provenance = artifact.environments[0]?.provenance;
              assert.ok(provenance !== undefined);
              provenance.recorderSealCommit = '0'.repeat(40);
            },
          }).options,
        ),
      /recorder seal disagreement/,
    );
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const provenance = artifact.environments[0]?.provenance;
              assert.ok(provenance !== undefined);
              provenance.baselineCommit = '0'.repeat(40);
            },
          }).options,
        ),
      /baseline commit disagreement/,
    );
  });

  it('fails closed when required history is unavailable', () => {
    const control = harnessControl();
    const inner = control.options.readGit;
    assert.ok(inner !== undefined);
    const unavailable = new Error('missing pinned reference');
    assert.throws(
      () =>
        loadV3Baseline(
          (args) => {
            if (args[0] === 'rev-parse') throw unavailable;
            return inner(args);
          },
          control.options.identities?.baseline,
          4,
        ),
      /missing pinned reference/,
    );
    // The recorder seal must be an ancestor of the artifact commit.
    assert.throws(
      () =>
        loadV3Baseline(
          (args) => {
            if (args[0] === 'merge-base') throw unavailable;
            return inner(args);
          },
          control.options.identities?.baseline,
          4,
        ),
      /missing pinned reference/,
    );
  });

  it('rejects cross-environment disagreement and malformed environment shape', () => {
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              const row = artifact.environments[1]?.rows[0];
              assert.ok(row !== undefined);
              row.finalCap += 1;
            },
          }).options,
        ),
      /environments disagree on rows/,
    );
    assert.throws(
      () =>
        runV3Benchmark(
          harnessControl({
            mutateArtifact: (artifact) => {
              artifact.environments.pop();
            },
          }).options,
        ),
      /exactly two recorded environments/,
    );
  });
});

describe('v3 immutable input verification', () => {
  it('verifies scenario identities, order, assumptions, calls, and caps before any run', () => {
    const control = harnessControl();
    verifyScenarioInputs(control.scenarios, control.rows);
    const result = runV3Benchmark(control.options);
    assert.equal(control.runCalls.length, control.scenarios.length);
    assert.ok(
      control.runCalls.every(({ cap }, index) => cap === control.rows[index]?.finalCap),
      'each scenario runs at its sealed baseline cap',
    );
    assert.ok(result.comparisons.every((comparison) => comparison.failures.length === 0));
  });

  it('rejects AST drift as input drift, in every mode, before any result comparison', () => {
    for (const mode of ['parity', 'gates'] as const) {
      const drifted = tinyCorpus();
      const first = drifted[0];
      assert.ok(first !== undefined);
      first.expr = or(first.expr, not('zzz'));
      const control = harnessControl({ mode, corpus: () => drifted });
      assert.throws(
        () => runV3Benchmark(control.options),
        /tiny_sat: input identity drift/,
        `mode ${mode}`,
      );
      assert.equal(control.runCalls.length, 0, 'no scenario may run after input drift');
    }
  });

  it('rejects corpus coverage and order disagreements', () => {
    const control = harnessControl();
    assert.throws(
      () => verifyScenarioInputs(control.scenarios.slice(1), control.rows),
      /coverage disagreement/,
    );
    const swapped = [...control.scenarios];
    const a = swapped[0];
    const b = swapped[1];
    assert.ok(a !== undefined && b !== undefined);
    swapped[0] = b;
    swapped[1] = a;
    assert.throws(
      () => verifyScenarioInputs(swapped, control.rows),
      /order disagreement at position 0/,
    );
  });

  it('rejects assumption and call-history drift distinctly from AST drift', () => {
    const control = harnessControl();
    const tamperedAssumptions = tinyCorpus();
    const sat = tamperedAssumptions[0];
    assert.ok(sat !== undefined);
    sat.assumptions = { a1: Value.TRUE };
    assert.throws(
      () => verifyScenarioInputs(tamperedAssumptions, control.rows),
      /input identity drift/,
    );
    // A definition-only change (no AST change) is still input drift.
    const tamperedDefinition = tinyCorpus();
    const target = tamperedDefinition[0];
    assert.ok(target !== undefined);
    target.definition = { ...target.definition, note: 'changed after sealing' };
    assert.throws(
      () => verifyScenarioInputs(tamperedDefinition, control.rows),
      /tiny_sat: input identity drift \(definition, AST, assumptions, or call history\)/,
    );
    const tamperedCalls = tinyCorpus();
    const incremental = tamperedCalls[2];
    assert.ok(incremental !== undefined);
    incremental.calls = [...incremental.calls, { v4: Value.TRUE }];
    assert.throws(() => verifyScenarioInputs(tamperedCalls, control.rows), /input identity drift/);
  });
});

describe('v3 behavioral comparison', () => {
  it('runs in gates mode by default: the initial parity window has ended', () => {
    const control = harnessControl();
    const result = runV3Benchmark(control.options);
    assert.match(control.logs.join('\n'), /v3 candidate benchmark harness \(gates mode\)/);
    assert.match(control.logs.join('\n'), /Gates verified/);
    assert.equal((result.artifact as { mode: string }).mode, 'gates');
    assert.ok(result.comparisons.every((comparison) => comparison.failures.length === 0));
    assert.ok(result.comparisons.every((comparison) => comparison.disclosures.length === 0));
  });

  it('passes exact parity on a self-recorded synthetic baseline and writes canonical artifacts', () => {
    const control = harnessControl({ mode: 'parity' });
    const result = runV3Benchmark(control.options);
    assert.deepEqual([...control.writes.keys()].sort(), [
      'test/v3-benchmark.json',
      'test/v3-benchmark.md',
    ]);
    const text = control.writes.get('test/v3-benchmark.json');
    assert.ok(text !== undefined);
    // Canonical machine JSON: exact JSON.stringify(…, null, 2) + '\n' bytes.
    assert.equal(json(JSON.parse(text)), text);
    assert.match(text, /"schema": 1/);
    const markdown = control.writes.get('test/v3-benchmark.md');
    assert.ok(markdown !== undefined);
    assert.match(markdown, /# v3 Candidate Benchmark Comparison/);
    assert.match(markdown, /Counters: Sealed Baseline Vs Candidate/);
    assert.match(markdown, /No disclosed deltas/);
    // The candidate's own provenance is recorded truthfully, not copied.
    assert.match(text, /v0\.0\.0-synthetic/);
    assert.match(control.logs.join('\n'), /Parity verified: all 4 scenarios/);
    assert.equal(result.comparisons.length, 4);
  });

  it('distinguishes legitimate compiler-output deltas from input drift', () => {
    for (const mode of ['parity', 'gates'] as const) {
      const control = harnessControl({
        mode,
        run: (scenario, cap) => ({
          ...runScenario(scenario, cap),
          compiledSha256: '0'.repeat(64),
        }),
      });
      if (mode === 'parity') {
        assert.throws(
          () => runV3Benchmark(control.options),
          /tiny_sat: compiledSha256 \(baseline "[0-9a-f]{64}", candidate "0{64}"\)/,
        );
      } else {
        const result = runV3Benchmark(control.options);
        const disclosures = result.comparisons.flatMap((comparison) => comparison.disclosures);
        assert.equal(disclosures.length, 4);
        assert.ok(disclosures.every((delta) => delta.field === 'compiledSha256'));
        assert.ok(control.writes.has('test/v3-benchmark.json'));
      }
      assert.equal(
        control.runCalls.length,
        control.scenarios.length,
        'compiler-output deltas are not input drift: inputs verify and every scenario runs',
      );
    }
  });

  it('fails parity on a changed counter but only discloses it in gates mode', () => {
    const bump = (measurement: Measurement): Measurement => ({
      ...measurement,
      stats: { ...measurement.stats, decisions: measurement.stats.decisions + 1 },
    });
    const parityControl = harnessControl({
      mode: 'parity',
      run: (scenario, cap) => bump(runScenario(scenario, cap)),
    });
    assert.throws(() => runV3Benchmark(parityControl.options), /tiny_sat: stats\.decisions/);
    assert.equal(parityControl.writes.size, 0, 'failed runs write nothing');
    const gatesControl = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => bump(runScenario(scenario, cap)),
    });
    const result = runV3Benchmark(gatesControl.options);
    const disclosures = result.comparisons.flatMap((comparison) => comparison.disclosures);
    assert.ok(disclosures.some((delta) => delta.field === 'stats.decisions'));
    assert.match(gatesControl.logs.join('\n'), /Gates verified/);
  });

  it('fails parity on a changed model digest but keeps input and cap checks intact', () => {
    const control = harnessControl({
      mode: 'parity',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (measurement.modelDigest !== null) {
          return { ...measurement, modelDigest: 'f'.repeat(64) };
        }
        return measurement;
      },
    });
    assert.throws(() => runV3Benchmark(control.options), /tiny_sat: modelDigest/);
    const gates = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        return measurement.modelDigest === null
          ? measurement
          : { ...measurement, modelDigest: 'f'.repeat(64) };
      },
    });
    const result = runV3Benchmark(gates.options);
    assert.ok(
      result.comparisons
        .flatMap((comparison) => comparison.disclosures)
        .some((delta) => delta.field === 'modelDigest'),
    );
  });

  it('discloses a changed single-shot first model without failing on its derivative set digest', () => {
    const changed = 'f'.repeat(64);
    const control = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (measurement.mode !== 'single' || measurement.modelDigest === null) {
          return measurement;
        }
        return {
          ...measurement,
          modelDigest: changed,
          modelSetDigest: digest([changed]),
          modelDigests: [changed],
          orderedModelPrefixDigest: digest([changed]),
        };
      },
    });
    const result = runV3Benchmark(control.options);
    const fields = new Set(
      result.comparisons.flatMap((comparison) =>
        comparison.disclosures.map((delta) => `${comparison.id}: ${delta.field}`),
      ),
    );
    // The first-model change discloses through every derived lens; the
    // enumeration row's semantic model SET stays hard and is untouched here.
    assert.ok(fields.has('tiny_sat: modelDigest'));
    assert.ok(fields.has('tiny_sat: modelSetDigest'));
    assert.ok(fields.has('tiny_sat: modelDigests[0]'));
    assert.ok(result.comparisons.every((comparison) => comparison.failures.length === 0));
    assert.match(control.logs.join('\n'), /Gates verified/);
  });

  it('keeps per-call verdicts, enumeration model sets, and completed-baseline outcomes hard in gates mode', () => {
    const verdictFlip = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (measurement.calls.length < 2) return measurement;
        const calls = measurement.calls.map((call) => ({ ...call }));
        const second = calls[1];
        assert.ok(second !== undefined);
        second.status = second.status === 'sat' ? 'unsat' : 'sat';
        return { ...measurement, calls };
      },
    });
    assert.throws(() => runV3Benchmark(verdictFlip.options), /calls\[1\]\.status/);

    const setChange = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (measurement.mode !== 'enumeration') return measurement;
        return { ...measurement, modelSetDigest: '0'.repeat(64) };
      },
    });
    assert.throws(() => runV3Benchmark(setChange.options), /modelSetDigest/);

    const exhaust = harnessControl({
      mode: 'gates',
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        return {
          ...measurement,
          status: 'exhausted' as const,
          stats: { ...measurement.stats, conflicts: cap },
        };
      },
    });
    assert.throws(
      () => runV3Benchmark(exhaust.options),
      /tiny_sat: status \(baseline "sat", candidate "exhausted"\)/,
    );
  });
});

describe('v3 exhausted baseline rows', () => {
  it('accepts same-cap exhaustion with an identical completed prefix', () => {
    const control = harnessControl({
      mutateRows: (rows) => {
        const row = rows[2];
        assert.ok(row !== undefined);
        exhaustIncrementalRow(row);
      },
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (scenario.mode !== 'incremental') return measurement;
        const [first, second] = measurement.calls;
        assert.ok(first !== undefined && second !== undefined);
        return {
          ...measurement,
          status: 'exhausted' as const,
          calls: [
            first,
            {
              index: second.index,
              status: 'exhausted' as const,
              modelDigest: null,
              stats: { ...second.stats },
            },
          ],
          completedCalls: 1,
          unexecutedCalls: scenario.calls.length - 2,
          orderedCallDigest: digest(
            [first, second].map(({ index }) => ({
              index,
              status: index === 0 ? first.status : 'exhausted',
              modelDigest: index === 0 ? first.modelDigest : null,
            })),
          ),
          stats: { ...measurement.stats, conflicts: cap },
        };
      },
    });
    const result = runV3Benchmark(control.options);
    assert.equal(result.comparisons.length, 4);
    assert.ok(result.comparisons.every((comparison) => comparison.failures.length === 0));
    assert.ok(
      result.comparisons.every((comparison) => comparison.disclosures.length === 0),
      'identical exhaustion extent is parity, not a disclosure',
    );
  });

  it('discloses completion of an exhausted baseline as an improvement in both modes', () => {
    for (const mode of ['parity', 'gates'] as const) {
      const control = harnessControl({
        mode,
        mutateRows: (rows) => {
          const row = rows[2];
          assert.ok(row !== undefined);
          exhaustIncrementalRow(row);
        },
      });
      const result = runV3Benchmark(control.options);
      const comparison = result.comparisons[2];
      assert.ok(comparison !== undefined);
      assert.equal(comparison.baselineStatus, 'exhausted');
      assert.equal(comparison.candidateStatus, 'complete');
      assert.deepEqual(
        comparison.disclosures.map((delta) => delta.field),
        ['status (baseline exhausted at its cap)'],
      );
      assert.equal(comparison.failures.length, 0);
      assert.ok(
        comparison.prefixEqual,
        'the baseline completed prefix still matches the candidate prefix',
      );
    }
  });

  it('rejects a candidate that stalls before the baseline completed prefix', () => {
    const control = harnessControl({
      mode: 'gates',
      mutateRows: (rows) => {
        const row = rows[2];
        assert.ok(row !== undefined);
        exhaustIncrementalRow(row);
      },
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (scenario.mode !== 'incremental') return measurement;
        return {
          ...measurement,
          status: 'exhausted' as const,
          calls: [],
          completedCalls: 0,
          unexecutedCalls: scenario.calls.length,
          stats: { ...measurement.stats, conflicts: cap },
        };
      },
    });
    assert.throws(
      () => runV3Benchmark(control.options),
      /tiny_incremental: exhausted-prefix coverage/,
    );
  });

  it('rejects a changed completed-prefix verdict even when both sides exhaust', () => {
    const control = harnessControl({
      mode: 'gates',
      mutateRows: (rows) => {
        const row = rows[2];
        assert.ok(row !== undefined);
        exhaustIncrementalRow(row);
      },
      run: (scenario, cap) => {
        const measurement = runScenario(scenario, cap);
        if (scenario.mode !== 'incremental') return measurement;
        const [first, second] = measurement.calls;
        assert.ok(first !== undefined && second !== undefined);
        return {
          ...measurement,
          status: 'exhausted' as const,
          calls: [
            { ...first, status: first.status === 'sat' ? ('unsat' as const) : ('sat' as const) },
            {
              index: second.index,
              status: 'exhausted' as const,
              modelDigest: null,
              stats: { ...second.stats },
            },
          ],
          completedCalls: 1,
          unexecutedCalls: scenario.calls.length - 2,
          stats: { ...measurement.stats, conflicts: cap },
        };
      },
    });
    assert.throws(() => runV3Benchmark(control.options), /calls\[0\]\.status/);
  });
});

describe('v3 comparison projections', () => {
  it('keeps the parity projection free of provenance and identical across differing provenance', () => {
    const control = harnessControl();
    const first = runV3Benchmark(control.options);
    const second = runV3Benchmark({
      ...control.options,
      environment: () => ({
        node: 'v9.9.9-other',
        versions: { node: '9.9.9' },
        platform: 'other',
        arch: 'other',
        nodeEnv: 'production',
        nodeOptions: null,
        execArgv: ['--other'],
        audits: false,
      }),
      snapshotSources: () => ({ 'candidate.ts': '0'.repeat(64) }),
    });
    // Cross-implementation parity holds; the behavioral comparison is clean
    // even though the two runs' provenance differs truthfully.
    assert.ok(second.comparisons.every((comparison) => comparison.failures.length === 0));
    assert.notEqual(json(second.replay), json(first.replay), 'replay projections keep provenance');
    const firstArtifact = JSON.parse(json(first.artifact)) as {
      replay: { implementation: { environment: { node: string } } };
    };
    const secondArtifact = JSON.parse(json(second.artifact)) as {
      replay: { implementation: { environment: { node: string } } };
    };
    assert.equal(firstArtifact.replay.implementation.environment.node, 'v0.0.0-synthetic');
    assert.equal(secondArtifact.replay.implementation.environment.node, 'v9.9.9-other');

    // The parity projection contains exactly the shared behavioral fields.
    const row = control.rows[0];
    const scenario = control.scenarios[0];
    assert.ok(row !== undefined && scenario !== undefined);
    const projection = baselineParityProjection(row);
    assert.deepEqual(Object.keys(projection).sort(), [
      'assumptions',
      'callHistory',
      'cap',
      'compiledSha256',
      'id',
      'inputSha256',
      'measurement',
      'mode',
    ]);
    const measurement = runScenario(scenario, row.finalCap);
    assert.deepEqual(candidateParityProjection(scenario, measurement), projection);
  });

  it('detects candidate source drift during the run', () => {
    let calls = 0;
    const control = harnessControl({
      snapshotSources: () => ({ 'candidate.ts': calls++ === 0 ? 'a'.repeat(64) : 'b'.repeat(64) }),
    });
    assert.throws(
      () => runV3Benchmark(control.options),
      /candidate implementation changed during the run/,
    );
    assert.equal(control.writes.size, 0);
  });

  it('selects the recorded baseline environment by audit state', () => {
    const auditsOff = harnessControl();
    const offResult = runV3Benchmark(auditsOff.options);
    assert.deepEqual(offResult.replay.references.baselineEnvironment, {
      nodeEnv: 'production',
      audits: false,
    });
    const auditsOn = harnessControl({
      environment: () => ({
        node: 'v0.0.0-synthetic',
        versions: { node: '0.0.0' },
        platform: 'synthetic',
        arch: 'synthetic',
        nodeEnv: null,
        nodeOptions: null,
        execArgv: [],
        audits: true,
      }),
    });
    const onResult = runV3Benchmark(auditsOn.options);
    assert.deepEqual(onResult.replay.references.baselineEnvironment, {
      nodeEnv: null,
      audits: true,
    });
    // Rows are proven identical across environments, so both selections pass
    // with zero failures; the choice is truthful labeling, never evidence pick.
    assert.ok(onResult.comparisons.every((comparison) => comparison.failures.length === 0));
  });

  it('replays byte-identically for the same implementation and environment', () => {
    const control = harnessControl();
    const first = runV3Benchmark(control.options);
    const second = runV3Benchmark(control.options);
    assert.equal(json(second.replay), json(first.replay));
    assert.equal(json(second.artifact), json(first.artifact));
    assert.equal(
      control.writes.get('test/v3-benchmark.json'),
      json(first.artifact),
      'the written artifact is the canonical serialization',
    );
  });

  it('byte-compares the replay projection of a real full-corpus run against itself', () => {
    // One real fast scenario through the real harness path, twice: identical
    // implementation and environment must produce byte-identical projections.
    const scenario = corpus().find(({ id }) => id === 'xor8');
    assert.ok(scenario !== undefined);
    const row = recordRow(scenario);
    const baselineText = syntheticBaselineText([row]);
    const legacyText = syntheticLegacyText();
    const options: V3HarnessOptions = {
      readGit: servingGit({
        [`${V3_ARTIFACT_COMMIT}:test/v3-baseline.json`]: baselineText,
        [`${V3_ARTIFACT_COMMIT}:test/legacy-compiled-cnf.json`]: legacyText,
      }),
      identities: {
        baseline: identityFor(baselineText, 'test/v3-baseline.json'),
        legacyCompiledCnf: identityFor(legacyText, 'test/legacy-compiled-cnf.json'),
      },
      corpus: () => [scenario],
      expectedRows: 1,
      now: () => 0,
      log: () => {},
    };
    const first = runV3Benchmark(options);
    const second = runV3Benchmark(options);
    assert.equal(json(second.replay), json(first.replay));
  });
});

describe('v3 evidence helpers', () => {
  const cnf = (overrides: Partial<CompiledCnf>): CompiledCnf => ({
    numVars: 0,
    numNamedVars: 0,
    clauses: [],
    nameToIndex: new Map(),
    indexToName: [],
    levelZeroUnsat: false,
    ...overrides,
  });

  it('distinguishes a lost named universe with identical clauses (no clause-only hashing)', () => {
    const withUniverse = compiledSnapshot(
      cnf({
        numVars: 1,
        numNamedVars: 1,
        nameToIndex: new Map([['a', 0]]),
        indexToName: ['a'],
      }),
    );
    const withoutUniverse = compiledSnapshot(cnf({}));
    assert.deepEqual(withUniverse.clauses, withoutUniverse.clauses);
    assert.notEqual(digest(withUniverse), digest(withoutUniverse));
    // levelZeroUnsat and numVars are part of the snapshot too.
    assert.notEqual(
      digest(compiledSnapshot(cnf({ levelZeroUnsat: true }))),
      digest(withoutUniverse),
    );
    assert.notEqual(
      digest(compiledSnapshot(cnf({ numVars: 1, clauses: [] }))),
      digest(withoutUniverse),
    );
  });

  it('canonicalizes clause and literal order in compiled snapshots', () => {
    const clause = (lits: number[]) => ({ lits, learned: false, activity: 0, lbd: 0 });
    const a = compiledSnapshot(cnf({ clauses: [clause([2, 0]), clause([5])] }));
    const b = compiledSnapshot(cnf({ clauses: [clause([5]), clause([0, 2])] }));
    assert.equal(digest(a), digest(b));
    assert.deepEqual(a.clauses, [[0, 2], [5]]);
  });

  it('validates models independently before hashing them', () => {
    const expr = pairs(1);
    const valid: VariableAssignments = { a1: Value.TRUE, b1: Value.FALSE };
    const digestA = modelEvidence(expr, {}, valid);
    assert.equal(digestA, modelEvidence(expr, {}, valid));
    assert.throws(() => modelEvidence(expr, {}, { a1: Value.TRUE }), /deep-equal/);
    assert.throws(
      () => modelEvidence(expr, {}, { a1: Value.FALSE, b1: Value.FALSE }),
      /model must satisfy independent AST evaluator/,
    );
    assert.throws(() => modelEvidence(expr, { a1: Value.FALSE }, valid), /1.*0|expected/i);
  });

  it('keeps input identity and compiled output as separate domains', () => {
    const scenario = tinyCorpus()[0];
    assert.ok(scenario !== undefined);
    const inputDigest = digest(inputIdentity(scenario));
    const outputDigest = digest(compiledSnapshot(compile(scenario.expr)));
    assert.notEqual(inputDigest, outputDigest);
    const restated: Scenario = { ...scenario, definition: { version: 1, note: 'restated' } };
    assert.notEqual(digest(inputIdentity(restated)), inputDigest);
    assert.equal(digest(compiledSnapshot(compile(restated.expr))), outputDigest);
  });
});

describe('v3 corpus against the sealed baseline (no solving)', () => {
  const baselineRows = REAL_BASELINE.environments[0]?.rows;
  assert.ok(baselineRows !== undefined);

  it('reproduces all 23 sealed scenario identities, ordered assumptions, calls, and caps', () => {
    const scenarios = corpus();
    assert.equal(scenarios.length, 23);
    verifyScenarioInputs(scenarios, baselineRows);
    for (const [index, scenario] of scenarios.entries()) {
      const row = baselineRows[index];
      assert.ok(row !== undefined);
      assert.equal(digest(inputIdentity(scenario)), row.inputSha256, scenario.id);
    }
  });

  it('reproduces the sealed compiled-snapshot hashes on unchanged rows, with disclosed xor drift', () => {
    // The compiler-sharing task intentionally changed aux-heavy compilation:
    // identity-memoized canonization plus structural hash-consing compile the
    // left-deep xor chains with linearly many aux gates instead of
    // exponentially many. The 20 plain-CNF rows (zero aux, no same-kind
    // nesting, no structural gate duplication) must still reproduce the
    // sealed snapshots byte-for-byte; the three xor rows disclose their drift
    // here and in test/v3-benchmark.md, pinned by bounded-shape assertions
    // instead of hashes (never exact aux counts on consed inputs).
    const disclosedDrift = new Map([
      ['xor8', 8],
      ['xor12', 12],
      ['xor16', 16],
    ]);
    for (const scenario of corpus()) {
      const row = baselineRows.find(({ id }) => id === scenario.id);
      assert.ok(row !== undefined);
      const snapshot = compiledSnapshot(compile(scenario.expr));
      const named = disclosedDrift.get(scenario.id);
      if (named === undefined) {
        assert.equal(
          digest(snapshot),
          row.compiledSha256,
          `${scenario.id}: compiled snapshot hash drifted`,
        );
      } else {
        assert.notEqual(
          digest(snapshot),
          row.compiledSha256,
          `${scenario.id}: the disclosed compiler-sharing delta was unexpectedly absent`,
        );
        assert.equal(snapshot.numNamedVars, named);
        assert.equal(snapshot.levelZeroUnsat, false);
        assert.ok(
          snapshot.numVars <= 4 * named,
          `${scenario.id}: aux population stays linear in the chain length (got ${snapshot.numVars})`,
        );
      }
    }
  });

  it('keeps the pinned reference identities consistent with Git', () => {
    assert.equal(
      realGit(['rev-parse', `${V3_BASELINE_REFERENCE.commit}:test/v3-baseline.json`])
        .toString()
        .trim(),
      V3_BASELINE_REFERENCE.gitBlob,
    );
    assert.equal(
      realGit([
        'rev-parse',
        `${LEGACY_COMPILED_CNF_REFERENCE.commit}:test/legacy-compiled-cnf.json`,
      ])
        .toString()
        .trim(),
      LEGACY_COMPILED_CNF_REFERENCE.gitBlob,
    );
    assert.equal(
      realGit(['rev-parse', '--verify', `${V3_BASELINE_COMMIT}^{commit}`])
        .toString()
        .trim(),
      V3_BASELINE_COMMIT,
    );
    assert.equal(
      realGit(['rev-parse', '--verify', `${V3_RECORDER_SEAL_COMMIT}^{commit}`])
        .toString()
        .trim(),
      V3_RECORDER_SEAL_COMMIT,
    );
  });
});
