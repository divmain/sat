import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import type { SolverStats } from '../src/solver.js';
import {
  assertModelShape,
  cnfToExpr,
  expressionValue,
  hypergraphFormula,
  mulberry32,
  phpCnf,
  random3Cnf,
} from './helpers.js';
import { PHP_REGRESSIONS } from './php-regressions.js';

export const COUNTERS = [
  'decisions',
  'propagations',
  'conflicts',
  'restarts',
  'learnedClauses',
  'learnedClausesCurrent',
] as const satisfies readonly (keyof SolverStats)[];

// Cells: reference, current, current - reference, reference / current, count change.
// "Higher" is not automatically worse for learning/restart counters.
export function comparisonCells(
  reference: number | undefined,
  current: number | undefined,
  currentPhase = 'Phase4',
): string[] {
  for (const value of [reference, current]) {
    if (value !== undefined) {
      assert.ok(
        Number.isSafeInteger(value) && value >= 0,
        'counter must be a non-negative integer',
      );
    }
  }
  if (reference === undefined || current === undefined) {
    return [
      reference === undefined ? 'not recorded' : String(reference),
      current === undefined ? 'not recorded' : String(current),
      'n/a',
      'n/a',
      'not comparable',
    ];
  }
  const delta = current - reference;
  const ratio =
    current === 0
      ? reference === 0
        ? 'n/a (0/0 parity)'
        : `n/a (${currentPhase} is zero)`
      : `${(reference / current).toFixed(2)}x`;
  return [
    String(reference),
    String(current),
    `${delta > 0 ? '+' : ''}${delta}`,
    ratio,
    delta === 0 ? 'parity' : delta > 0 ? 'higher' : 'lower',
  ];
}

interface ReferenceIdentity {
  commit: string;
  path: string;
  gitBlob: string;
  sha256: string;
}

export const PHASE1_REFERENCE: ReferenceIdentity = {
  commit: '7037f823d192dc3cf2dc9119c8063781e143113c',
  path: 'test/baseline.json',
  gitBlob: '489af8c72ed9c37befa806ccef03404d0a818e61',
  sha256: '826b4ce3b30a160ab54be48fefd4ca63affc7707786609bd481aabda6536b8ac',
};

export const PHASE2_REFERENCE: ReferenceIdentity = {
  commit: 'ade64e558ee47c60ae7b4b2cc29f861ccfb245cf',
  path: 'test/phase2-benchmark.json',
  gitBlob: 'e838c35c6d99fde7c73627254ecec18255958c58',
  sha256: '830c4bcc5281b2534032de5fa01b5da17f971c1c877999326b18452da5aa7cd4',
};

export const PHASE3_REFERENCE: ReferenceIdentity = {
  commit: '53a059c761e9b3591b8513a03309699ecef0c889',
  path: 'test/phase3-benchmark.json',
  gitBlob: 'd2eb15f01b60a8e639268a94a8081c30570ec6fa',
  sha256: 'cefb8e62794156441b1154ee7be82a7642446e19bde40ba33d3005a1badd146d',
};

// The v2 release commit froze the Phase-4 evidence. Its recorded HEAD field
// (53a059c…) is context only: source provenance is checked against these
// release-commit bytes, never against the recorded HEAD or working files.
export const PHASE4_REFERENCE: ReferenceIdentity = {
  commit: 'ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2',
  path: 'test/phase4-benchmark.json',
  gitBlob: '3f75b8d819a6b2e0fed45bed662b3bb575ca2868',
  sha256: '4e0bf82088935537737a2e61e011875988a66b703b105c5f6c61c1b5b61ab795',
};

export const PHASE4_MARKDOWN_REFERENCE: ReferenceIdentity = {
  commit: 'ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2',
  path: 'test/phase4-benchmark.md',
  gitBlob: '669dee20a621d3575a3efe0518739cbc5b54d733',
  sha256: '9c42e40e47158d0fb7f47a5a59cbe61b7d02d8ec06f862cf2b5fb3f15a15bc24',
};

export const PHASE4_MANIFEST_REFERENCE: ReferenceIdentity = {
  commit: 'ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2',
  path: 'test/phase4-release-manifest.json',
  gitBlob: '461cab4973b971fcf4543ac62ed5d02bce6a71d2',
  sha256: '98d20f0ca246bbfedc2d069dd783ef52e5ea2022e51946796ab5ffbfe9e235bb',
};

export interface Implementation {
  head: string;
  sourceSha256: Record<string, string>;
  node: string;
  nodeEnv: string | null;
}

export interface BenchmarkFixture {
  name: string;
  fixture: string;
  fixtureSha256: string;
  assumptions: VariableAssignments;
  maxConflicts: number;
  calibratedConflicts: number | null;
}

interface Phase2Entry extends BenchmarkFixture {
  verdict: 'SAT' | 'UNSAT';
  phase1: Partial<SolverStats> | null;
  phase2: Partial<SolverStats>;
}

export interface BenchmarkReferences {
  phase1: Record<string, Partial<SolverStats>>;
  phase2: {
    reference: ReferenceIdentity;
    implementation: Implementation;
    entries: Phase2Entry[];
  };
  phase3: {
    references: {
      phase1: ReferenceIdentity;
      phase2: ReferenceIdentity & {
        provenance: Pick<BenchmarkReferences['phase2'], 'reference' | 'implementation'>;
      };
    };
    implementation: Implementation;
    entries: Array<Phase2Entry & { phase3: Partial<SolverStats> }>;
  };
}

export interface BenchmarkResult extends BenchmarkFixture {
  verdict: 'SAT' | 'UNSAT';
  phase4: SolverStats;
}

export const sha256 = (content: string | Buffer): string =>
  createHash('sha256').update(content).digest('hex');

// Git is the only reference reader. No fallback to HEAD, working files, or new measurements.
function authenticateReference(
  readGit: (args: string[]) => Buffer,
  reference: ReferenceIdentity,
  phase: string,
): string {
  assert.equal(
    readGit(['rev-parse', '--verify', `${reference.commit}^{commit}`])
      .toString('utf8')
      .trim(),
    reference.commit,
    `${phase} reference commit mismatch`,
  );
  const content = readGit(['show', `${reference.commit}:${reference.path}`]);
  const blob = createHash('sha1').update(`blob ${content.length}\0`).update(content).digest('hex');
  assert.equal(blob, reference.gitBlob, `${phase} reference blob mismatch`);
  assert.equal(sha256(content), reference.sha256, `${phase} reference SHA-256 mismatch`);
  return content.toString('utf8');
}

export function loadReferences(readGit: (args: string[]) => Buffer): BenchmarkReferences {
  const contents = [PHASE1_REFERENCE, PHASE2_REFERENCE, PHASE3_REFERENCE].map((reference, index) =>
    authenticateReference(readGit, reference, `Phase-${index + 1}`),
  );
  // The authenticated bytes fix these historical schemas, including absent counters.
  const phase1 = JSON.parse(contents[0]) as BenchmarkReferences['phase1'];
  const phase2 = JSON.parse(contents[1]) as BenchmarkReferences['phase2'];
  const phase3 = JSON.parse(contents[2]) as BenchmarkReferences['phase3'];
  const references = { phase1, phase2, phase3 };
  assertReferenceChain(references);
  for (const [phase, reference, implementation] of [
    ['Phase-2', PHASE2_REFERENCE, phase2.implementation],
    ['Phase-3', PHASE3_REFERENCE, phase3.implementation],
  ] as const) {
    for (const [path, hash] of Object.entries(implementation.sourceSha256)) {
      assert.equal(
        sha256(readGit(['show', `${reference.commit}:${path}`])),
        hash,
        `${phase} source provenance mismatch: ${path}`,
      );
    }
  }
  return references;
}

// Decoded agreement is separate from byte authentication, not a substitute for it.
export function assertReferenceChain({ phase1, phase2, phase3 }: BenchmarkReferences): void {
  assert.deepEqual(phase2.reference, PHASE1_REFERENCE, 'Phase-2 reference provenance disagreement');
  assert.deepEqual(
    phase3.references,
    {
      phase1: PHASE1_REFERENCE,
      phase2: {
        ...PHASE2_REFERENCE,
        provenance: { reference: phase2.reference, implementation: phase2.implementation },
      },
    },
    'Phase-3 reference provenance disagreement',
  );
  const names = phase2.entries.map((entry) => entry.name);
  assert.equal(new Set(names).size, names.length, 'duplicate Phase-2 instance');
  for (const name of Object.keys(phase1)) {
    assert.ok(names.includes(name), `Missing original Phase-1 instance: ${name}`);
  }
  for (const entry of phase2.entries) {
    assert.deepEqual(
      entry.phase1,
      phase1[entry.name] ?? null,
      `Phase-1 counters disagree with Phase-2 evidence: ${entry.name}`,
    );
  }
  assert.deepEqual(
    phase3.entries.map(({ phase3: _phase3, ...entry }) => entry),
    phase2.entries,
    'Phase-3 evidence chain disagreement with Phase 2',
  );
}

export interface Phase4Entry extends BenchmarkResult {
  phase1: Partial<SolverStats> | null;
  phase2: Partial<SolverStats>;
  phase3: Partial<SolverStats>;
}

export interface Phase4Record {
  phase: string;
  scope: string;
  references: BenchmarkReferences['phase3']['references'] & {
    phase3: ReferenceIdentity & {
      provenance: {
        references: BenchmarkReferences['phase3']['references'];
        implementation: Implementation;
      };
    };
  };
  implementation: Implementation;
  notes: string[];
  regressions: Array<{
    instance: string;
    reference: string;
    counter: string;
    before: number;
    after: number;
    delta: number;
  }>;
  entries: Phase4Entry[];
}

export interface Phase4ReleaseManifest {
  benchmark: {
    artifacts: Array<{ path: string; gitBlob: string; sha256: string }>;
  };
}

// The manifest from the same release commit must identify exactly the pinned
// Phase-4 artifact bytes the verifier authenticates independently.
export function assertPhase4Manifest(manifest: Phase4ReleaseManifest): void {
  const artifacts = new Map(
    manifest.benchmark.artifacts.map((artifact) => [artifact.path, artifact]),
  );
  for (const reference of [PHASE4_REFERENCE, PHASE4_MARKDOWN_REFERENCE]) {
    const artifact = artifacts.get(reference.path);
    assert.ok(artifact, `Phase-4 manifest is missing the ${reference.path} artifact record`);
    assert.equal(
      artifact.gitBlob,
      reference.gitBlob,
      `Phase-4 manifest disagrees with the pinned ${reference.path} Git blob`,
    );
    assert.equal(
      artifact.sha256,
      reference.sha256,
      `Phase-4 manifest disagrees with the pinned ${reference.path} SHA-256`,
    );
  }
}

// Decoded agreement between the frozen Phase-4 record and the independently
// authenticated Phase-1/2/3 references, separate from byte authentication.
// The record's own phase4 counters are the parity reference and are only
// validated for shape here.
export function assertPhase4Record(record: Phase4Record, references: BenchmarkReferences): void {
  assert.equal(record.phase, 'Phase4', 'Phase-4 record phase disagreement');
  assert.equal(record.scope, 'single-shot', 'Phase-4 record scope disagreement');
  assert.deepEqual(
    record.references,
    {
      ...references.phase3.references,
      phase3: {
        ...PHASE3_REFERENCE,
        provenance: {
          references: references.phase3.references,
          implementation: references.phase3.implementation,
        },
      },
    },
    'Phase-4 record provenance disagreement with authenticated Phases 1-3',
  );
  assert.equal(
    record.entries.length,
    references.phase3.entries.length,
    'Phase-4 record coverage disagreement',
  );
  for (const entry of record.entries) {
    const previous = references.phase3.entries.find(({ name }) => name === entry.name);
    assert.ok(previous, `Phase-4 record instance missing from Phase-3 evidence: ${entry.name}`);
    for (const counter of COUNTERS) {
      const value = entry.phase4[counter];
      assert.ok(
        Number.isSafeInteger(value) && value >= 0,
        `Phase-4 record counter must be a non-negative integer: ${entry.name}.${counter}`,
      );
    }
    const { phase4: _counters, ...historical } = entry;
    assert.deepEqual(
      historical,
      previous,
      `Phase-4 record disagrees with authenticated Phase-3 evidence: ${entry.name}`,
    );
  }
}

// Every embedded Phase-4 source fingerprint is checked against the release
// commit's bytes, independently of today's edited working sources; the
// record's HEAD field is context only and never used for provenance.
export function assertPhase4Sources(
  record: Phase4Record,
  readGit: (args: string[]) => Buffer,
): void {
  for (const [path, hash] of Object.entries(record.implementation.sourceSha256)) {
    assert.equal(
      sha256(readGit(['show', `${PHASE4_REFERENCE.commit}:${path}`])),
      hash,
      `Phase-4 source provenance mismatch: ${path}`,
    );
  }
}

export function loadPhase4Record(
  readGit: (args: string[]) => Buffer,
  references: BenchmarkReferences,
): Phase4Record {
  const record = JSON.parse(
    authenticateReference(readGit, PHASE4_REFERENCE, 'Phase-4'),
  ) as Phase4Record;
  const manifest = JSON.parse(
    authenticateReference(readGit, PHASE4_MANIFEST_REFERENCE, 'Phase-4 manifest'),
  ) as Phase4ReleaseManifest;
  authenticateReference(readGit, PHASE4_MARKDOWN_REFERENCE, 'Phase-4 markdown');
  assertPhase4Manifest(manifest);
  assertPhase4Record(record, references);
  assertPhase4Sources(record, readGit);
  return record;
}

export function assertSourcesUnchanged(
  before: Record<string, unknown>,
  after: Record<string, unknown>,
): void {
  assert.deepEqual(after, before, 'Benchmark input changed during the run; rerun before recording');
}

export function benchmarkFixtures(): Array<{ expr: BooleanExpr; fixture: BenchmarkFixture }> {
  const instances = [
    {
      name: 'hypergraph',
      fixture: 'hypergraphFormula()',
      build: hypergraphFormula,
      assumptions: { h: Value.TRUE },
      maxConflicts: 200_000,
      calibratedConflicts: null,
    },
    ...[
      { pigeons: 5, holes: 4, maxConflicts: 200_000, calibratedConflicts: null },
      { pigeons: 6, holes: 5, maxConflicts: 200_000, calibratedConflicts: null },
    ].map(({ pigeons, holes, ...budget }) => ({
      name: `php_${pigeons}_${holes}`,
      fixture: `cnfToExpr(phpCnf(${pigeons}, ${holes}))`,
      build: () => cnfToExpr(phpCnf(pigeons, holes)),
      assumptions: {},
      ...budget,
    })),
    ...[42, 43, 44].map((seed) => ({
      name: `sat3_seed${seed}`,
      fixture: `cnfToExpr(random3Cnf(mulberry32(${seed}), 20, 85))`,
      build: () => cnfToExpr(random3Cnf(mulberry32(seed), 20, 85)),
      assumptions: {},
      maxConflicts: 200_000,
      calibratedConflicts: null,
    })),
    ...PHP_REGRESSIONS.map(({ pigeons, holes, ...budget }) => ({
      name: `php_${pigeons}_${holes}`,
      fixture: `cnfToExpr(phpCnf(${pigeons}, ${holes}))`,
      build: () => cnfToExpr(phpCnf(pigeons, holes)),
      assumptions: {},
      ...budget,
    })),
  ];
  return instances.map(({ build, ...fixture }) => {
    const expr = build();
    const fixtureSha256 = sha256(JSON.stringify({ expr, assumptions: fixture.assumptions }));
    return { expr, fixture: { ...fixture, fixtureSha256 } };
  });
}

export function verifyFixtures(
  fixtures: BenchmarkFixture[],
  references: BenchmarkReferences,
): void {
  assertReferenceChain(references);
  assert.deepEqual(
    fixtures.map(({ name }) => name).sort(),
    references.phase2.entries.map(({ name }) => name).sort(),
    'Benchmark fixture coverage disagreement',
  );
  for (const fixture of fixtures) {
    const previous = references.phase2.entries.find(({ name }) => name === fixture.name);
    assert.ok(previous, `Missing pinned Phase-2 instance: ${fixture.name}`);
    const { verdict: _verdict, phase1: _phase1, phase2: _phase2, ...expected } = previous;
    assert.deepEqual(fixture, expected, `Benchmark fixture disagreement: ${fixture.name}`);
  }
}

function assertBenchmarkCounters(fixture: BenchmarkFixture, stats: SolverStats): void {
  for (const counter of COUNTERS) {
    assert.ok(
      Object.hasOwn(stats, counter) && Number.isSafeInteger(stats[counter]) && stats[counter] >= 0,
      `${fixture.name}: missing or invalid ${counter}`,
    );
  }
  if (stats.conflicts >= fixture.maxConflicts) {
    throw new Error(`${fixture.name}: maximum conflict budget exhausted (${fixture.maxConflicts})`);
  }
}

export function assertBenchmarkResult(
  expr: BooleanExpr,
  fixture: BenchmarkFixture,
  model: VariableAssignments | null,
  stats: SolverStats,
  expectedVerdict: 'SAT' | 'UNSAT',
): void {
  assertBenchmarkCounters(fixture, stats);
  if (model !== null) {
    assertModelShape(model, expr);
    assert.equal(expressionValue(expr, model), Value.TRUE, `${fixture.name}: model falsifies AST`);
    for (const [name, value] of Object.entries(fixture.assumptions)) {
      if (value !== Value.UNSET) {
        assert.ok(
          Object.hasOwn(model, name) && model[name] === value,
          `${fixture.name}: model violates constant assumption ${JSON.stringify(name)}`,
        );
      }
    }
  }
  assert.equal(
    model === null ? 'UNSAT' : 'SAT',
    expectedVerdict,
    `${fixture.name}: verdict disagreement with pinned Phase-2/3 evidence`,
  );
  if (fixture.name === 'hypergraph') {
    assert.deepEqual(
      [stats.decisions, stats.propagations, stats.conflicts],
      [2, 16, 0],
      'hypergraph must retain exactly 2 decisions, 16 propagations, 0 conflicts',
    );
  }
  if (fixture.name.startsWith('php_')) {
    assert.equal(model, null, 'PHP benchmark UNSAT follows from the pigeonhole principle');
    assert.ok(stats.learnedClauses > 0, `${fixture.name}: learning must be engaged`);
  }
}

export const table = (headers: string[], rows: (string | number)[][]): string =>
  [
    `| ${headers.join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...rows.map((row) => `| ${row.join(' | ')} |`),
  ].join('\n');

export function createPhase4Report(
  references: BenchmarkReferences,
  implementation: Implementation,
  results: BenchmarkResult[],
) {
  verifyFixtures(
    results.map(({ verdict: _verdict, phase4: _phase4, ...fixture }) => fixture),
    references,
  );
  const entries = results.map(({ phase4, ...result }) => {
    const previous = references.phase3.entries.find(({ name }) => name === result.name);
    assert.ok(previous);
    assert.equal(result.verdict, previous.verdict, `${result.name}: verdict disagreement`);
    assertBenchmarkCounters(result, phase4);
    return {
      ...result,
      phase1: previous.phase1,
      phase2: previous.phase2,
      phase3: previous.phase3,
      // Store only the six counters, in a fixed order, never incidental solver fields.
      phase4: {
        decisions: phase4.decisions,
        propagations: phase4.propagations,
        conflicts: phase4.conflicts,
        restarts: phase4.restarts,
        learnedClauses: phase4.learnedClauses,
        learnedClausesCurrent: phase4.learnedClausesCurrent,
      },
    };
  });
  const phases = [
    ['phase1', 'Phase1'],
    ['phase2', 'Phase2'],
    ['phase3', 'Phase3'],
  ] as const;
  const regressions = entries.flatMap((entry) =>
    phases.flatMap(([key, phase]) =>
      (['decisions', 'propagations', 'conflicts'] as const).flatMap((counter) => {
        const before = entry[key]?.[counter];
        const after = entry.phase4[counter];
        return before !== undefined && after > before
          ? [
              {
                instance: entry.name,
                reference: phase,
                counter,
                before,
                after,
                delta: after - before,
              },
            ]
          : [];
      }),
    ),
  );
  const notes = [
    'Phase-4 release single-shot evidence only: manual counter comparison, not a speedup gate or task-completion claim. This suite does not measure createSolver performance or persistent enumeration.',
    'Higher decisions, propagations, or conflicts are explicitly listed as count regressions against each reference. No blanket performance gain, Phase-1 infeasibility, or orders-of-magnitude improvement is claimed.',
    'Phase 1 contains six completed rows, no budget-exhausted rows, and no PHP(7,6)/PHP(8,7) measurements. Phase 1 did not record learnedClausesCurrent, fixture hashes, or verdicts. Missing measurements remain missing, not zero, timeouts, or infinite improvements.',
    'Fixture verification requires exact agreement with the authenticated Phase-2/3 AST/constant-assumption fingerprints, generator labels, assumptions, coverage, and conflict caps. The original Phase-1 runner and generator configuration was checked in Git history; no new historical measurements are invented.',
    'The original six rows retain maxConflicts=200000. Random 3-SAT retains 20 variables, 85 clauses, and seeds 42/43/44. PHP(7,6)/PHP(8,7) retain caps 7230/36270, exactly 10x the historical calibrations 723/3627; caps are not recalibrated.',
    'Every run uses fresh compilation and an internal Solver, mirroring single-shot getSolution with the default brancher and enablePle=true plus an explicit conflict cap. Every SAT model passes independent assertModelShape/expressionValue and strict own numeric constant-assumption checks. Verdicts must agree with Phases 2 and 3; PHP UNSAT also follows from the pigeonhole principle. Budget exhaustion throws, never becomes UNSAT evidence.',
    'Hypergraph must retain exactly 2 decisions, 16 propagations, and 0 conflicts. The PHP rows must engage learning. Passing fixed budgets proves only those budgets.',
    'Ratios are reference/Phase4, rounded to two decimals, not wall-time speedups. A zero denominator is n/a, with 0/0 labelled parity. Learning and restart counters report activity, not speedup; more or fewer of these counters alone is not a performance verdict.',
    'learnedClausesCurrent is the final live learned-clause count, not peak or total memory. The default reduction threshold is not lowered for this suite; these six counters do not count reduction events or establish default-reduction engagement. Phase-3 single-shot rows never reached its 10000-admission default threshold. Protected clauses and permanent enumeration blockers preclude any implied total-memory bound; enumeration is outside this suite.',
    'All three references are independently authenticated by full artifact commit, Git blob, and SHA-256. Phase-3 embedded Phase-1/2 provenance is preserved verbatim and checked against the independently authenticated prior artifacts, including counters, fixtures, and verdicts. Phase-2/3 implementation hashes are checked against their ARTIFACT commits, not their recorded HEADs (context only).',
    'Current HEAD is context only. sourceSha256 fingerprints actual working bytes before implementation imports; hashes and file versions are checked again before recording. File versions are not stored. fixtureSha256 hashes UTF-8 JSON.stringify({ expr, assumptions }) before compilation and is checked again after solving.',
    'Working-tree baseline.json and frozen Phase-2/3 JSON/Markdown/review files are never reference inputs or output targets. Only phase4-benchmark.json and phase4-benchmark.md are written. No models, timestamps, or wall times are stored; timing is console-only.',
  ];
  const report = {
    phase: 'Phase4',
    scope: 'single-shot',
    references: {
      ...references.phase3.references,
      phase3: {
        ...PHASE3_REFERENCE,
        provenance: {
          references: references.phase3.references,
          implementation: references.phase3.implementation,
        },
      },
    },
    implementation,
    notes,
    regressions,
    entries,
  };
  const previousImplementations = [
    ['Phase-2', references.phase2.implementation],
    ['Phase-3', references.phase3.implementation],
  ] as const;
  const markdown = [
    '# Phase-4 Release Single-Shot Benchmark Comparison',
    '',
    'Generated by `npm run bench`. No models, timestamps, or wall times are stored.',
    '',
    '## Provenance',
    '',
    ...[PHASE1_REFERENCE, PHASE2_REFERENCE, PHASE3_REFERENCE].flatMap((reference, index) => [
      `- Phase-${index + 1} reference: \`${reference.commit}:${reference.path}\``,
      `- Verified Git blob: \`${reference.gitBlob}\`; SHA-256: \`${reference.sha256}\``,
    ]),
    ...previousImplementations.flatMap(([phase, previous]) => [
      `- ${phase} recorded HEAD (preserved, not its artifact commit): \`${previous.head}\``,
      `- ${phase} Node: \`${previous.node}\`; NODE_ENV: \`${previous.nodeEnv ?? '(unset)'}\``,
    ]),
    `- Current HEAD (context, not implementation identity): \`${implementation.head}\``,
    `- Current Node: \`${implementation.node}\`; NODE_ENV: \`${
      implementation.nodeEnv ?? '(unset)'
    }\``,
    '',
    '## Interpretation And Limits',
    '',
    ...notes.map((note) => `- ${note}`),
    '',
    '## Current Counters',
    '',
    table(
      ['instance', 'verdict', ...COUNTERS, 'maxConflicts'],
      entries.map((entry) => [
        entry.name,
        entry.verdict,
        ...COUNTERS.map((counter) => entry.phase4[counter]),
        entry.maxConflicts,
      ]),
    ),
    '',
    '## Count Regressions',
    '',
    regressions.length === 0
      ? 'No higher decision/propagation/conflict counts on comparable rows. Missing data remains incomparable.'
      : table(
          ['instance', 'reference', 'counter', 'before', 'Phase4', 'delta', 'assessment'],
          regressions.map(({ instance, reference, counter, before, after, delta }) => [
            instance,
            reference,
            counter,
            before,
            after,
            `+${delta}`,
            'REGRESSION (higher count)',
          ]),
        ),
    ...phases.flatMap(([key, phase]) => [
      '',
      `## Phase4 Vs ${phase}`,
      '',
      table(
        [
          'instance',
          'counter',
          phase,
          'Phase4',
          `delta (Phase4 - ${phase})`,
          `ratio (${phase} / Phase4)`,
          'count change',
        ],
        entries.flatMap((entry) =>
          COUNTERS.map((counter) => [
            entry.name,
            counter,
            ...comparisonCells(entry[key]?.[counter], entry.phase4[counter], 'Phase4'),
          ]),
        ),
      ),
    ]),
    '',
    '## Verified Fixture Fingerprints',
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
    '## Current Source Fingerprints',
    '',
    table(['file', 'SHA-256 (raw working bytes)'], Object.entries(implementation.sourceSha256)),
    ...previousImplementations.flatMap(([phase, previous]) => [
      '',
      `## Preserved ${phase} Source Fingerprints`,
      '',
      table(
        ['file', 'SHA-256 (historically recorded bytes)'],
        Object.entries(previous.sourceSha256),
      ),
    ]),
    '',
  ].join('\n');
  return { report, markdown };
}
