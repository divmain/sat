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
  currentPhase = 'Phase2',
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
}

export interface BenchmarkResult extends BenchmarkFixture {
  verdict: 'SAT' | 'UNSAT';
  phase3: SolverStats;
}

export const sha256 = (content: string | Buffer): string =>
  createHash('sha256').update(content).digest('hex');

// Git is the only reference reader. No fallback to HEAD, working files, or new measurements.
export function loadReferences(readGit: (args: string[]) => Buffer): BenchmarkReferences {
  const contents = [PHASE1_REFERENCE, PHASE2_REFERENCE].map((reference, index) => {
    const phase = `Phase-${index + 1}`;
    assert.equal(
      readGit(['rev-parse', '--verify', `${reference.commit}^{commit}`])
        .toString('utf8')
        .trim(),
      reference.commit,
      `${phase} reference commit mismatch`,
    );
    const content = readGit(['show', `${reference.commit}:${reference.path}`]);
    const blob = createHash('sha1')
      .update(`blob ${content.length}\0`)
      .update(content)
      .digest('hex');
    assert.equal(blob, reference.gitBlob, `${phase} reference blob mismatch`);
    assert.equal(sha256(content), reference.sha256, `${phase} reference SHA-256 mismatch`);
    return content.toString('utf8');
  });
  // The authenticated bytes fix these historical schemas, including absent counters.
  const phase1 = JSON.parse(contents[0]) as BenchmarkReferences['phase1'];
  const phase2 = JSON.parse(contents[1]) as BenchmarkReferences['phase2'];
  assert.deepEqual(phase2.reference, PHASE1_REFERENCE, 'Phase-2 reference provenance disagreement');
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
  for (const [path, hash] of Object.entries(phase2.implementation.sourceSha256)) {
    assert.equal(
      sha256(readGit(['show', `${PHASE2_REFERENCE.commit}:${path}`])),
      hash,
      `Phase-2 source provenance mismatch: ${path}`,
    );
  }
  return { phase1, phase2 };
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

export function assertBenchmarkResult(
  expr: BooleanExpr,
  fixture: BenchmarkFixture,
  model: VariableAssignments | null,
  stats: SolverStats,
  expectedVerdict: 'SAT' | 'UNSAT',
): void {
  for (const counter of COUNTERS) {
    assert.ok(
      Object.hasOwn(stats, counter) && Number.isSafeInteger(stats[counter]) && stats[counter] >= 0,
      `${fixture.name}: missing or invalid ${counter}`,
    );
  }
  if (stats.conflicts >= fixture.maxConflicts) {
    throw new Error(`${fixture.name}: maximum conflict budget exhausted (${fixture.maxConflicts})`);
  }
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
    `${fixture.name}: verdict disagreement with pinned Phase-2 evidence`,
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

export function createPhase3Report(
  references: BenchmarkReferences,
  implementation: Implementation,
  results: BenchmarkResult[],
) {
  verifyFixtures(
    results.map(({ verdict: _verdict, phase3: _phase3, ...fixture }) => fixture),
    references,
  );
  const entries = results.map(({ phase3, ...result }) => {
    const previous = references.phase2.entries.find(({ name }) => name === result.name);
    assert.ok(previous);
    assert.equal(result.verdict, previous.verdict, `${result.name}: verdict disagreement`);
    for (const counter of COUNTERS) {
      assert.ok(
        Object.hasOwn(phase3, counter) &&
          Number.isSafeInteger(phase3[counter]) &&
          phase3[counter] >= 0,
        `${result.name}: missing or invalid ${counter}`,
      );
    }
    return {
      ...result,
      phase1: references.phase1[result.name] ?? null,
      phase2: previous.phase2,
      phase3,
    };
  });
  const phases = [
    ['phase1', 'Phase1'],
    ['phase2', 'Phase2'],
  ] as const;
  const regressions = entries.flatMap((entry) =>
    phases.flatMap(([key, phase]) =>
      (['decisions', 'propagations', 'conflicts'] as const).flatMap((counter) => {
        const before = entry[key]?.[counter];
        const after = entry.phase3[counter];
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
    'Manual counter comparison only, not a speedup gate or task-completion claim. This single-shot suite does not measure persistent enumeration.',
    'Higher decisions, propagations, or conflicts are explicitly listed as count regressions against each reference. No blanket performance gain, Phase-1 infeasibility, or orders-of-magnitude improvement is claimed.',
    'Phase 1 contains six completed rows, no budget-exhausted rows, and no PHP(7,6)/PHP(8,7) measurements. Phase 1 did not record learnedClausesCurrent, fixture hashes, or verdicts. Missing measurements remain missing, not zero, timeouts, or infinite improvements.',
    'Fixture verification requires exact agreement with the authenticated Phase-2 AST/constant-assumption fingerprints, generator labels, assumptions, coverage, and conflict caps. The original Phase-1 runner and generator configuration was checked in Git history; no new Phase-1 measurements are invented.',
    'The original six rows retain maxConflicts=200000. Random 3-SAT retains 20 variables, 85 clauses, and seeds 42/43/44. PHP(7,6)/PHP(8,7) retain caps 7230/36270, exactly 10x the historical calibrations 723/3627; caps are not recalibrated.',
    'Every run uses fresh compilation, the default brancher, and enablePle=true. Every SAT model passes independent assertModelShape/expressionValue and strict own numeric constant-assumption checks. Verdicts must agree with Phase 2; PHP UNSAT also follows from the pigeonhole principle. Budget exhaustion throws, never becomes UNSAT evidence.',
    'Hypergraph must retain exactly 2 decisions, 16 propagations, and 0 conflicts. The PHP rows must engage learning. Passing fixed budgets proves only those budgets.',
    'Ratios are reference/Phase3, rounded to two decimals, not wall-time speedups. A zero denominator is n/a, with 0/0 labelled parity. Learning and restart counters report activity, not speedup; more or fewer of these counters alone is not a performance verdict.',
    'Both references are authenticated by full commit, Git blob, and SHA-256. Phase-2 provenance is preserved verbatim, including its recorded HEAD and working-byte hashes; those hashes are also checked against files at its committed reference.',
    'Current HEAD is context only. sourceSha256 fingerprints actual working bytes before implementation imports; hashes and file versions are checked again before recording. File versions are not stored. fixtureSha256 hashes UTF-8 JSON.stringify({ expr, assumptions }) before compilation and is checked again after solving.',
    'Working-tree baseline.json and Phase-2 JSON/Markdown/review files are never reference inputs or output targets. Only phase3-benchmark.json and phase3-benchmark.md are written. No models, timestamps, or wall times are stored; timing is console-only.',
  ];
  const report = {
    references: {
      phase1: PHASE1_REFERENCE,
      phase2: {
        ...PHASE2_REFERENCE,
        provenance: {
          reference: references.phase2.reference,
          implementation: references.phase2.implementation,
        },
      },
    },
    implementation,
    notes,
    regressions,
    entries,
  };
  const markdown = [
    '# Phase-3 Benchmark Comparison',
    '',
    'Generated by `npm run bench`. No models, timestamps, or wall times are stored.',
    '',
    '## Provenance',
    '',
    ...[PHASE1_REFERENCE, PHASE2_REFERENCE].flatMap((reference, index) => [
      `- Phase-${index + 1} reference: \`${reference.commit}:${reference.path}\``,
      `- Verified Git blob: \`${reference.gitBlob}\`; SHA-256: \`${reference.sha256}\``,
    ]),
    `- Phase-2 recorded HEAD (preserved, not its artifact commit): \`${references.phase2.implementation.head}\``,
    `- Phase-2 Node: \`${references.phase2.implementation.node}\`; NODE_ENV: \`${
      references.phase2.implementation.nodeEnv ?? '(unset)'
    }\``,
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
        ...COUNTERS.map((counter) => entry.phase3[counter]),
        entry.maxConflicts,
      ]),
    ),
    '',
    '## Count Regressions',
    '',
    regressions.length === 0
      ? 'No higher decision/propagation/conflict counts on comparable rows. Missing data remains incomparable.'
      : table(
          ['instance', 'reference', 'counter', 'before', 'Phase3', 'delta', 'assessment'],
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
      `## Phase3 Vs ${phase}`,
      '',
      table(
        [
          'instance',
          'counter',
          phase,
          'Phase3',
          `delta (Phase3 - ${phase})`,
          `ratio (${phase} / Phase3)`,
          'count change',
        ],
        entries.flatMap((entry) =>
          COUNTERS.map((counter) => [
            entry.name,
            counter,
            ...comparisonCells(entry[key]?.[counter], entry.phase3[counter], 'Phase3'),
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
    '',
    '## Preserved Phase-2 Source Fingerprints',
    '',
    table(
      ['file', 'SHA-256 (historically recorded bytes)'],
      Object.entries(references.phase2.implementation.sourceSha256),
    ),
    '',
  ].join('\n');
  return { report, markdown };
}
