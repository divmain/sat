import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { describe, it } from 'node:test';
import { compile } from '../src/compile.js';
import { and, not, or, Value } from '../src/expr.js';
import type { VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import {
  assertBenchmarkResult,
  assertSourcesUnchanged,
  benchmarkFixtures,
  comparisonCells,
  COUNTERS,
  createPhase3Report,
  loadReferences,
  PHASE1_REFERENCE,
  PHASE2_REFERENCE,
  sha256,
  verifyFixtures,
} from './bench-comparison.js';
import type { BenchmarkFixture, BenchmarkResult } from './bench-comparison.js';
import { cnfToExpr, phpCnf } from './helpers.js';

describe('benchmark comparison cells', () => {
  it('labels a reduction with the original/current ratio and signed delta', () => {
    assert.deepEqual(comparisonCells(51, 38), ['51', '38', '-13', '1.34x', 'lower']);
  });

  it('retains regressions rather than inverting the ratio to look like a gain', () => {
    assert.deepEqual(comparisonCells(6, 9), ['6', '9', '+3', '0.67x', 'higher']);
  });

  it('distinguishes positive parity from an undefined zero/zero ratio', () => {
    assert.deepEqual(comparisonCells(2, 2), ['2', '2', '0', '1.00x', 'parity']);
    assert.deepEqual(comparisonCells(0, 0), ['0', '0', '0', 'n/a (0/0 parity)', 'parity']);
  });

  it('does not turn missing Phase-1 data into zero, a timeout, or an infinite gain', () => {
    assert.deepEqual(comparisonCells(undefined, 723), [
      'not recorded',
      '723',
      'n/a',
      'n/a',
      'not comparable',
    ]);
    assert.deepEqual(comparisonCells(undefined, 0), [
      'not recorded',
      '0',
      'n/a',
      'n/a',
      'not comparable',
    ]);
  });

  it('keeps learning from zero as a higher count, not a speedup', () => {
    assert.deepEqual(comparisonCells(0, 27), ['0', '27', '+27', '0.00x', 'higher']);
  });

  it('handles a zero current count without emitting a non-finite ratio', () => {
    assert.deepEqual(comparisonCells(5, 0), ['5', '0', '-5', 'n/a (Phase2 is zero)', 'lower']);
  });

  it('labels Phase3 zero denominators and missing values on either side', () => {
    assert.deepEqual(comparisonCells(5, 0, 'Phase3'), [
      '5',
      '0',
      '-5',
      'n/a (Phase3 is zero)',
      'lower',
    ]);
    assert.deepEqual(comparisonCells(0, undefined, 'Phase3'), [
      '0',
      'not recorded',
      'n/a',
      'n/a',
      'not comparable',
    ]);
    assert.deepEqual(comparisonCells(undefined, undefined, 'Phase3'), [
      'not recorded',
      'not recorded',
      'n/a',
      'n/a',
      'not comparable',
    ]);
  });

  it('rejects negative, non-finite, fractional, unsafe, or coerced counters', () => {
    for (const value of [-1, Number.NaN, Number.POSITIVE_INFINITY, 0.5, 2 ** 53, true, '2', null]) {
      assert.throws(() => comparisonCells(value as number, 1), /non-negative integer/);
      assert.throws(() => comparisonCells(1, value as number), /non-negative integer/);
    }
  });
});

const readGit = (args: string[]): Buffer =>
  execFileSync('git', args, { cwd: new URL('../', import.meta.url) });
const references = loadReferences(readGit);
const fixtures = benchmarkFixtures();

describe('benchmark reference and fixture authentication', () => {
  it('uses full immutable Git references and preserves historical working-byte provenance', () => {
    const calls: string[][] = [];
    assert.deepEqual(
      loadReferences((args) => {
        calls.push(args);
        return readGit(args);
      }),
      references,
    );
    for (const reference of [PHASE1_REFERENCE, PHASE2_REFERENCE]) {
      assert.ok(
        calls.some((args) => args.join(' ') === `show ${reference.commit}:${reference.path}`),
      );
      assert.equal(reference.commit.length, 40);
      assert.equal(reference.gitBlob.length, 40);
      assert.equal(reference.sha256.length, 64);
    }
    assert.deepEqual(references.phase2.reference, PHASE1_REFERENCE);
    assert.equal(references.phase2.implementation.head, PHASE1_REFERENCE.commit);
    assert.equal(
      references.phase2.implementation.sourceSha256['src/solver.ts'],
      'cee5031d304b5dacd9d8ed0a4de0b8908c4bd1ae5edd5f528aca79c0c85a12a1',
    );
  });

  it('propagates unavailable history rather than selecting another reference', () => {
    const missing = new Error('missing pinned Git history');
    assert.throws(
      () =>
        loadReferences(() => {
          throw missing;
        }),
      (error) => error === missing,
    );
  });

  for (const [index, reference] of [PHASE1_REFERENCE, PHASE2_REFERENCE].entries()) {
    it(`rejects a wrong Phase-${index + 1} commit identity`, () => {
      assert.throws(
        () =>
          loadReferences((args) =>
            args[0] === 'rev-parse' && args[2] === `${reference.commit}^{commit}`
              ? Buffer.from('0'.repeat(40))
              : readGit(args),
          ),
        new RegExp(`Phase-${index + 1} reference commit mismatch`),
      );
    });

    it(`rejects modified Phase-${index + 1} reference bytes before parsing them`, () => {
      assert.throws(
        () =>
          loadReferences((args) =>
            args[0] === 'show' && args[1] === `${reference.commit}:${reference.path}`
              ? Buffer.from('{}')
              : readGit(args),
          ),
        new RegExp(`Phase-${index + 1} reference blob mismatch`),
      );
    });
  }

  it('rejects disagreement with the source hashes recorded by Phase 2', () => {
    assert.throws(
      () =>
        loadReferences((args) =>
          args[1] === `${PHASE2_REFERENCE.commit}:src/solver.ts`
            ? Buffer.from('different historical implementation')
            : readGit(args),
        ),
      /Phase-2 source provenance mismatch: src\/solver.ts/,
    );
  });

  it('reproduces all eight pinned fixtures without solving or writing reports', () => {
    verifyFixtures(
      fixtures.map(({ fixture }) => fixture),
      references,
    );
    assert.equal(fixtures.length, 8);
    assert.deepEqual(
      fixtures.map(({ fixture }) => fixture.maxConflicts),
      [200_000, 200_000, 200_000, 200_000, 200_000, 200_000, 7_230, 36_270],
    );
    assert.deepEqual(
      fixtures.slice(-2).map(({ fixture }) => fixture.calibratedConflicts),
      [723, 3627],
    );
    for (const { expr, fixture } of fixtures) {
      assert.equal(
        sha256(JSON.stringify({ expr, assumptions: fixture.assumptions })),
        fixture.fixtureSha256,
      );
    }
  });

  it('rejects fixture, assumption, cap, calibration, omission, and duplicate disagreements', () => {
    const metadata = fixtures.map(({ fixture }) => fixture);
    for (const change of [
      { fixture: 'different generator' },
      { fixtureSha256: '0'.repeat(64) },
      { assumptions: { h: Value.FALSE } },
      { maxConflicts: 200_001 },
      { calibratedConflicts: 1 },
    ]) {
      assert.throws(
        () => verifyFixtures([{ ...metadata[0], ...change }, ...metadata.slice(1)], references),
        /fixture disagreement/,
      );
    }
    assert.throws(
      () => verifyFixtures(metadata.slice(1), references),
      /fixture coverage disagreement/,
    );
    assert.throws(
      () => verifyFixtures([metadata[0], ...metadata.slice(0, -1)], references),
      /fixture coverage disagreement/,
    );
    for (const index of [6, 7]) {
      const changed = metadata.map((fixture, i) =>
        i === index ? { ...fixture, maxConflicts: fixture.maxConflicts + 1 } : fixture,
      );
      assert.throws(() => verifyFixtures(changed, references), /fixture disagreement/);
    }
  });

  it('fails on changed bytes or added/removed input sources even with the same HEAD', () => {
    const before = { 'src/solver.ts': sha256('original'), 'src/index.ts': sha256('api') };
    assertSourcesUnchanged(before, { ...before });
    for (const after of [
      { ...before, 'src/solver.ts': sha256('uncommitted change') },
      { ...before, 'src/new-module.ts': sha256('new input') },
      { 'src/solver.ts': before['src/solver.ts'] },
    ]) {
      assert.throws(
        () => assertSourcesUnchanged(before, after),
        /Benchmark input changed during the run/,
      );
    }
    const version = { sha256: before['src/solver.ts'], ino: 1n, mtimeNs: 1n, ctimeNs: 1n };
    assert.throws(
      () =>
        assertSourcesUnchanged(
          { 'src/solver.ts': version },
          { 'src/solver.ts': { ...version, ctimeNs: 2n } },
        ),
      /Benchmark input changed during the run/,
    );
  });
});

const stats: SolverStats = {
  decisions: 0,
  propagations: 0,
  conflicts: 0,
  restarts: 0,
  learnedClauses: 0,
  learnedClausesCurrent: 0,
};
const modelFixture: BenchmarkFixture = {
  name: 'model_probe',
  fixture: "or('a', 'b')",
  fixtureSha256: sha256('unit-test-only fixture'),
  assumptions: { a: Value.TRUE },
  maxConflicts: 100,
  calibratedConflicts: null,
};

describe('benchmark result validation', () => {
  it('accepts strict numeric models, empty SAT, and genuine UNSAT', () => {
    assertBenchmarkResult(
      or('a', 'b'),
      modelFixture,
      { a: Value.TRUE, b: Value.FALSE },
      stats,
      'SAT',
    );
    assertBenchmarkResult(and(), { ...modelFixture, assumptions: {} }, {}, stats, 'SAT');
    assertBenchmarkResult(or(), { ...modelFixture, assumptions: {} }, null, stats, 'UNSAT');
  });

  const badModels = [
    ['Boolean TRUE', { a: true, b: 0 }, /every model value must be TRUE or FALSE/],
    ['Boolean FALSE', { a: 1, b: false }, /every model value must be TRUE or FALSE/],
    ['UNSET', { a: 1, b: -1 }, /every model value must be TRUE or FALSE/],
    ['coerced numeric string', { a: '1', b: 0 }, /every model value must be TRUE or FALSE/],
    ['missing key', { a: 1 }, /model key set/],
    ['extra key', { a: 1, b: 0, auxiliary: 1 }, /model key set/],
    ['inherited key', Object.assign(Object.create({ a: 1 }), { b: 0 }), /ordinary model prototype/],
    [
      'null prototype',
      Object.assign(Object.create(null), { a: 1, b: 0 }),
      /ordinary model prototype/,
    ],
    [
      'hidden key',
      Object.defineProperty({ a: 1, b: 0 }, 'hidden', { value: 1 }),
      /hidden or symbol keys/,
    ],
    ['symbol key', { a: 1, b: 0, [Symbol('extra')]: 1 }, /hidden or symbol keys/],
    ['falsifying model', { a: 0, b: 0 }, /model falsifies AST/],
    ['constant assumption violation', { a: 0, b: 1 }, /model violates constant assumption/],
  ] as const;
  for (const [name, model, message] of badModels) {
    it(`rejects ${name} before accepting SAT evidence`, () => {
      assert.throws(
        () =>
          assertBenchmarkResult(
            or('a', 'b'),
            modelFixture,
            model as VariableAssignments,
            stats,
            'SAT',
          ),
        message,
      );
    });
  }

  it('checks arbitrary-name assumptions as own numeric properties, not inherited or coerced values', () => {
    for (const name of [
      '__proto__',
      'constructor',
      'toString',
      'hasOwnProperty',
      '',
      '0',
      'a=0,b',
      '"\\\n',
    ]) {
      const expr = or(name, not(name));
      const fixture = { ...modelFixture, assumptions: Object.fromEntries([[name, Value.TRUE]]) };
      assertBenchmarkResult(expr, fixture, Object.fromEntries([[name, Value.TRUE]]), stats, 'SAT');
      assert.throws(
        () =>
          assertBenchmarkResult(
            expr,
            fixture,
            Object.fromEntries([[name, Value.FALSE]]),
            stats,
            'SAT',
          ),
        /model violates constant assumption/,
      );
      assert.throws(
        () =>
          assertBenchmarkResult(
            expr,
            fixture,
            Object.fromEntries([[name, true]]) as unknown as VariableAssignments,
            stats,
            'SAT',
          ),
        /every model value must be TRUE or FALSE/,
      );
    }
  });

  it('fails on a changed verdict instead of recording it as a new baseline', () => {
    assert.throws(
      () => assertBenchmarkResult(or('a', 'b'), modelFixture, null, stats, 'SAT'),
      /verdict disagreement/,
    );
    assert.throws(
      () => assertBenchmarkResult(or('a', 'b'), modelFixture, { a: 1, b: 0 }, stats, 'UNSAT'),
      /verdict disagreement/,
    );
  });

  it('requires all six finite non-negative own numeric counters', () => {
    for (const counter of COUNTERS) {
      const missing: Partial<SolverStats> = { ...stats };
      delete missing[counter];
      assert.throws(
        () => assertBenchmarkResult(or(), modelFixture, null, missing as SolverStats, 'UNSAT'),
        /missing or invalid/,
      );
    }
    for (const value of [-1, Number.NaN, Number.POSITIVE_INFINITY, 0.5, 2 ** 53, true, '0']) {
      assert.throws(
        () =>
          assertBenchmarkResult(
            or(),
            modelFixture,
            null,
            { ...stats, decisions: value as number },
            'UNSAT',
          ),
        /missing or invalid decisions/,
      );
    }
    assert.throws(
      () => assertBenchmarkResult(or(), modelFixture, null, Object.create(stats), 'UNSAT'),
      /missing or invalid decisions/,
    );
  });

  it('throws on a conflict-budget exhaustion, including a false UNSAT at the cap', () => {
    const solver = new Solver(compile(cnfToExpr(phpCnf(3, 2))), {
      enablePle: true,
      maxConflicts: 1,
    });
    assert.throws(() => solver.solve(), /maximum conflict budget exhausted \(1\)/);
    assert.equal(solver.stats.conflicts, 1);
    for (const conflicts of [100, 101]) {
      assert.throws(
        () => assertBenchmarkResult(or(), modelFixture, null, { ...stats, conflicts }, 'UNSAT'),
        /maximum conflict budget exhausted \(100\)/,
      );
    }
  });

  it('enforces the exact hypergraph control and PHP learning without a speedup gate', () => {
    const { expr, fixture } = fixtures[0];
    const model = Object.fromEntries(
      [...Array(19)].map((_, i) => [String.fromCharCode(97 + i), Value.TRUE]),
    );
    const control = { ...stats, decisions: 2, propagations: 16 };
    assertBenchmarkResult(expr, fixture, model, control, 'SAT');
    for (const counter of ['decisions', 'propagations', 'conflicts'] as const) {
      assert.throws(
        () =>
          assertBenchmarkResult(
            expr,
            fixture,
            model,
            { ...control, [counter]: control[counter] + 1 },
            'SAT',
          ),
        /hypergraph must retain exactly/,
      );
    }
    const php = fixtures[1];
    assert.throws(
      () => assertBenchmarkResult(php.expr, php.fixture, null, stats, 'UNSAT'),
      /learning must be engaged/,
    );
  });
});

const implementation = {
  head: PHASE2_REFERENCE.commit,
  sourceSha256: { 'src/solver.ts': sha256('different working bytes under the same HEAD') },
  node: process.version,
  nodeEnv: null,
};
const syntheticResults = (): BenchmarkResult[] =>
  references.phase2.entries.map((entry) => {
    const { phase1: _phase1, phase2, ...fixture } = entry;
    return { ...fixture, phase3: { ...phase2 } as SolverStats };
  });

describe('Phase-3 report semantics (in-memory, no artifacts)', () => {
  it('reports raw six-counter data against BOTH phases with preserved provenance and missingness', () => {
    const { report, markdown } = createPhase3Report(references, implementation, syntheticResults());
    assert.deepEqual(report.references.phase1, PHASE1_REFERENCE);
    assert.deepEqual(report.references.phase2, {
      ...PHASE2_REFERENCE,
      provenance: {
        reference: references.phase2.reference,
        implementation: references.phase2.implementation,
      },
    });
    assert.deepEqual(report.implementation, implementation);
    for (const entry of report.entries) {
      assert.deepEqual(Object.keys(entry.phase3), COUNTERS);
      assert.deepEqual(entry.phase1, references.phase1[entry.name] ?? null);
      assert.deepEqual(
        entry.phase2,
        references.phase2.entries.find(({ name }) => name === entry.name)?.phase2,
      );
      assert.equal(Object.hasOwn(entry.phase1 ?? {}, 'learnedClausesCurrent'), false);
    }
    assert.equal(report.entries.find(({ name }) => name === 'php_7_6')?.phase1, null);
    assert.equal(report.entries.find(({ name }) => name === 'php_8_7')?.phase1, null);
    assert.match(markdown, /## Phase3 Vs Phase1/);
    assert.match(markdown, /## Phase3 Vs Phase2/);
    for (const phase of ['Phase1', 'Phase2']) {
      const section = markdown.split(`## Phase3 Vs ${phase}`)[1].split('\n## ')[0];
      const rows = section.split('\n').filter((line) => line.startsWith('| '));
      assert.equal(rows.length, report.entries.length * COUNTERS.length + 2);
    }
    assert.match(
      markdown,
      /\| php_7_6 \| conflicts \| not recorded \| 723 \| n\/a \| n\/a \| not comparable \|/,
    );
    assert.match(
      markdown,
      /\| hypergraph \| learnedClausesCurrent \| not recorded \| 0 \| n\/a \| n\/a \| not comparable \|/,
    );
    assert.match(
      markdown,
      /\| hypergraph \| conflicts \| 0 \| 0 \| 0 \| n\/a \(0\/0 parity\) \| parity \|/,
    );
    for (const reference of [PHASE1_REFERENCE, PHASE2_REFERENCE]) {
      for (const value of [reference.commit, reference.gitBlob, reference.sha256]) {
        assert.ok(markdown.includes(value));
      }
    }
  });

  it('explicitly lists a Phase-2 regression even when the same count improves on Phase 1', () => {
    const results = syntheticResults();
    const php = results.find(({ name }) => name === 'php_6_5');
    assert.ok(php);
    php.phase3.decisions = 300;
    php.phase3.restarts = 7;
    php.phase3.learnedClauses = 300;
    php.phase3.learnedClausesCurrent = 73;
    const { report, markdown } = createPhase3Report(references, implementation, results);
    assert.deepEqual(report.regressions, [
      {
        instance: 'php_6_5',
        reference: 'Phase2',
        counter: 'decisions',
        before: 195,
        after: 300,
        delta: 105,
      },
    ]);
    assert.match(
      markdown,
      /\| php_6_5 \| Phase2 \| decisions \| 195 \| 300 \| \+105 \| REGRESSION \(higher count\) \|/,
    );
    assert.match(markdown, /\| php_6_5 \| decisions \| 374 \| 300 \| -74 \| 1\.25x \| lower \|/);
    assert.match(markdown, /\| php_6_5 \| decisions \| 195 \| 300 \| \+105 \| 0\.65x \| higher \|/);
    assert.match(markdown, /Learning and restart counters report activity, not speedup/);
    assert.match(markdown, /No blanket performance gain/);
    assert.match(markdown, /does not measure persistent enumeration/);
  });

  it('keeps unrecorded reference counters missing and labels a Phase3 zero denominator', () => {
    const incomplete = structuredClone(references);
    const { learnedClausesCurrent: _missing, ...partial } = incomplete.phase2.entries[0].phase2;
    incomplete.phase2.entries[0].phase2 = partial;
    const results = syntheticResults();
    results[1].phase3.conflicts = 0;
    const { report, markdown } = createPhase3Report(incomplete, implementation, results);
    assert.equal(Object.hasOwn(report.entries[0].phase2, 'learnedClausesCurrent'), false);
    assert.match(
      markdown,
      /\| php_5_4 \| conflicts \| 28 \| 0 \| -28 \| n\/a \(Phase3 is zero\) \| lower \|/,
    );
    assert.match(
      markdown.split('## Phase3 Vs Phase2')[1],
      /\| hypergraph \| learnedClausesCurrent \| not recorded \| 0 \|/,
    );
  });

  it('lists decision, propagation, and conflict regressions against each reference independently', () => {
    const results = syntheticResults();
    const random = results.find(({ name }) => name === 'sat3_seed43');
    assert.ok(random);
    for (const counter of ['decisions', 'propagations', 'conflicts'] as const) {
      random.phase3[counter] += 1;
    }
    const { report } = createPhase3Report(references, implementation, results);
    assert.deepEqual(
      report.regressions.map(({ reference, counter, delta }) => [reference, counter, delta]),
      [
        ['Phase1', 'decisions', 1],
        ['Phase1', 'propagations', 1],
        ['Phase1', 'conflicts', 1],
        ['Phase2', 'decisions', 1],
        ['Phase2', 'propagations', 1],
        ['Phase2', 'conflicts', 1],
      ],
    );
  });

  it('rejects missing current counters, changed verdicts, and partial reports', () => {
    const results = syntheticResults();
    const { learnedClausesCurrent: _missing, ...missing } = results[0].phase3;
    assert.throws(
      () =>
        createPhase3Report(references, implementation, [
          { ...results[0], phase3: missing as SolverStats },
          ...results.slice(1),
        ]),
      /missing or invalid learnedClausesCurrent/,
    );
    assert.throws(
      () =>
        createPhase3Report(references, implementation, [
          { ...results[0], verdict: 'UNSAT' },
          ...results.slice(1),
        ]),
      /verdict disagreement/,
    );
    assert.throws(
      () => createPhase3Report(references, implementation, results.slice(1)),
      /fixture coverage disagreement/,
    );
  });

  it('is deterministic, with no model, timestamp, or wall-time data in either artifact', () => {
    const first = createPhase3Report(references, implementation, syntheticResults());
    const second = createPhase3Report(references, implementation, syntheticResults());
    assert.deepEqual(first, second);
    const json = `${JSON.stringify(first.report, null, 2)}\n`;
    assert.doesNotMatch(
      json,
      /"(?:wallMs|timestamp|generatedAt|models?|elapsedMs|mtimeNs|ctimeNs)"\s*:/,
    );
    assert.doesNotMatch(`${json}\n${first.markdown}`, /20\d\d-\d\d-\d\dT\d\d:/);
    assert.doesNotMatch(first.markdown, /\| wall ms/);
    assert.match(first.markdown, /Missing data remains incomparable/);
  });
});
