import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, statSync } from 'node:fs';
import { describe, it } from 'node:test';
import { compile } from '../src/compile.js';
import { and, not, or, Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import {
  assertBenchmarkResult,
  assertPhase4Manifest,
  assertPhase4Record,
  assertPhase4Sources,
  assertReferenceChain,
  assertSourcesUnchanged,
  benchmarkFixtures,
  comparisonCells,
  COUNTERS,
  createPhase4Report,
  loadPhase4Record,
  loadReferences,
  PHASE1_REFERENCE,
  PHASE2_REFERENCE,
  PHASE3_REFERENCE,
  PHASE4_MANIFEST_REFERENCE,
  PHASE4_MARKDOWN_REFERENCE,
  PHASE4_REFERENCE,
  sha256,
  verifyFixtures,
} from './bench-comparison.js';
import type {
  BenchmarkFixture,
  BenchmarkReferences,
  BenchmarkResult,
  Phase4Record,
  Phase4ReleaseManifest,
} from './bench-comparison.js';
import { runBenchmark, sourceSnapshot } from './bench.js';
import type { BenchmarkOptions, VerifyMode } from './bench.js';
import { cnfToExpr, expressionValue, phpCnf } from './helpers.js';

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
    assert.deepEqual(comparisonCells(5, 0), ['5', '0', '-5', 'n/a (Phase4 is zero)', 'lower']);
    assert.deepEqual(comparisonCells(5, 0, 'Phase2'), [
      '5',
      '0',
      '-5',
      'n/a (Phase2 is zero)',
      'lower',
    ]);
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

// Cache immutable Git objects only in this spec; every load still authenticates the bytes.
const gitObjects = new Map<string, Buffer>();
const readGit = (args: string[]): Buffer => {
  const key = JSON.stringify(args);
  let content = gitObjects.get(key);
  if (content === undefined || args[1] === 'HEAD') {
    content = execFileSync('git', args, { cwd: new URL('../', import.meta.url) });
    gitObjects.set(key, content);
  }
  return Buffer.from(content);
};
const references = loadReferences(readGit);
const fixtures = benchmarkFixtures();
const historicalReferences = [PHASE1_REFERENCE, PHASE2_REFERENCE, PHASE3_REFERENCE];
const phase4References = [PHASE4_REFERENCE, PHASE4_MARKDOWN_REFERENCE, PHASE4_MANIFEST_REFERENCE];
const allReferences = [...historicalReferences, ...phase4References];
const modes: VerifyMode[] = ['parity', 'gates'];
const phase4Record = loadPhase4Record(readGit, references);

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
    for (const reference of historicalReferences) {
      assert.ok(
        calls.some((args) => args.join(' ') === `show ${reference.commit}:${reference.path}`),
      );
      assert.equal(reference.commit.length, 40);
      assert.equal(reference.gitBlob.length, 40);
      assert.equal(reference.sha256.length, 64);
      const bytes = readGit(['show', `${reference.commit}:${reference.path}`]);
      assert.equal(createHash('sha256').update(bytes).digest('hex'), reference.sha256);
      assert.equal(
        readGit(['rev-parse', '--verify', `${reference.commit}:${reference.path}`])
          .toString('utf8')
          .trim(),
        reference.gitBlob,
      );
    }
    assert.deepEqual(references.phase2.reference, PHASE1_REFERENCE);
    assert.equal(references.phase2.implementation.head, PHASE1_REFERENCE.commit);
    assert.equal(
      references.phase2.implementation.sourceSha256['src/solver.ts'],
      'cee5031d304b5dacd9d8ed0a4de0b8908c4bd1ae5edd5f528aca79c0c85a12a1',
    );
    assert.equal(references.phase3.implementation.head, PHASE2_REFERENCE.commit);
    assert.equal(
      references.phase3.implementation.sourceSha256['src/solver.ts'],
      'b182fb21c54c54edb7c9bedb3aa97118c12db09707e00b03e79dee96e0fd6011',
    );
    assert.deepEqual(references.phase3.references, {
      phase1: PHASE1_REFERENCE,
      phase2: {
        ...PHASE2_REFERENCE,
        provenance: {
          reference: references.phase2.reference,
          implementation: references.phase2.implementation,
        },
      },
    });
    assert.deepEqual(
      calls.filter(([command]) => command === 'show').map(([, path]) => path),
      [
        ...historicalReferences.map(({ commit, path }) => `${commit}:${path}`),
        ...Object.keys(references.phase2.implementation.sourceSha256).map(
          (path) => `${PHASE2_REFERENCE.commit}:${path}`,
        ),
        ...Object.keys(references.phase3.implementation.sourceSha256).map(
          (path) => `${PHASE3_REFERENCE.commit}:${path}`,
        ),
      ],
      'source reads must use artifact commits, never recorded HEAD or working files',
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

  for (const [index, reference] of historicalReferences.entries()) {
    for (const command of ['rev-parse', 'show']) {
      it(`fails closed on missing Phase-${index + 1} ${command} history`, () => {
        const missing = new Error(`missing Phase-${index + 1} ${command}`);
        const calls: string[][] = [];
        assert.throws(
          () =>
            loadReferences((args) => {
              calls.push(args);
              if (args[0] === command && args.some((arg) => arg.startsWith(reference.commit))) {
                throw missing;
              }
              return readGit(args);
            }),
          (error) => error === missing,
        );
        assert.equal(calls.at(-1)?.[0], command);
        assert.ok(calls.every((args) => !args.includes('HEAD')));
      });
    }

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

  for (const [phase, reference, implementation] of [
    ['Phase-2', PHASE2_REFERENCE, references.phase2.implementation],
    ['Phase-3', PHASE3_REFERENCE, references.phase3.implementation],
  ] as const) {
    it(`rejects missing or modified ${phase} sources at the artifact commit`, () => {
      for (const path of Object.keys(implementation.sourceSha256)) {
        const missing = new Error(`missing historical source: ${path}`);
        assert.throws(
          () =>
            loadReferences((args) => {
              if (args[1] === `${reference.commit}:${path}`) {
                throw missing;
              }
              return readGit(args);
            }),
          (error) => error === missing,
        );
        assert.throws(
          () =>
            loadReferences((args) =>
              args[1] === `${reference.commit}:${path}`
                ? Buffer.from('different historical implementation')
                : readGit(args),
            ),
          new RegExp(`${phase} source provenance mismatch: ${path}`),
        );
      }
    });
  }

  it('checks decoded provenance-chain agreement separately from byte authentication', () => {
    const changes: Array<(value: BenchmarkReferences) => void> = [
      (value) => {
        value.phase2.reference.commit = '0'.repeat(40);
      },
      (value) => {
        value.phase3.references.phase1.sha256 = '0'.repeat(64);
      },
      (value) => {
        value.phase3.references.phase2.commit = '0'.repeat(40);
      },
      (value) => {
        value.phase3.references.phase2.gitBlob = '0'.repeat(40);
      },
      (value) => {
        value.phase3.references.phase2.provenance.reference.path = 'other.json';
      },
      (value) => {
        value.phase3.references.phase2.provenance.implementation.head = PHASE2_REFERENCE.commit;
      },
      (value) => {
        value.phase3.references.phase2.provenance.implementation.nodeEnv = 'production';
      },
      (value) => {
        value.phase3.references.phase2.provenance.implementation.sourceSha256['src/solver.ts'] =
          '0'.repeat(64);
      },
      (value) => {
        Reflect.deleteProperty(
          value.phase3.references.phase2.provenance.implementation.sourceSha256,
          'test/bench.ts',
        );
      },
      (value) => {
        value.phase2.implementation.sourceSha256['test/bench-comparison.ts'] = '0'.repeat(64);
      },
    ];
    for (const change of changes) {
      const changed = structuredClone(references);
      change(changed);
      assert.throws(() => assertReferenceChain(changed), /reference provenance disagreement/);
      assert.throws(
        () =>
          verifyFixtures(
            fixtures.map(({ fixture }) => fixture),
            changed,
          ),
        /reference provenance disagreement/,
      );
    }
  });

  it('requires the entire Phase-3 fixture/verdict/counter chain to agree with Phase 1/2', () => {
    const changes: Array<(value: BenchmarkReferences) => void> = [
      (value) => {
        value.phase3.entries[0].phase1 = null;
      },
      (value) => {
        value.phase3.entries[0].phase2.decisions = 3;
      },
      (value) => {
        Reflect.deleteProperty(value.phase3.entries[0].phase2, 'learnedClausesCurrent');
      },
      (value) => {
        value.phase3.entries[0].fixture = 'different generator';
      },
      (value) => {
        value.phase3.entries[0].fixtureSha256 = '0'.repeat(64);
      },
      (value) => {
        value.phase3.entries[0].assumptions.h = Value.FALSE;
      },
      (value) => {
        value.phase3.entries[0].maxConflicts += 1;
      },
      (value) => {
        value.phase3.entries[6].calibratedConflicts = 724;
      },
      (value) => {
        value.phase3.entries[0].verdict = 'UNSAT';
      },
      (value) => {
        value.phase3.entries.pop();
      },
      (value) => {
        value.phase3.entries[7] = value.phase3.entries[6];
      },
    ];
    for (const change of changes) {
      const changed = structuredClone(references);
      change(changed);
      assert.throws(() => assertReferenceChain(changed), /Phase-3 evidence chain disagreement/);
    }
    const changed = structuredClone(references);
    changed.phase2.entries[0].phase1 = null;
    assert.throws(() => assertReferenceChain(changed), /Phase-1 counters disagree/);
    changed.phase2.entries.push(changed.phase2.entries[0]);
    assert.throws(() => assertReferenceChain(changed), /duplicate Phase-2 instance/);
    const omitted = structuredClone(references);
    omitted.phase2.entries.shift();
    assert.throws(() => assertReferenceChain(omitted), /Missing original Phase-1 instance/);
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

describe('Phase-4 record authentication (release commit, manifest, embedded sources)', () => {
  it('authenticates the frozen record, markdown, and manifest from the release commit in one load', () => {
    const calls: string[][] = [];
    const record = loadPhase4Record((args) => {
      calls.push(args);
      return readGit(args);
    }, references);
    assert.deepEqual(record, phase4Record);
    for (const reference of phase4References) {
      assert.ok(
        calls.some((args) => args.join(' ') === `show ${reference.commit}:${reference.path}`),
        `must read ${reference.path} from the release commit`,
      );
      assert.equal(reference.commit.length, 40);
      assert.equal(reference.gitBlob.length, 40);
      assert.equal(reference.sha256.length, 64);
      const bytes = readGit(['show', `${reference.commit}:${reference.path}`]);
      assert.equal(createHash('sha256').update(bytes).digest('hex'), reference.sha256);
      assert.equal(
        readGit(['rev-parse', '--verify', `${reference.commit}:${reference.path}`])
          .toString('utf8')
          .trim(),
        reference.gitBlob,
      );
    }
    for (const path of Object.keys(phase4Record.implementation.sourceSha256)) {
      assert.ok(
        calls.some((args) => args.join(' ') === `show ${PHASE4_REFERENCE.commit}:${path}`),
        `must verify the embedded fingerprint of ${path} against the release commit`,
      );
    }
    assert.ok(
      calls.every((args) => !args.includes('HEAD')),
      'Phase-4 authentication must use the pinned artifact commit, never recorded HEAD',
    );
  });

  for (const reference of phase4References) {
    it(`fails closed when ${reference.path} history is missing`, () => {
      const missing = new Error(`missing pinned Phase-4 history: ${reference.path}`);
      assert.throws(
        () =>
          loadPhase4Record((args) => {
            if (args[0] === 'show' && args[1] === `${reference.commit}:${reference.path}`) {
              throw missing;
            }
            return readGit(args);
          }, references),
        (error) => error === missing,
      );
    });

    it(`rejects modified ${reference.path} bytes before parsing them`, () => {
      assert.throws(
        () =>
          loadPhase4Record(
            (args) =>
              args[0] === 'show' && args[1] === `${reference.commit}:${reference.path}`
                ? Buffer.from('{}')
                : readGit(args),
            references,
          ),
        /reference blob mismatch/,
      );
    });
  }

  it('cross-checks the manifest artifact identities against the pinned Phase-4 references', () => {
    const manifest = JSON.parse(
      readGit([
        'show',
        `${PHASE4_MANIFEST_REFERENCE.commit}:${PHASE4_MANIFEST_REFERENCE.path}`,
      ]).toString('utf8'),
    ) as Phase4ReleaseManifest;
    assertPhase4Manifest(manifest);
    const changes: Array<(value: Phase4ReleaseManifest) => void> = [
      (value) => {
        value.benchmark.artifacts.pop();
      },
      (value) => {
        value.benchmark.artifacts[0].path = 'test/other.json';
      },
      (value) => {
        value.benchmark.artifacts[0].gitBlob = '0'.repeat(40);
      },
      (value) => {
        value.benchmark.artifacts[0].sha256 = '0'.repeat(64);
      },
      (value) => {
        value.benchmark.artifacts[1].gitBlob = '0'.repeat(40);
      },
      (value) => {
        value.benchmark.artifacts[1].sha256 = '0'.repeat(64);
      },
    ];
    for (const change of changes) {
      const changed = structuredClone(manifest);
      change(changed);
      assert.throws(() => assertPhase4Manifest(changed), /Phase-4 manifest/);
    }
  });

  it('rejects decoded record tampering against the authenticated Phase-1/2/3 chain', () => {
    const changes: Array<(record: Phase4Record) => void> = [
      (record) => {
        record.phase = 'Phase3';
      },
      (record) => {
        record.scope = 'incremental';
      },
      (record) => {
        record.references.phase1.commit = '0'.repeat(40);
      },
      (record) => {
        record.references.phase2.gitBlob = '0'.repeat(40);
      },
      (record) => {
        record.references.phase3.sha256 = '0'.repeat(64);
      },
      (record) => {
        record.references.phase3.provenance.references.phase2.commit = '0'.repeat(40);
      },
      (record) => {
        record.references.phase3.provenance.implementation.nodeEnv = 'production';
      },
      (record) => {
        record.entries[0].verdict = 'UNSAT';
      },
      (record) => {
        record.entries[0].phase2.decisions = 3;
      },
      (record) => {
        record.entries[0].phase3.conflicts = 1;
      },
      (record) => {
        record.entries[0].fixtureSha256 = '0'.repeat(64);
      },
      (record) => {
        record.entries[0].maxConflicts += 1;
      },
      (record) => {
        record.entries[0].phase4.decisions = -1;
      },
      (record) => {
        record.entries.pop();
      },
    ];
    for (const change of changes) {
      const changed = structuredClone(phase4Record);
      change(changed);
      assert.throws(
        () => assertPhase4Record(changed, references),
        /Phase-4 record (?:phase|scope|provenance|coverage) disagreement|missing from Phase-3 evidence|disagrees with authenticated Phase-3 evidence|non-negative integer/,
      );
    }
  });

  it('verifies embedded Phase-4 source fingerprints against release-commit bytes, independent of edited working files', () => {
    // Today's bench.ts is a verifier, not the historical bytes hashed into the record.
    const working = sha256(readFileSync(new URL('../test/bench.ts', import.meta.url)));
    assert.notEqual(
      working,
      phase4Record.implementation.sourceSha256['test/bench.ts'],
      'precondition: the working bench.ts differs from the frozen release-commit bytes',
    );
    assertPhase4Sources(phase4Record, readGit);
    const unavailable = new Error('missing historical source: test/bench.ts');
    assert.throws(
      () =>
        assertPhase4Sources(phase4Record, (args) => {
          if (args[1] === `${PHASE4_REFERENCE.commit}:test/bench.ts`) {
            throw unavailable;
          }
          return readGit(args);
        }),
      (error) => error === unavailable,
    );
    assert.throws(
      () =>
        assertPhase4Sources(phase4Record, (args) =>
          args[1] === `${PHASE4_REFERENCE.commit}:test/bench.ts`
            ? Buffer.from('modified historical source')
            : readGit(args),
        ),
      /Phase-4 source provenance mismatch: test\/bench\.ts/,
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
  head: PHASE3_REFERENCE.commit,
  sourceSha256: { 'src/solver.ts': sha256('different working bytes under the same HEAD') },
  node: process.version,
  nodeEnv: null,
};
const syntheticResults = (): BenchmarkResult[] =>
  references.phase2.entries.map((entry) => {
    const { phase1: _phase1, phase2, ...fixture } = entry;
    return { ...fixture, phase4: { ...phase2 } as SolverStats };
  });

describe('Phase-4 synthetic report rendering (not runner/model validation, no artifacts)', () => {
  it('reports all 8x6 comparisons per phase with preserved provenance and missingness', () => {
    const { report, markdown } = createPhase4Report(references, implementation, syntheticResults());
    assert.equal(report.phase, 'Phase4');
    assert.equal(report.scope, 'single-shot');
    assert.deepEqual(Object.keys(report), [
      'phase',
      'scope',
      'references',
      'implementation',
      'notes',
      'regressions',
      'entries',
    ]);
    assert.deepEqual(Object.keys(report.references), ['phase1', 'phase2', 'phase3']);
    assert.deepEqual(report.references.phase1, PHASE1_REFERENCE);
    assert.deepEqual(report.references.phase2, {
      ...PHASE2_REFERENCE,
      provenance: {
        reference: references.phase2.reference,
        implementation: references.phase2.implementation,
      },
    });
    assert.deepEqual(report.references.phase3, {
      ...PHASE3_REFERENCE,
      provenance: {
        references: references.phase3.references,
        implementation: references.phase3.implementation,
      },
    });
    assert.equal(
      JSON.stringify(report.references.phase3.provenance.references),
      JSON.stringify(references.phase3.references),
      'preserve embedded Phase-1/2 provenance verbatim, including key order',
    );
    assert.equal(
      JSON.stringify({ phase1: report.references.phase1, phase2: report.references.phase2 }),
      JSON.stringify(references.phase3.references),
    );
    assert.equal(
      JSON.stringify(report.references.phase3.provenance.implementation),
      JSON.stringify(references.phase3.implementation),
    );
    assert.deepEqual(report.implementation, implementation);
    assert.equal(report.entries.length, 8);
    for (const entry of report.entries) {
      assert.deepEqual(
        Object.keys(entry).sort(),
        [
          'name',
          'fixture',
          'fixtureSha256',
          'assumptions',
          'maxConflicts',
          'calibratedConflicts',
          'verdict',
          'phase1',
          'phase2',
          'phase3',
          'phase4',
        ].sort(),
      );
      assert.deepEqual(Object.keys(entry.phase4), COUNTERS);
      assert.deepEqual(entry.phase1, references.phase1[entry.name] ?? null);
      assert.deepEqual(
        entry.phase2,
        references.phase2.entries.find(({ name }) => name === entry.name)?.phase2,
      );
      assert.deepEqual(
        entry.phase3,
        references.phase3.entries.find(({ name }) => name === entry.name)?.phase3,
      );
      assert.equal(Object.hasOwn(entry.phase1 ?? {}, 'learnedClausesCurrent'), false);
    }
    assert.equal(report.entries.find(({ name }) => name === 'php_7_6')?.phase1, null);
    assert.equal(report.entries.find(({ name }) => name === 'php_8_7')?.phase1, null);
    assert.match(markdown, /^# Phase-4 Release Single-Shot Benchmark Comparison/);
    for (const [key, phase] of [
      ['phase1', 'Phase1'],
      ['phase2', 'Phase2'],
      ['phase3', 'Phase3'],
    ] as const) {
      const section = markdown.split(`## Phase4 Vs ${phase}`)[1].split('\n## ')[0];
      const rows = section.split('\n').filter((line) => line.startsWith('| '));
      assert.equal(rows.length, report.entries.length * COUNTERS.length + 2);
      assert.deepEqual(
        rows.slice(2),
        report.entries.flatMap((entry) =>
          COUNTERS.map(
            (counter) =>
              `| ${[
                entry.name,
                counter,
                ...comparisonCells(entry[key]?.[counter], entry.phase4[counter], 'Phase4'),
              ].join(' | ')} |`,
          ),
        ),
      );
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
    for (const reference of historicalReferences) {
      for (const value of [reference.commit, reference.gitBlob, reference.sha256]) {
        assert.ok(markdown.includes(value));
      }
    }
    for (const [phase, previous] of [
      ['Phase-2', references.phase2.implementation],
      ['Phase-3', references.phase3.implementation],
    ] as const) {
      assert.ok(
        markdown.includes(
          `${phase} recorded HEAD (preserved, not its artifact commit): \`${previous.head}\``,
        ),
      );
      const section = markdown
        .split(`## Preserved ${phase} Source Fingerprints`)[1]
        .split('\n## ')[0];
      for (const [path, hash] of Object.entries(previous.sourceSha256)) {
        assert.ok(section.includes(`| ${path} | ${hash} |`));
      }
    }
  });

  it('explicitly lists Phase-2/3 regressions even when the same count improves on Phase 1', () => {
    const results = syntheticResults();
    const php = results.find(({ name }) => name === 'php_6_5');
    assert.ok(php);
    php.phase4.decisions = 300;
    php.phase4.restarts = 7;
    php.phase4.learnedClauses = 300;
    php.phase4.learnedClausesCurrent = 73;
    const { report, markdown } = createPhase4Report(references, implementation, results);
    assert.deepEqual(report.regressions, [
      {
        instance: 'php_6_5',
        reference: 'Phase2',
        counter: 'decisions',
        before: 195,
        after: 300,
        delta: 105,
      },
      {
        instance: 'php_6_5',
        reference: 'Phase3',
        counter: 'decisions',
        before: 205,
        after: 300,
        delta: 95,
      },
    ]);
    assert.match(
      markdown,
      /\| php_6_5 \| Phase2 \| decisions \| 195 \| 300 \| \+105 \| REGRESSION \(higher count\) \|/,
    );
    assert.match(markdown, /\| php_6_5 \| decisions \| 374 \| 300 \| -74 \| 1\.25x \| lower \|/);
    assert.match(markdown, /\| php_6_5 \| decisions \| 195 \| 300 \| \+105 \| 0\.65x \| higher \|/);
    assert.match(
      markdown,
      /\| php_6_5 \| Phase3 \| decisions \| 205 \| 300 \| \+95 \| REGRESSION \(higher count\) \|/,
    );
    assert.match(markdown, /\| php_6_5 \| decisions \| 205 \| 300 \| \+95 \| 0\.68x \| higher \|/);
    assert.match(markdown, /Learning and restart counters report activity, not speedup/);
    assert.match(markdown, /No blanket performance gain/);
    assert.match(markdown, /does not measure createSolver performance or persistent enumeration/);
    assert.match(markdown, /not peak or total memory/);
    assert.match(markdown, /default reduction threshold is not lowered/);
    assert.match(
      markdown,
      /do not count reduction events or establish default-reduction engagement/,
    );
    assert.match(markdown, /preclude any implied total-memory bound/);
  });

  it('keeps unrecorded reference counters missing and labels Phase4 zero denominators', () => {
    const incomplete = structuredClone(references);
    const { learnedClausesCurrent: _missing, ...partial } = incomplete.phase2.entries[0].phase2;
    incomplete.phase2.entries[0].phase2 = partial;
    incomplete.phase3.entries[0].phase2 = { ...partial };
    Reflect.deleteProperty(incomplete.phase3.entries[0].phase3, 'learnedClausesCurrent');
    const results = syntheticResults();
    results[1].phase4.conflicts = 0;
    const { report, markdown } = createPhase4Report(incomplete, implementation, results);
    assert.equal(Object.hasOwn(report.entries[0].phase2, 'learnedClausesCurrent'), false);
    assert.match(
      markdown,
      /\| php_5_4 \| conflicts \| 28 \| 0 \| -28 \| n\/a \(Phase4 is zero\) \| lower \|/,
    );
    assert.equal(Object.hasOwn(report.entries[0].phase3, 'learnedClausesCurrent'), false);
    for (const phase of ['Phase1', 'Phase2', 'Phase3']) {
      const section = markdown.split(`## Phase4 Vs ${phase}`)[1].split('\n## ')[0];
      assert.match(section, /\| hypergraph \| learnedClausesCurrent \| not recorded \| 0 \|/);
      assert.match(
        section,
        /\| php_5_4 \| conflicts \| (?:28|52) \| 0 \| -(?:28|52) \| n\/a \(Phase4 is zero\) \| lower \|/,
      );
    }
  });

  it('lists decision, propagation, and conflict regressions against each reference independently', () => {
    const results = syntheticResults();
    const random = results.find(({ name }) => name === 'sat3_seed43');
    assert.ok(random);
    for (const counter of ['decisions', 'propagations', 'conflicts'] as const) {
      random.phase4[counter] += 1;
    }
    const { report } = createPhase4Report(references, implementation, results);
    assert.deepEqual(
      report.regressions.map(({ reference, counter, delta }) => [reference, counter, delta]),
      [
        ['Phase1', 'decisions', 1],
        ['Phase1', 'propagations', 1],
        ['Phase1', 'conflicts', 1],
        ['Phase2', 'decisions', 1],
        ['Phase2', 'propagations', 1],
        ['Phase2', 'conflicts', 1],
        ['Phase3', 'decisions', 1],
        ['Phase3', 'propagations', 1],
        ['Phase3', 'conflicts', 1],
      ],
    );
  });

  it('rejects missing current counters, changed verdicts, and partial reports', () => {
    const results = syntheticResults();
    const { learnedClausesCurrent: _missing, ...missing } = results[0].phase4;
    assert.throws(
      () =>
        createPhase4Report(references, implementation, [
          { ...results[0], phase4: missing as SolverStats },
          ...results.slice(1),
        ]),
      /missing or invalid learnedClausesCurrent/,
    );
    assert.throws(
      () =>
        createPhase4Report(references, implementation, [
          { ...results[0], verdict: 'UNSAT' },
          ...results.slice(1),
        ]),
      /verdict disagreement/,
    );
    assert.throws(
      () => createPhase4Report(references, implementation, results.slice(1)),
      /fixture coverage disagreement/,
    );
  });

  it('is deterministic, with no model, timestamp, or wall-time data in either artifact', () => {
    const first = createPhase4Report(references, implementation, syntheticResults());
    const second = createPhase4Report(references, implementation, syntheticResults());
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

  it('stores only the six counters in canonical order, not incidental solver metadata', () => {
    const results = syntheticResults();
    const original = results[0].phase4;
    results[0].phase4 = {
      ...Object.fromEntries([...COUNTERS].reverse().map((counter) => [counter, original[counter]])),
      model: { h: Value.TRUE },
      wallMs: 1,
    } as unknown as SolverStats;
    const { report } = createPhase4Report(references, implementation, results);
    assert.deepEqual(Object.keys(report.entries[0].phase4), COUNTERS);
    assert.deepEqual(report.entries[0].phase4, original);
  });
});

// Exercise the actual verifier, including SAT model validation and both modes.
// Only PHP searches are stubbed with historical counts/UNSAT; these are NOT new measurements.
function runnerControl() {
  const instances = benchmarkFixtures();
  const logs: string[] = [];
  const events: string[] = [];
  const snapshots: ReturnType<typeof sourceSnapshot>[] = [];
  const compiled: BooleanExpr[] = [];
  const solvers: Solver[] = [];
  const solverOptions: Array<ConstructorParameters<typeof Solver>[1]> = [];
  const models: Array<{ index: number; model: VariableAssignments }> = [];
  const runtime = {
    compile: (expr: BooleanExpr) => {
      events.push('compile');
      compiled.push(expr);
      return compile(expr);
    },
    Solver: class extends Solver {
      private readonly instanceIndex = solvers.length;

      constructor(...args: ConstructorParameters<typeof Solver>) {
        super(...args);
        solvers.push(this);
        solverOptions.push(args[1]);
      }

      override solve(): boolean {
        const previous = references.phase3.entries[this.instanceIndex];
        if (previous.verdict === 'UNSAT') {
          Object.assign(this.stats, previous.phase3);
          return false;
        }
        return super.solve();
      }

      override model(): VariableAssignments {
        const model = super.model();
        models.push({ index: this.instanceIndex, model });
        return model;
      }
    },
  };
  const options: BenchmarkOptions = {
    readGit,
    snapshotSources: () => {
      events.push('snapshot');
      const snapshot = sourceSnapshot();
      snapshots.push(snapshot);
      return snapshot;
    },
    loadSolver: async () => {
      events.push('load solver');
      return runtime;
    },
    fixtures: () => {
      events.push('fixtures');
      return instances;
    },
    log: (message) => {
      logs.push(message);
    },
  };
  return {
    options,
    runtime,
    instances,
    logs,
    events,
    snapshots,
    compiled,
    solvers,
    solverOptions,
    models,
  };
}

describe('actual legacy benchmark verifier (in-memory, real SAT solves, stubbed PHP searches)', () => {
  for (const mode of modes) {
    it(`verifies the unchanged tree in ${mode} mode with real model validation and zero writes`, async () => {
      const control = runnerControl();
      await runBenchmark({ ...control.options, mode });
      assert.equal(control.compiled.length, 8);
      assert.equal(new Set(control.compiled).size, 8);
      assert.equal(new Set(control.solvers).size, 8);
      assert.deepEqual(
        control.models.map(({ index }) => index),
        [0, 3, 4, 5],
      );
      for (const { index, model } of control.models) {
        assert.equal(expressionValue(control.instances[index].expr, model), Value.TRUE);
      }
      for (const [index, options] of control.solverOptions.entries()) {
        const fixture = control.instances[index].fixture;
        assert.deepEqual(options, {
          assumptions: fixture.assumptions,
          enablePle: true,
          maxConflicts: fixture.maxConflicts,
        });
        assert.notEqual(options?.assumptions, fixture.assumptions);
      }
      assert.deepEqual(control.events.slice(0, 4), [
        'snapshot',
        'load solver',
        'snapshot',
        'fixtures',
      ]);
      assert.deepEqual(control.events.slice(-1), ['snapshot']);
      assert.equal(control.snapshots.length, 3);
      const before = control.snapshots[0];
      for (const path of [
        'src/compile.ts',
        'src/expr.ts',
        'src/index.ts',
        'src/solver.ts',
        'test/bench.ts',
        'test/bench-comparison.ts',
        'test/helpers.ts',
        'test/php-regressions.ts',
        'package.json',
        'package-lock.json',
        'tsconfig.json',
      ]) {
        const url = new URL(`../${path}`, import.meta.url);
        const { ino, mtimeNs, ctimeNs } = statSync(url, { bigint: true });
        assert.deepEqual(before[path], {
          sha256: sha256(readFileSync(url)),
          ino,
          mtimeNs,
          ctimeNs,
        });
      }
      const logs = control.logs.join('\n');
      assert.match(logs, new RegExp(`verifier \\(${mode} mode; assert-only, writes nothing\\)`));
      assert.match(logs, /wall ms \(compile \+ solve\)/);
      assert.match(logs, /Nothing was written/);
      if (mode === 'parity') {
        assert.match(logs, /all 48 counters exactly match the frozen Phase-4 record/);
      } else {
        assert.match(logs, /Gates verified/);
        assert.match(logs, /All 48 counters match the frozen Phase-4 record/);
      }
    });
  }

  it('leaves every frozen Phase-4 artifact byte-identical, including file versions, in both modes', async () => {
    const artifactUrls = [
      'test/phase4-benchmark.json',
      'test/phase4-benchmark.md',
      'test/phase4-release-manifest.json',
    ].map((path) => new URL(`../${path}`, import.meta.url));
    const fingerprint = (url: URL) => {
      const { ino, mtimeNs, ctimeNs } = statSync(url, { bigint: true });
      return { sha256: sha256(readFileSync(url)), ino, mtimeNs, ctimeNs };
    };
    const before = artifactUrls.map(fingerprint);
    for (const mode of modes) {
      const control = runnerControl();
      await runBenchmark({ ...control.options, mode });
    }
    assert.deepEqual(
      artifactUrls.map(fingerprint),
      before,
      'verify mode must not rewrite, touch, or replace the frozen Phase-4 artifacts',
    );
  });

  it('is deterministic through the actual verifier in both modes', async () => {
    const normalized = (control: ReturnType<typeof runnerControl>) =>
      control.logs.join('\n').replace(/\d+\.\d+/g, '<wall ms>');
    for (const mode of modes) {
      const first = runnerControl();
      await runBenchmark({ ...first.options, mode });
      const second = runnerControl();
      await runBenchmark({ ...second.options, mode });
      assert.equal(normalized(first), normalized(second));
    }
  });

  it('fails closed for missing or modified references in every phase, in both modes', async () => {
    for (const reference of allReferences) {
      for (const mode of modes) {
        for (const missing of [true, false]) {
          const control = runnerControl();
          const unavailable = new Error('missing pinned reference');
          control.options.readGit = (args) => {
            if (args[0] === 'show' && args[1] === `${reference.commit}:${reference.path}`) {
              if (missing) {
                throw unavailable;
              }
              return Buffer.from('{}');
            }
            return readGit(args);
          };
          await assert.rejects(
            runBenchmark({ ...control.options, mode }),
            missing ? (error: unknown) => error === unavailable : /reference blob mismatch/,
          );
          assert.equal(control.solvers.length, 0);
        }
      }
    }
  });

  it('fails closed for missing or modified historical implementation sources at every artifact commit, in both modes', async () => {
    for (const [reference, paths] of [
      [PHASE2_REFERENCE, ['src/solver.ts', 'test/bench-comparison.ts']],
      [PHASE3_REFERENCE, ['src/solver.ts', 'test/bench-comparison.ts']],
      // Embedded Phase-4 fingerprints are checked against release-commit bytes,
      // independently of today's edited verifier sources.
      [PHASE4_REFERENCE, ['src/solver.ts', 'test/bench.ts']],
    ] as const) {
      for (const mode of modes) {
        for (const path of paths) {
          for (const missing of [true, false]) {
            const control = runnerControl();
            const unavailable = new Error('missing historical source');
            control.options.readGit = (args) => {
              if (args[1] === `${reference.commit}:${path}`) {
                if (missing) {
                  throw unavailable;
                }
                return Buffer.from('modified historical source');
              }
              return readGit(args);
            };
            await assert.rejects(
              runBenchmark({ ...control.options, mode }),
              missing ? (error: unknown) => error === unavailable : /source provenance mismatch/,
            );
            assert.equal(control.solvers.length, 0);
          }
        }
      }
    }
  });

  for (const mode of modes) {
    it(`rejects fixture metadata, coverage, caps, and actual AST changes before compiling (${mode} mode)`, async () => {
      const changes: Array<(instances: ReturnType<typeof benchmarkFixtures>) => void> = [
        (instances) => {
          instances[0].fixture.fixture = 'different generator';
        },
        (instances) => {
          instances[0].fixture.fixtureSha256 = '0'.repeat(64);
        },
        (instances) => {
          instances[0].fixture.assumptions.h = Value.FALSE;
        },
        (instances) => {
          instances[0].expr = or();
        },
        (instances) => {
          instances.pop();
        },
        (instances) => {
          instances[7] = instances[6];
        },
        (instances) => {
          instances[6].fixture.maxConflicts += 1;
        },
        (instances) => {
          instances[7].fixture.maxConflicts += 1;
        },
        (instances) => {
          instances[6].fixture.calibratedConflicts = 724;
        },
        ...[0, -1, 200_001, Number.NaN, Number.POSITIVE_INFINITY, 0.5, true, '200000'].map(
          (maxConflicts) => (instances: ReturnType<typeof benchmarkFixtures>) => {
            instances[0].fixture.maxConflicts = maxConflicts as number;
          },
        ),
      ];
      for (const change of changes) {
        const control = runnerControl();
        change(control.instances);
        await assert.rejects(
          runBenchmark({ ...control.options, mode }),
          /fixture (?:coverage )?disagreement|fixture changed during the run/,
        );
        assert.equal(control.compiled.length, 0);
      }
    });
  }

  it('rechecks AST/assumption hashes and metadata after all solves, before verification completes', async () => {
    const changes: Array<(instances: ReturnType<typeof benchmarkFixtures>) => void> = [
      (instances) => {
        instances[0].expr = or();
      },
      (instances) => {
        instances[0].fixture.assumptions.h = Value.FALSE;
      },
      (instances) => {
        instances[0].fixture.maxConflicts += 1;
      },
    ];
    for (const change of changes) {
      const control = runnerControl();
      const Base = control.runtime.Solver;
      control.runtime.Solver = class extends Base {
        override solve(): boolean {
          const sat = super.solve();
          if (control.solvers.length === 8) {
            change(control.instances);
          }
          return sat;
        }
      };
      await assert.rejects(
        runBenchmark(control.options),
        /fixture disagreement|fixture changed during the run/,
      );
      assert.equal(control.solvers.length, 8);
    }
  });

  const badModels: Array<[string, (model: VariableAssignments) => unknown, RegExp]> = [
    ['Boolean TRUE', (model) => ({ ...model, h: true }), /every model value must be TRUE or FALSE/],
    [
      'Boolean FALSE',
      (model) => ({ ...model, a: false }),
      /every model value must be TRUE or FALSE/,
    ],
    ['UNSET', (model) => ({ ...model, h: Value.UNSET }), /every model value must be TRUE or FALSE/],
    [
      'numeric string',
      (model) => ({ ...model, h: '1' }),
      /every model value must be TRUE or FALSE/,
    ],
    [
      'missing key',
      (model) => {
        const { h: _missing, ...rest } = model;
        return rest;
      },
      /model key set/,
    ],
    ['extra key', (model) => ({ ...model, auxiliary: 1 }), /model key set/],
    [
      'inherited key',
      (model) => {
        const { h, ...rest } = model;
        return Object.assign(Object.create({ h }), rest);
      },
      /ordinary model prototype/,
    ],
    [
      'null prototype',
      (model) => Object.assign(Object.create(null), model),
      /ordinary model prototype/,
    ],
    [
      'hidden key',
      (model) => Object.defineProperty(model, 'hidden', { value: 1 }),
      /hidden or symbol keys/,
    ],
    ['symbol key', (model) => ({ ...model, [Symbol('extra')]: 1 }), /hidden or symbol keys/],
    [
      'falsifying AST',
      (model) => ({ ...model, h: Value.TRUE, a: Value.FALSE }),
      /model falsifies AST/,
    ],
    ['null SAT model', () => null, /solver verdict\/model disagreement/],
  ];
  for (const [label, change, message] of badModels) {
    it(`rejects ${label} in the verifier, not just the renderer`, async () => {
      const control = runnerControl();
      const Base = control.runtime.Solver;
      control.runtime.Solver = class extends Base {
        override model(): VariableAssignments {
          return change(super.model()) as VariableAssignments;
        }
      };
      await assert.rejects(runBenchmark(control.options), message);
    });
  }

  it('independently rejects a valid AST model that violates the original constant assumption', async () => {
    const control = runnerControl();
    const Base = control.runtime.Solver;
    control.runtime.Solver = class extends Base {
      constructor(...args: ConstructorParameters<typeof Solver>) {
        // Mutate the solver's copy before construction, not the validator's assumptions.
        if (args[1]?.assumptions && Object.hasOwn(args[1].assumptions, 'h')) {
          args[1].assumptions.h = Value.FALSE;
        }
        super(...args);
      }

      override solve(): boolean {
        const sat = super.solve();
        // Isolate model/assumption validation from the separate hypergraph counter oracle.
        Object.assign(this.stats, { ...stats, decisions: 2, propagations: 16 });
        return sat;
      }
    };
    await assert.rejects(runBenchmark(control.options), /model violates constant assumption/);
    assert.equal(expressionValue(control.instances[0].expr, control.models[0].model), Value.TRUE);
    assert.equal(control.instances[0].fixture.assumptions.h, Value.TRUE);
    assert.equal(control.models[0].model.h, Value.FALSE);
  });

  it('rejects missing, inherited, or invalid counters before verification completes', async () => {
    const changes: Array<(stats: SolverStats) => void> = [
      ...COUNTERS.map((counter) => (stats: SolverStats) => {
        delete (stats as Partial<SolverStats>)[counter];
      }),
      ...[-1, Number.NaN, Number.POSITIVE_INFINITY, 0.5, 2 ** 53, true, '0', null].map(
        (value) => (stats: SolverStats) => {
          stats.decisions = value as number;
        },
      ),
      (stats) => {
        Object.setPrototypeOf(stats, { ...stats });
        Reflect.deleteProperty(stats, 'decisions');
      },
    ];
    for (const change of changes) {
      const control = runnerControl();
      const Base = control.runtime.Solver;
      control.runtime.Solver = class extends Base {
        override solve(): boolean {
          const sat = super.solve();
          change(this.stats);
          return sat;
        }
      };
      await assert.rejects(runBenchmark(control.options), /missing or invalid/);
    }
  });

  it('propagates solver budget exceptions and rejects false UNSAT at or beyond the cap', async () => {
    const exhausted = new Error('maximum conflict budget exhausted (200000)');
    for (const conflicts of [null, 200_000, 200_001]) {
      const control = runnerControl();
      const Base = control.runtime.Solver;
      control.runtime.Solver = class extends Base {
        override solve(): boolean {
          if (conflicts === null) {
            throw exhausted;
          }
          this.stats.conflicts = conflicts;
          return false;
        }
      };
      await assert.rejects(
        runBenchmark(control.options),
        conflicts === null
          ? (error: unknown) => error === exhausted
          : /maximum conflict budget exhausted \(200000\)/,
      );
    }
  });

  for (const mode of modes) {
    it(`rejects invalid or changed solver verdicts (${mode} mode)`, async () => {
      for (const verdict of [false, 0, 1, 'SAT', null, undefined]) {
        const control = runnerControl();
        const Base = control.runtime.Solver;
        control.runtime.Solver = class extends Base {
          override solve(): boolean {
            super.solve();
            return verdict as boolean;
          }
        };
        await assert.rejects(
          runBenchmark({ ...control.options, mode }),
          /verdict disagreement|invalid solver verdict/,
        );
      }
    });
  }

  for (const mode of modes) {
    it(`enforces the hypergraph and PHP learning controls (${mode} mode)`, async () => {
      for (const invalidHypergraph of [true, false]) {
        const control = runnerControl();
        const Base = control.runtime.Solver;
        control.runtime.Solver = class extends Base {
          override solve(): boolean {
            const sat = super.solve();
            if (invalidHypergraph) {
              this.stats.decisions += 1;
            } else if (control.solvers.length === 2) {
              this.stats.learnedClauses = 0;
            }
            return sat;
          }
        };
        await assert.rejects(
          runBenchmark({ ...control.options, mode }),
          invalidHypergraph ? /hypergraph must retain exactly/ : /learning must be engaged/,
        );
      }
    });
  }

  it('fails parity mode on a changed candidate counter but only reports it in gates mode', async () => {
    const makeControl = () => {
      const control = runnerControl();
      const Base = control.runtime.Solver;
      control.runtime.Solver = class extends Base {
        override solve(): boolean {
          const sat = super.solve();
          // php_5_4 (instance 1): no verdict/oracle/cap check pins restarts, so
          // parity alone must catch the drift and gates mode must only report it.
          if (control.solvers.length === 2) {
            this.stats.restarts += 1;
          }
          return sat;
        }
      };
      return control;
    };
    const parity = makeControl();
    await assert.rejects(
      runBenchmark({ ...parity.options, mode: 'parity' }),
      /php_5_4: restarts broke Phase-4 parity \(current \d+, frozen \d+\)/,
    );
    const gates = makeControl();
    await runBenchmark({ ...gates.options, mode: 'gates' });
    const logs = gates.logs.join('\n');
    assert.match(logs, /Counter deltas \(non-fatal in gates mode\)/);
    assert.match(logs, /\| php_5_4 \| restarts \| \d+ \| \d+ \| \+1 \|/);
    assert.match(logs, /Gates verified/);
  });

  it('guards real snapshots after imports and before verification completes, including same-byte file versions', async () => {
    const changes: Array<(snapshot: ReturnType<typeof sourceSnapshot>) => void> = [
      (snapshot) => {
        snapshot['src/solver.ts'] = {
          ...snapshot['src/solver.ts'],
          sha256: sha256('changed source'),
        };
      },
      (snapshot) => {
        snapshot['src/solver.ts'] = {
          ...snapshot['src/solver.ts'],
          ino: snapshot['src/solver.ts'].ino + 1n,
        };
      },
      (snapshot) => {
        snapshot['src/solver.ts'] = {
          ...snapshot['src/solver.ts'],
          mtimeNs: snapshot['src/solver.ts'].mtimeNs + 1n,
        };
      },
      (snapshot) => {
        snapshot['src/solver.ts'] = {
          ...snapshot['src/solver.ts'],
          ctimeNs: snapshot['src/solver.ts'].ctimeNs + 1n,
        };
      },
      (snapshot) => {
        Reflect.deleteProperty(snapshot, 'test/bench-comparison.ts');
      },
      (snapshot) => {
        snapshot['src/new-module.ts'] = { ...snapshot['src/solver.ts'] };
      },
      (snapshot) => {
        snapshot['test/bench-config.ts'] = { ...snapshot['test/bench-comparison.ts'] };
      },
    ];
    for (const boundary of [2, 3]) {
      for (const change of changes) {
        const control = runnerControl();
        const snapshotSources = control.options.snapshotSources;
        assert.ok(snapshotSources);
        control.options.snapshotSources = () => {
          const snapshot = snapshotSources();
          if (control.snapshots.length === boundary) {
            change(snapshot);
          }
          return snapshot;
        };
        await assert.rejects(
          runBenchmark(control.options),
          /Benchmark input changed during the run/,
        );
        assert.equal(control.snapshots.length, boundary);
        assert.equal(control.solvers.length, boundary === 2 ? 0 : 8);
      }
    }
  });
});
