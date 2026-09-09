import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile } from '../src/compile.js';
import { and, not, or, Value } from '../src/expr.js';
import { luby, Solver } from '../src/solver.js';
import { expressionValue } from './helpers';

const invalidNumbers = [
  0,
  -0,
  -1,
  0.5,
  1.5,
  Number.NaN,
  Number.POSITIVE_INFINITY,
  Number.NEGATIVE_INFINITY,
  Number.MAX_SAFE_INTEGER + 1,
  Number.MAX_VALUE,
];

// Cast only at the call boundary to exercise runtime validation, not TS types.
const malformedNumbers: Array<[string, unknown]> = [
  ['null', null],
  ['numeric string', '1'],
  ['boolean', true],
  ['bigint', BigInt(1)],
  ['symbol', Symbol('1')],
  ['array', [1]],
  ['coercible object', { valueOf: () => 1 }],
  ['function', () => 1],
];

describe('one-based Luby sequence', () => {
  const prefix = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];

  it('matches the literal prefix starting at index one', () => {
    assert.deepStrictEqual(
      prefix.map((_, offset) => luby(offset + 1)),
      prefix,
    );
  });

  it('matches independently constructed blocks through index 4095', () => {
    // Build S_(k+1) by concatenating two complete copies of S_k and its next
    // power of two. No expected term uses luby() or its index-descent formula.
    let block = [1];
    for (let last = 2; last <= 2_048; last *= 2) {
      block = [...block, ...block, last];
    }
    for (let offset = 0; offset < block.length; offset += 1) {
      assert.strictEqual(luby(offset + 1), block[offset], `index ${offset + 1}`);
    }
  });

  it('keeps exact block boundaries and copied terms beyond 32 bits through MAX_SAFE_INTEGER', () => {
    // Concatenation gives S_k length 2^k - 1, ending in 2^(k-2), 2^(k-1).
    // The second copy of S_k starts at 2^k and repeats the literal prefix.
    for (const exponent of [31, 32, 40, 52]) {
      const start = 2 ** exponent;
      assert.strictEqual(luby(start - 2), 2 ** (exponent - 2), `index ${start - 2}`);
      assert.strictEqual(luby(start - 1), 2 ** (exponent - 1), `index ${start - 1}`);
      for (let offset = 0; offset < prefix.length; offset += 1) {
        assert.strictEqual(luby(start + offset), prefix[offset], `index ${start + offset}`);
      }
    }

    // The last three terms of S_53 follow directly from its nested block ends.
    const ending: Array<[number, number]> = [
      [Number.MAX_SAFE_INTEGER - 2, 2 ** 50],
      [Number.MAX_SAFE_INTEGER - 1, 2 ** 51],
      [Number.MAX_SAFE_INTEGER, 2 ** 52],
    ];
    for (const [index, expected] of ending) {
      assert.strictEqual(luby(index), expected, `index ${index}`);
    }
  });

  it('rejects numeric indices outside the positive safe integers', () => {
    for (const index of invalidNumbers) {
      assert.throws(
        () => luby(index),
        /Luby index must be a positive safe integer/,
        `index ${index}`,
      );
    }
  });

  it('rejects undefined and malformed runtime indices without coercion', () => {
    const cases: Array<[string, unknown]> = [['undefined', undefined], ...malformedNumbers];
    for (const [label, index] of cases) {
      assert.throws(
        () => luby(index as number),
        /Luby index must be a positive safe integer/,
        label,
      );
    }
  });
});

describe('internal restartBaseConflicts validation', () => {
  it('allows omitted options and an omitted or explicitly undefined base', () => {
    const cnf = compile(and());
    assert.doesNotThrow(() => new Solver(cnf));
    assert.doesNotThrow(() => new Solver(cnf, {}));
    assert.doesNotThrow(() => new Solver(cnf, { restartBaseConflicts: undefined }));
  });

  it('accepts positive safe integer bases', () => {
    for (const restartBaseConflicts of [1, 2, 3, 100]) {
      assert.doesNotThrow(() => new Solver(compile(and()), { restartBaseConflicts }));
    }
  });

  it('rejects numeric bases outside the positive safe integers', () => {
    for (const restartBaseConflicts of invalidNumbers) {
      assert.throws(
        () => new Solver(compile(and()), { restartBaseConflicts }),
        /restartBaseConflicts must be a positive safe integer/,
        `base ${restartBaseConflicts}`,
      );
    }
  });

  it('rejects malformed runtime bases without coercion or null defaulting', () => {
    for (const [label, restartBaseConflicts] of malformedNumbers) {
      assert.throws(
        () => new Solver(compile(and()), { restartBaseConflicts: restartBaseConflicts as number }),
        /restartBaseConflicts must be a positive safe integer/,
        label,
      );
    }
  });

  it('accepts huge safe bases without a spurious restart after one real conflict', () => {
    // FALSE-first a@1, b@2 forces opposite values of c. Resolving c learns
    // (a OR b), asserting b at level 1: a spurious restart cannot hide as a
    // root no-op. This is a large-base smoke test, not a schedule-scaling test.
    const formula = and(or('a', 'b', 'c'), or('a', 'b', not('c')));
    for (const restartBaseConflicts of [
      2 ** 31,
      2 ** 32,
      2 ** 32 + 1,
      2 ** 52 + 1,
      Number.MAX_SAFE_INTEGER,
    ]) {
      const label = `base ${restartBaseConflicts}`;
      const solver = new Solver(compile(formula), {
        restartPolicy: 'luby',
        restartBaseConflicts,
      });
      assert.strictEqual(solver.solve(), true, label);
      assert.strictEqual(solver.stats.conflicts, 1, label);
      assert.strictEqual(solver.stats.learnedClauses, 1, label);
      assert.strictEqual(solver.stats.restarts, 0, label);
      assert.strictEqual(expressionValue(formula, solver.model()), Value.TRUE, label);
    }
  });
});

describe('internal restartPolicy selector', () => {
  // Observation-only structural cast, matching the established internals seam.
  const policyKind = (solver: Solver): string =>
    (solver as unknown as { restartPolicy: { readonly kind: string } }).restartPolicy.kind;

  it('defaults to the knob-free EMA policy, even when only the Luby base is passed', () => {
    assert.strictEqual(policyKind(new Solver(compile(and()))), 'ema');
    assert.strictEqual(policyKind(new Solver(compile(and()), {})), 'ema');
    // The base validates but NEVER implicitly selects the Luby schedule.
    assert.strictEqual(policyKind(new Solver(compile(and()), { restartBaseConflicts: 1 })), 'ema');
    assert.strictEqual(policyKind(new Solver(compile(and()), { restartPolicy: 'ema' })), 'ema');
  });

  it('selects the Luby schedule only on explicit request', () => {
    assert.strictEqual(policyKind(new Solver(compile(and()), { restartPolicy: 'luby' })), 'luby');
    assert.strictEqual(
      policyKind(new Solver(compile(and()), { restartPolicy: 'luby', restartBaseConflicts: 7 })),
      'luby',
    );
  });

  it('rejects malformed runtime selectors without coercion', () => {
    const malformed: Array<[string, unknown]> = [
      ['capitalized', 'EMA'],
      ['other string', 'binary'],
      ['empty string', ''],
      ['zero', 0],
      ['null', null],
      ['boolean', true],
      ['array', ['luby']],
      ['object', { policy: 'luby' }],
    ];
    for (const [label, restartPolicy] of malformed) {
      assert.throws(
        () => new Solver(compile(and()), { restartPolicy: restartPolicy as 'luby' }),
        /restartPolicy must be 'ema' or 'luby'/,
        label,
      );
    }
  });

  it('keeps the Luby base validation independent of the selected policy', () => {
    // Format validation applies whenever the knob is present, under either
    // policy; the EMA default simply never consumes the validated value.
    assert.doesNotThrow(() => new Solver(compile(and()), { restartBaseConflicts: 5 }));
    assert.throws(
      () => new Solver(compile(and()), { restartPolicy: 'ema', restartBaseConflicts: 0 }),
      /restartBaseConflicts must be a positive safe integer/,
    );
    assert.throws(
      () => new Solver(compile(and()), { restartPolicy: 'luby', restartBaseConflicts: 1.5 }),
      /restartBaseConflicts must be a positive safe integer/,
    );
  });
});
