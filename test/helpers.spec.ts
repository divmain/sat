// Executable home for the test-infrastructure helpers' acceptance assertions.
// The helpers themselves live in `helpers.ts`, which deliberately does not
// match `*.spec.ts`.
//
// Everything here is deterministic: every randomized test runs on a fixed
// mulberry32 seed and asserts properties that hold by construction for that
// seed (verified once by hand, then pinned forever).
import { describe, it } from 'node:test';
import assert from 'node:assert';
import { and, getVariables, implies, isVariable, not, or, Value, xor } from '../src/expr.js';
import type { BooleanExpr, Variable, VariableAssignments } from '../src/expr.js';
import {
  assertModelListsEqual,
  assertModelShape,
  enumerateAssignments,
  expressionValue,
  modelKey,
  modelsEqual,
  mulberry32,
  randomAssumptions,
  randomFormula,
  referenceModels,
  sortModels,
} from './helpers.js';

// Local spec utilities (deterministic; no randomness except through helpers).

const FALSE = Value.FALSE;
const TRUE = Value.TRUE;
const ARBITRARY_NAMES = [
  '__proto__',
  'constructor',
  'toString',
  'hasOwnProperty',
  '',
  'a=0,b',
  '0',
  'quote"\\\n\u03bb',
];

// True when some model matches `partial` on every assigned variable.
function hasExtension(partial: VariableAssignments, models: VariableAssignments[]): boolean {
  return models.some((model) =>
    Object.entries(partial).every(
      ([key, value]) => Object.hasOwn(model, key) && model[key] === value,
    ),
  );
}

// Depth, maximum fan-in, and the set of AST node kinds below `node`.
function astStats(node: Variable | BooleanExpr): {
  depth: number;
  maxFanIn: number;
  kinds: Set<string>;
} {
  if (isVariable(node)) {
    return { depth: 0, maxFanIn: 0, kinds: new Set(['var']) };
  }
  let childNodes: Array<Variable | BooleanExpr>;
  let kind: string;
  if ('and' in node) {
    childNodes = node.and;
    kind = 'and';
  } else if ('or' in node) {
    childNodes = node.or;
    kind = 'or';
  } else if ('not' in node) {
    childNodes = [node.not];
    kind = 'not';
  } else if ('atMost' in node) {
    childNodes = node.atMost.exprs;
    kind = 'atMost';
  } else {
    childNodes = node.atLeast.exprs;
    kind = 'atLeast';
  }
  const childStats = childNodes.map((child) => astStats(child));
  const depth = 1 + Math.max(0, ...childStats.map((stats) => stats.depth));
  const maxFanIn = Math.max(childNodes.length, ...childStats.map((stats) => stats.maxFanIn));
  const kinds = new Set<string>([kind]);
  for (const stats of childStats) {
    for (const nestedKind of stats.kinds) {
      kinds.add(nestedKind);
    }
  }
  return { depth, maxFanIn, kinds };
}

describe('mulberry32 PRNG', () => {
  // Pinned once by hand from the reference implementation; any future
  // correct implementation must reproduce these stream prefixes exactly.
  const GOLDEN_STREAMS: ReadonlyArray<readonly [number, readonly number[]]> = [
    [
      0,
      [
        0.26642920868471265, 0.0003297457005828619, 0.2232720274478197, 0.1462021479383111,
        0.46732782293111086, 0.5450490827206522,
      ],
    ],
    [
      1,
      [
        0.6270739405881613, 0.002735721180215478, 0.5274470399599522, 0.9810509674716741,
        0.9683778982143849, 0.281103502959013,
      ],
    ],
    [
      42,
      [
        0.6011037519201636, 0.44829055899754167, 0.8524657934904099, 0.6697340414393693,
        0.17481389874592423, 0.5265925421845168,
      ],
    ],
  ];

  it('produces identical streams for identical seeds (two independent instances)', () => {
    const rngA = mulberry32(7);
    const rngB = mulberry32(7);
    const streamA = Array.from({ length: 256 }, () => rngA.next());
    const streamB = Array.from({ length: 256 }, () => rngB.next());
    assert.deepEqual(streamA, streamB);
  });

  it('matches the pinned golden stream prefixes for seeds 0, 1, and 42', () => {
    for (const [seed, expected] of GOLDEN_STREAMS) {
      const rng = mulberry32(seed);
      const actual = Array.from({ length: expected.length }, () => rng.next());
      assert.deepEqual(actual, expected, `seed ${seed} must match its golden prefix`);
    }
  });

  it('produces different streams for different seeds', () => {
    const rngA = mulberry32(1);
    const rngB = mulberry32(2);
    const streamA = Array.from({ length: 64 }, () => rngA.next());
    const streamB = Array.from({ length: 64 }, () => rngB.next());
    assert.notDeepEqual(streamA, streamB);
  });

  it('nextInt stays integral within [0, maxExclusive) and validates its bound', () => {
    const rng = mulberry32(3);
    for (let i = 0; i < 300; i += 1) {
      const value = rng.nextInt(5);
      assert.ok(Number.isInteger(value) && value >= 0 && value < 5, `bad draw: ${value}`);
    }
    assert.throws(() => rng.nextInt(0));
    assert.throws(() => rng.nextInt(1.5));
  });

  it('boolean draws only true/false', () => {
    const rng = mulberry32(17);
    for (let i = 0; i < 300; i += 1) {
      const value = rng.boolean();
      assert.ok(value === true || value === false);
    }
  });

  it('pick draws from the collection and rejects empty collections', () => {
    const rng = mulberry32(11);
    const items: readonly string[] = ['x', 'y', 'z'];
    for (let i = 0; i < 200; i += 1) {
      const picked = rng.pick(items);
      assert.ok(items.includes(picked), `pick returned ${picked}`);
    }
    assert.throws(() => rng.pick([]));
  });
});

describe('randomFormula generation', () => {
  const baseOptions = { maxDepth: 4, maxWidth: 3, maxVariables: 6 };

  it('produces identical formula streams for identical seeds', () => {
    const rngA = mulberry32(12);
    const rngB = mulberry32(12);
    const streamA = Array.from({ length: 24 }, () => randomFormula(rngA, baseOptions));
    const streamB = Array.from({ length: 24 }, () => randomFormula(rngB, baseOptions));
    assert.deepEqual(streamA, streamB);
  });

  it('produces different formula streams for different seeds', () => {
    const rngA = mulberry32(12);
    const rngB = mulberry32(13);
    const streamA = Array.from({ length: 24 }, () => randomFormula(rngA, baseOptions));
    const streamB = Array.from({ length: 24 }, () => randomFormula(rngB, baseOptions));
    assert.notDeepEqual(streamA, streamB);
  });

  it('exercises all five constructors over a fixed-seed stream', () => {
    const rng = mulberry32(42);
    const kindsSeen = new Set<string>();
    for (let i = 0; i < 50; i += 1) {
      for (const kind of randomFormula(rng, baseOptions).kinds) {
        kindsSeen.add(kind);
      }
    }
    assert.deepEqual([...kindsSeen].sort(), ['and', 'implies', 'not', 'or', 'xor']);
  });

  it('keeps formulas within the depth, width, and variable bounds', () => {
    const rng = mulberry32(42);
    for (let i = 0; i < 50; i += 1) {
      const { expr } = randomFormula(rng, baseOptions);
      const stats = astStats(expr);
      // implies/xor expand to at most three junction levels per choice.
      assert.ok(stats.depth <= 3 * baseOptions.maxDepth, `depth ${stats.depth}`);
      assert.ok(stats.maxFanIn <= baseOptions.maxWidth, `fan-in ${stats.maxFanIn}`);
      const variables = [...getVariables(expr)];
      assert.ok(
        variables.length <= baseOptions.maxVariables,
        `${variables.length} variables exceeds the cap`,
      );
      for (const variable of variables) {
        assert.ok(
          variable >= 'a' && variable <= 'f',
          `variable ${variable} outside the default pool`,
        );
      }
    }
  });

  it('honours an explicit variable pool', () => {
    const rng = mulberry32(5);
    const pool = ['p', 'q', 'r'];
    for (let i = 0; i < 20; i += 1) {
      const { expr } = randomFormula(rng, { maxDepth: 3, maxWidth: 3, variables: pool });
      for (const variable of getVariables(expr)) {
        assert.ok(pool.includes(variable), `variable ${variable} outside the supplied pool`);
      }
    }
  });

  it('validates its options', () => {
    const rng = mulberry32(1);
    assert.throws(() => randomFormula(rng, { maxDepth: 0, maxWidth: 3 }));
    assert.throws(() => randomFormula(rng, { maxDepth: 4, maxWidth: 1 }));
    assert.throws(() => randomFormula(rng, { maxDepth: 4, maxWidth: 3, variables: [] }));
    assert.throws(() => randomFormula(rng, { maxDepth: 4, maxWidth: 3, maxVariables: 0 }));
  });
});

describe('the naive reference enumerator', () => {
  const battery: ReadonlyArray<readonly [string, BooleanExpr, VariableAssignments[]]> = [
    ['and()', and(), [{}]],
    ['or()', or(), []],
    [
      "or('a','b')",
      or('a', 'b'),
      [
        { a: FALSE, b: TRUE },
        { a: TRUE, b: FALSE },
        { a: TRUE, b: TRUE },
      ],
    ],
    ["and('a','b')", and('a', 'b'), [{ a: TRUE, b: TRUE }]],
    ["not('b')", not('b'), [{ b: FALSE }]],
    [
      "implies('a','b')",
      implies('a', 'b'),
      [
        { a: FALSE, b: FALSE },
        { a: FALSE, b: TRUE },
        { a: TRUE, b: TRUE },
      ],
    ],
    [
      "xor('a','b')",
      xor('a', 'b'),
      [
        { a: FALSE, b: TRUE },
        { a: TRUE, b: FALSE },
      ],
    ],
  ];

  it('agrees with hand-computed model counts on the fixed battery', () => {
    const expectedCounts = new Map<string, number>([
      ['and()', 1],
      ['or()', 0],
      ["or('a','b')", 3],
      ["and('a','b')", 1],
      ["not('b')", 1],
      ["implies('a','b')", 3],
      ["xor('a','b')", 2],
    ]);
    for (const [label, expr] of battery) {
      assert.equal(referenceModels(expr).length, expectedCounts.get(label), `${label} model count`);
    }
  });

  it('returns exactly the hand-computed models for each battery entry', () => {
    for (const [, expr, expected] of battery) {
      assertModelListsEqual(referenceModels(expr), [...expected]);
    }
  });

  it('enumerates exactly 2^k total assignments, canonically ordered', () => {
    assert.deepStrictEqual(enumerateAssignments(['a', 'b']), [
      { a: FALSE, b: FALSE },
      { a: TRUE, b: FALSE },
      { a: FALSE, b: TRUE },
      { a: TRUE, b: TRUE },
    ]);
    // Input order does not matter: results are keyed by sorted name.
    assert.deepStrictEqual(enumerateAssignments(['b', 'a']), enumerateAssignments(['a', 'b']));
    assert.equal(enumerateAssignments(['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']).length, 256);
    // The k <= 8 hard limit.
    assert.throws(() => enumerateAssignments(['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i']));
  });

  for (const name of ARBITRARY_NAMES) {
    it(`preserves assignments and hand-computed truth tables for ${JSON.stringify(name)}`, () => {
      // Computed property literals define own data properties, even for __proto__.
      const falsy = { [name]: FALSE };
      const truthy = { [name]: TRUE };
      const assignments = enumerateAssignments([name]);
      assert.deepStrictEqual(assignments, [falsy, truthy]);
      for (const [index, assignment] of assignments.entries()) {
        assert.strictEqual(Object.getPrototypeOf(assignment), Object.prototype);
        assert.deepStrictEqual(Reflect.ownKeys(assignment), [name]);
        assert.deepStrictEqual(Object.getOwnPropertyDescriptor(assignment, name), {
          value: index === 0 ? FALSE : TRUE,
          enumerable: true,
          configurable: true,
          writable: true,
        });
      }
      assert.deepStrictEqual(referenceModels(and(name)), [truthy]);
      assert.deepStrictEqual(referenceModels(not(name)), [falsy]);
      assert.deepStrictEqual(referenceModels(or(name, not(name))), [falsy, truthy]);
      assert.deepStrictEqual(referenceModels(and(name, not(name))), []);
      assert.strictEqual(expressionValue(and(name), truthy), TRUE);
      assert.strictEqual(expressionValue(and(name), falsy), FALSE);
      assert.strictEqual(expressionValue(not(name), truthy), FALSE);
      assert.strictEqual(expressionValue(not(name), falsy), TRUE);
    });
  }

  it('rejects missing, inherited, and non-numeric reference variable reads', () => {
    for (const name of ARBITRARY_NAMES) {
      for (const assignment of [
        {},
        Object.create({ [name]: TRUE }),
        { [name]: true },
        { [name]: '0' },
        { [name]: Value.UNSET },
      ]) {
        assert.throws(
          () => expressionValue(and(name), assignment as VariableAssignments),
          /reference evaluation requires an own TRUE\/FALSE assignment/,
        );
      }
    }
  });

  it('classifies every total assignment exactly as the reference evaluator does', () => {
    const rng = mulberry32(21);
    for (let i = 0; i < 30; i += 1) {
      const { expr } = randomFormula(rng, { maxDepth: 3, maxWidth: 3, maxVariables: 5 });
      const variables = [...getVariables(expr)].sort();
      const models = referenceModels(expr);
      const modelKeys = new Set(models.map((model) => modelKey(model)));
      assert.equal(modelKeys.size, models.length);
      for (const assignment of enumerateAssignments(variables)) {
        const satisfies = expressionValue(expr, assignment) === Value.TRUE;
        assert.equal(
          modelKeys.has(modelKey(assignment)),
          satisfies,
          'enumerator classification must match the reference evaluator',
        );
      }
    }
  });

  it('every enumerated model satisfies the formula and satisfies shape checks', () => {
    // and() and or() exercise the degenerate empty-variable corners.
    assertModelShape({}, and());
    for (const [label, expr] of battery) {
      const models = referenceModels(expr);
      for (const model of models) {
        assert.equal(expressionValue(expr, model), Value.TRUE, `${label} model must satisfy`);
        assertModelShape(model, expr);
      }
    }
  });
});

describe('assumption-subset generation', () => {
  for (const name of ARBITRARY_NAMES) {
    it(`retains consistent and contradictory own assumptions for ${JSON.stringify(name)}`, () => {
      for (const required of [FALSE, TRUE]) {
        const expr = required === TRUE ? and(name) : not(name);
        const opposite = required === TRUE ? FALSE : TRUE;
        const rng = mulberry32(9);
        let emptyDraws = 0;
        let assignedDraws = 0;
        for (let draw = 0; draw < 32; draw += 1) {
          const partial = randomAssumptions(rng, expr, { kind: 'consistent' });
          assert.strictEqual(Object.getPrototypeOf(partial), Object.prototype);
          if (Object.keys(partial).length === 0) {
            assert.deepStrictEqual(partial, {});
            emptyDraws += 1;
          } else {
            assert.deepStrictEqual(partial, { [name]: required });
            assignedDraws += 1;
          }
          assert.deepStrictEqual(randomAssumptions(rng, expr, { kind: 'contradictory' }), {
            [name]: opposite,
          });
        }
        assert.ok(emptyDraws > 0 && assignedDraws > 0, 'exercise both empty and assigned subsets');

        // The irrelevant variable must be removed, never the required literal.
        assert.deepStrictEqual(
          randomAssumptions(mulberry32(5), and(expr, or('spare', not('spare'))), {
            kind: 'contradictory',
          }),
          { [name]: opposite },
        );
        // Falsifying an OR requires retaining BOTH negative assumptions.
        assert.deepStrictEqual(
          randomAssumptions(mulberry32(6), or(name, 'spare'), { kind: 'contradictory' }),
          { [name]: FALSE, spare: FALSE },
        );
      }
    });
  }

  it('produces consistent partials that extend to a model', () => {
    const rng = mulberry32(9);
    let checked = 0;
    for (let i = 0; i < 20; i += 1) {
      const { expr } = randomFormula(rng, { maxDepth: 3, maxWidth: 3, maxVariables: 4 });
      const models = referenceModels(expr);
      if (models.length === 0) {
        continue; // unsatisfiable formulas cannot yield consistent partials
      }
      const partial = randomAssumptions(mulberry32(i + 100), expr, { kind: 'consistent' });
      for (const variable of Object.keys(partial)) {
        assert.ok(
          partial[variable] === Value.TRUE || partial[variable] === Value.FALSE,
          `assigned values must be TRUE or FALSE (${variable})`,
        );
      }
      assert.ok(hasExtension(partial, models), 'consistent partial must be extendable to a model');
      checked += 1;
    }
    assert.ok(checked > 10, 'the fixed-seed battery must include satisfiable formulas');
  });

  it('produces contradictory partials that extend to no model', () => {
    const rng = mulberry32(9);
    let checked = 0;
    for (let i = 0; i < 20; i += 1) {
      const { expr } = randomFormula(rng, { maxDepth: 3, maxWidth: 3, maxVariables: 4 });
      const variables = [...getVariables(expr)].sort();
      const models = referenceModels(expr);
      if (models.length === 2 ** variables.length) {
        continue; // tautologies cannot yield contradictory partials
      }
      const partial = randomAssumptions(mulberry32(i + 200), expr, { kind: 'contradictory' });
      assert.ok(
        !hasExtension(partial, models),
        'contradictory partial must not be extendable to any model',
      );
      checked += 1;
    }
    assert.ok(checked > 10, 'the fixed-seed battery must include non-tautological formulas');
  });

  it('is deterministic under a fixed seed', () => {
    const expr = or(and('a', not('b')), xor('c', 'd'));
    const consistentA = randomAssumptions(mulberry32(5), expr, { kind: 'consistent' });
    const consistentB = randomAssumptions(mulberry32(5), expr, { kind: 'consistent' });
    assert.deepStrictEqual(consistentA, consistentB);
    const contradictoryA = randomAssumptions(mulberry32(6), expr, { kind: 'contradictory' });
    const contradictoryB = randomAssumptions(mulberry32(6), expr, { kind: 'contradictory' });
    assert.deepStrictEqual(contradictoryA, contradictoryB);
  });

  it('honours maxAssumptions for consistent partials', () => {
    const rng = mulberry32(8);
    const expr = and('a', 'b', 'c', 'd');
    const models = referenceModels(expr);
    for (let i = 0; i < 40; i += 1) {
      const partial = randomAssumptions(rng, expr, { kind: 'consistent', maxAssumptions: 2 });
      assert.ok(Object.keys(partial).length <= 2);
      assert.ok(hasExtension(partial, models));
    }
  });

  it('throws when no conclusive partial of the requested kind exists', () => {
    // or() is unsatisfiable: no consistent partial exists.
    assert.throws(() => randomAssumptions(mulberry32(1), or(), { kind: 'consistent' }));
    // and() is a tautology: no contradictory partial exists.
    assert.throws(() => randomAssumptions(mulberry32(1), and(), { kind: 'contradictory' }));
    // or('a', not('a')) is also a tautology.
    assert.throws(() =>
      randomAssumptions(mulberry32(1), or('a', not('a')), { kind: 'contradictory' }),
    );
  });

  it('handles degenerate zero- and one-variable formulas', () => {
    // and() is a tautology with one model: the empty assignment.
    assert.deepStrictEqual(randomAssumptions(mulberry32(1), and(), { kind: 'consistent' }), {});
    // or() is unsatisfiable: the empty partial assignment contradicts it.
    assert.deepStrictEqual(randomAssumptions(mulberry32(2), or(), { kind: 'contradictory' }), {});
    // not('b') has exactly one model; seed 3 happens to draw the empty
    // consistent partial and the {b: TRUE} contradiction (pinned values).
    assert.deepStrictEqual(randomAssumptions(mulberry32(3), not('b'), { kind: 'consistent' }), {});
    assert.deepStrictEqual(randomAssumptions(mulberry32(3), not('b'), { kind: 'contradictory' }), {
      b: Value.TRUE,
    });
  });
});

describe('model comparison utilities', () => {
  it('modelKey is a stable, order-insensitive key', () => {
    assert.strictEqual(modelKey({ b: TRUE, a: FALSE }), '[["a",0],["b",1]]');
    assert.strictEqual(modelKey({ a: FALSE, b: TRUE }), '[["a",0],["b",1]]');
    assert.strictEqual(modelKey({}), '[]');
  });

  it('modelKey unambiguously encodes arbitrary names instead of joining delimiters', () => {
    const models: VariableAssignments[] = [{ a: FALSE, b: TRUE }, { 'a=0,b': TRUE }];
    assert.notStrictEqual(modelKey(models[0]), modelKey(models[1]));
    assertModelListsEqual(models, [...models].reverse());
    for (const name of ARBITRARY_NAMES) {
      for (const value of [FALSE, TRUE]) {
        assert.deepStrictEqual(JSON.parse(modelKey({ [name]: value })), [[name, value]]);
      }
    }
  });

  it('modelsEqual ignores key order and distinguishes values', () => {
    assert.ok(modelsEqual({ a: TRUE, b: FALSE }, { b: FALSE, a: TRUE }));
    assert.ok(!modelsEqual({ a: TRUE, b: TRUE }, { a: TRUE, b: FALSE }));
    assert.ok(!modelsEqual({ a: TRUE, b: FALSE }, { a: TRUE }));
    assert.ok(!modelsEqual({ a: true } as unknown as VariableAssignments, { a: TRUE }));
    assert.ok(!modelsEqual(Object.assign(Object.create(null), { a: TRUE }), { a: TRUE }));
  });

  it('sortModels makes collections order-insensitive', () => {
    const models = [
      { a: TRUE, b: FALSE },
      { a: FALSE, b: TRUE },
    ];
    assert.deepStrictEqual(sortModels(models), [...models].reverse());
  });

  it('assertModelListsEqual passes on permutations and fails on differences', () => {
    assertModelListsEqual(
      [
        { a: TRUE, b: FALSE },
        { a: TRUE, b: TRUE },
      ],
      [
        { a: TRUE, b: TRUE },
        { a: TRUE, b: FALSE },
      ],
    );
    assert.throws(() => assertModelListsEqual([{ a: TRUE, b: FALSE }], [{ a: TRUE, b: TRUE }]));
  });

  it('assertModelListsEqual rejects coerced values, wrong keys, counts, and prototypes', () => {
    for (const [actual, expected] of [
      [{ a: true }, { a: TRUE }],
      [{ a: false }, { a: FALSE }],
      [{ a: '1' }, { a: TRUE }],
      [{}, { a: TRUE }],
      [{ a: TRUE, b: FALSE }, { a: TRUE }],
      [Object.assign(Object.create(null), { a: TRUE }), { a: TRUE }],
    ]) {
      assert.throws(
        () => assertModelListsEqual([actual as VariableAssignments], [expected]),
        assert.AssertionError,
      );
    }
    assert.throws(() => assertModelListsEqual([], [{ a: TRUE }]), assert.AssertionError);
    assert.throws(
      () => assertModelListsEqual([{ a: TRUE }, { a: TRUE }], [{ a: TRUE }]),
      assert.AssertionError,
    );
  });

  it('assertModelShape accepts numeric TRUE/FALSE models and rejects malformed ones', () => {
    assertModelShape({ a: TRUE, b: FALSE }, or('a', 'b'));
    assert.throws(() =>
      assertModelShape({ a: true, b: false } as unknown as VariableAssignments, or('a', 'b')),
    );
    assert.throws(() => assertModelShape({ a: TRUE, b: Value.UNSET }, or('a', 'b')));
    assert.throws(() => assertModelShape({ a: TRUE }, or('a', 'b')));
    assert.throws(() => assertModelShape({ a: TRUE, b: FALSE, c: TRUE }, or('a', 'b')));
  });

  it('assertModelShape checks exact own keys and the ordinary public model prototype', () => {
    assertModelShape({ ['__proto__']: TRUE }, and('__proto__'));
    assert.throws(() => assertModelShape({}, and('__proto__')), assert.AssertionError);
    for (const model of [
      Object.assign(Object.create({ a: TRUE }), { b: FALSE }),
      Object.assign(Object.create(null), { a: TRUE, b: FALSE }),
      Object.defineProperty({ a: TRUE, b: FALSE }, 'hidden', { value: TRUE }),
      { a: TRUE, b: FALSE, [Symbol('extra')]: TRUE },
    ]) {
      assert.throws(() => assertModelShape(model, or('a', 'b')), assert.AssertionError);
    }
  });
});
