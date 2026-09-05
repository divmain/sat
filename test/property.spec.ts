// Seeded cross-validation of the public solvers against the naive reference
// enumerator (Design § Testing and Benchmarking Strategy). The full harness
// (task-92a3): >= 300 seeded formulas over <= 8 named variables covering all
// five constructors, with
//   - the verdict triangle (getSolution sat ⟺ getAllSolutions nonempty ⟺
//     reference count > 0),
//   - exact model-count equality against the naive reference enumerator,
//   - per-model shape (key set / no-UNSET) and reference-validity checks with
//     duplicate detection,
//   - random assumption subsets per formula (both consistent and
//     contradictory): getSolution(f, { assumptions }) is null iff no
//     reference model extends the assumptions; every returned model extends
//     them; enumeration under assumptions matches the reference extension
//     count.
// Everything is seeded (mulberry32, fixed seeds) — the suite is
// deterministic across runs by construction.

import { describe, it } from 'node:test';
import assert from 'node:assert';
import { and, getAllSolutions, getSolution, implies, not, or, Value, xor } from '../src';
import { getVariables } from '../src/expr';
import type { BooleanExpr, VariableAssignments } from '../src';
import {
  assertModelListsEqual,
  assertModelShape,
  expressionValue,
  modelKey,
  mulberry32,
  randomAssumptions,
  randomFormula,
  referenceModels,
  sortModels,
} from './helpers';

// The fixed battery from the task-2 reference-enumerator harness
// (test/helpers.spec.ts): hand-computed model sets over the constructors,
// including the degenerate zero-variable corners.
const battery: ReadonlyArray<readonly [string, BooleanExpr]> = [
  ['and()', and()],
  ['or()', or()],
  ["or('a','b')", or('a', 'b')],
  ["and('a','b')", and('a', 'b')],
  ["not('b')", not('b')],
  ["implies('a','b')", implies('a', 'b')],
  ["xor('a','b')", xor('a', 'b')],
];

// ≥ 300 seeded formulas (Design: "≥ 300–500 formulas"), over ≤ 8 named
// variables so the naive reference enumerator's 2^k bound stays at 256 max.
const SEED_COUNT = 320;
const FORMULA_OPTIONS = { maxDepth: 3, maxWidth: 4, maxVariables: 8 };

// Per-formula assumption draws: 2 consistent + 2 contradictory subsets,
// drawn from PRNG instances seeded deterministically per (formula, draw).
const ASSUMPTIONS_PER_FORMULA = 4;
const ASSUMPTION_SEED_BASE = 100_000;
const MAX_CONSISTENT_ASSUMPTIONS = 3;

// True when `partial` is a subset of `model` (every assigned variable of the
// partial matches the model's value).
function modelExtends(model: VariableAssignments, partial: VariableAssignments): boolean {
  return Object.keys(partial).every((key) => model[key] === partial[key]);
}

// The no-assumption cross-check battery for one formula: verdict triangle,
// exact counts against the reference, duplicate detection, per-model shape,
// and reference validity of every returned model.
const assertEnumerationAgainstReference: (label: string, expr: BooleanExpr) => void = (
  label,
  expr,
) => {
  const actual = getAllSolutions(expr);
  const reference = referenceModels(expr);

  // Verdict triangle: getSolution sat ⟺ getAllSolutions nonempty ⟺ the
  // reference enumerates at least one model.
  assert.strictEqual(
    getSolution(expr) !== null,
    reference.length > 0,
    `${label} getSolution verdict`,
  );
  assert.strictEqual(actual.length > 0, reference.length > 0, `${label} enumeration verdict`);

  // Exact model-count equality against the naive reference enumerator.
  assert.strictEqual(actual.length, reference.length, `${label} model count`);
  // No duplicates (blocking clauses must exclude every already-returned model).
  const keys = actual.map(modelKey);
  assert.strictEqual(new Set(keys).size, keys.length, `${label} duplicate models`);
  // Per-model shape (key set exactly the named variables, no UNSET) and
  // reference validity.
  for (const model of actual) {
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE, `${label} returned model`);
  }
};

// The assumption cross-check for one partial assignment: `getSolution` under
// the assumptions is null iff no reference model extends them; any returned
// model extends them and satisfies the formula; enumeration under the
// assumptions matches the reference extension count exactly.
const assertAssumptionsAgainstReference: (
  label: string,
  expr: BooleanExpr,
  partial: VariableAssignments,
  reference: VariableAssignments[],
) => void = (label, expr, partial, reference) => {
  const extendingReference = reference.filter((model) => modelExtends(model, partial));
  const model = getSolution(expr, { assumptions: partial });

  assert.strictEqual(model !== null, extendingReference.length > 0, `${label} assumption verdict`);
  if (model !== null) {
    assert.ok(modelExtends(model, partial), `${label} returned model must extend the assumptions`);
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE, `${label} assumed model`);
  }

  const enumerated = getAllSolutions(expr, { assumptions: partial });
  assert.strictEqual(
    enumerated.length,
    extendingReference.length,
    `${label} assumed enumeration count`,
  );
  assert.deepEqual(
    sortModels(enumerated),
    sortModels(extendingReference),
    `${label} assumed enumeration set`,
  );
};

describe('getAllSolutions cross-validation against the reference enumerator', () => {
  describe('fixed battery', () => {
    it('returns exactly the hand-computed model sets, order-insensitively', () => {
      const expectedByLabel = new Map<string, Record<string, Value>[]>([
        ['and()', [{}]],
        ['or()', []],
        [
          "or('a','b')",
          [
            { a: Value.FALSE, b: Value.TRUE },
            { a: Value.TRUE, b: Value.FALSE },
            { a: Value.TRUE, b: Value.TRUE },
          ],
        ],
        ["and('a','b')", [{ a: Value.TRUE, b: Value.TRUE }]],
        ["not('b')", [{ b: Value.FALSE }]],
        [
          "implies('a','b')",
          [
            { a: Value.FALSE, b: Value.FALSE },
            { a: Value.FALSE, b: Value.TRUE },
            { a: Value.TRUE, b: Value.TRUE },
          ],
        ],
        [
          "xor('a','b')",
          [
            { a: Value.FALSE, b: Value.TRUE },
            { a: Value.TRUE, b: Value.FALSE },
          ],
        ],
      ]);
      for (const [label, expr] of battery) {
        const expected = expectedByLabel.get(label);
        assert.ok(expected !== undefined, `missing expectation for ${label}`);
        assertModelListsEqual(getAllSolutions(expr), expected);
      }
    });

    it('passes the count-equality and shape checks on every battery entry', () => {
      for (const [label, expr] of battery) {
        assertEnumerationAgainstReference(label, expr);
      }
    });
  });

  describe('seeded random formulas (>= 300)', () => {
    it('matches the reference verdict triangle and exact counts on every seeded formula', () => {
      const kindsSeen = new Set<string>();
      for (let seed = 0; seed < SEED_COUNT; seed += 1) {
        const rng = mulberry32(seed);
        const { expr, kinds } = randomFormula(rng, FORMULA_OPTIONS);
        for (const kind of kinds) {
          kindsSeen.add(kind);
        }
        assertEnumerationAgainstReference(`seed ${seed}`, expr);
      }
      // the fixed-seed stream must exercise all five constructors
      assert.deepEqual([...kindsSeen].sort(), ['and', 'implies', 'not', 'or', 'xor']);
    });

    it('draws random assumption subsets per formula — consistent ones cross-checked', () => {
      for (let seed = 0; seed < SEED_COUNT; seed += 1) {
        const rng = mulberry32(seed);
        const { expr } = randomFormula(rng, FORMULA_OPTIONS);
        const reference = referenceModels(expr);
        if (reference.length === 0) {
          continue; // unsatisfiable formulas admit no consistent partial
        }
        for (let draw = 0; draw < ASSUMPTIONS_PER_FORMULA / 2; draw += 1) {
          const partial = randomAssumptions(
            mulberry32(ASSUMPTION_SEED_BASE + seed * ASSUMPTIONS_PER_FORMULA + draw),
            expr,
            {
              kind: 'consistent',
              maxAssumptions: MAX_CONSISTENT_ASSUMPTIONS,
            },
          );
          assertAssumptionsAgainstReference(`seed ${seed} draw ${draw}`, expr, partial, reference);
        }
      }
    });

    it('draws random assumption subsets per formula — contradictory ones cross-checked', () => {
      for (let seed = 0; seed < SEED_COUNT; seed += 1) {
        const rng = mulberry32(seed);
        const { expr } = randomFormula(rng, FORMULA_OPTIONS);
        const reference = referenceModels(expr);
        const variableCount = getVariables(expr).size;
        if (reference.length === 2 ** variableCount) {
          continue; // tautologies admit no contradictory partial
        }
        for (let draw = ASSUMPTIONS_PER_FORMULA / 2; draw < ASSUMPTIONS_PER_FORMULA; draw += 1) {
          const partial = randomAssumptions(
            mulberry32(ASSUMPTION_SEED_BASE + seed * ASSUMPTIONS_PER_FORMULA + draw),
            expr,
            {
              kind: 'contradictory',
            },
          );
          assertAssumptionsAgainstReference(`seed ${seed} draw ${draw}`, expr, partial, reference);
        }
      }
    });

    it('is deterministic under a fixed seed (same formula, model set, and subsets)', () => {
      for (let seed = 0; seed < 8; seed += 1) {
        const rngA = mulberry32(seed);
        const rngB = mulberry32(seed);
        const formulaA = randomFormula(rngA, FORMULA_OPTIONS).expr;
        const formulaB = randomFormula(rngB, FORMULA_OPTIONS).expr;
        assert.deepEqual(
          sortModels(getAllSolutions(formulaA)),
          sortModels(getAllSolutions(formulaB)),
        );

        const reference = referenceModels(formulaA);
        if (reference.length > 0) {
          const consistentA = randomAssumptions(
            mulberry32(ASSUMPTION_SEED_BASE + seed * ASSUMPTIONS_PER_FORMULA),
            formulaA,
            {
              kind: 'consistent',
              maxAssumptions: MAX_CONSISTENT_ASSUMPTIONS,
            },
          );
          const consistentB = randomAssumptions(
            mulberry32(ASSUMPTION_SEED_BASE + seed * ASSUMPTIONS_PER_FORMULA),
            formulaB,
            {
              kind: 'consistent',
              maxAssumptions: MAX_CONSISTENT_ASSUMPTIONS,
            },
          );
          assert.deepEqual(consistentA, consistentB, `seed ${seed} consistent subset`);
        }
      }
    });
  });
});
