// Seeded cross-validation of both solver variants against the naive reference
// enumerator (Design § Testing and Benchmarking Strategy). The full harness
// (task-884f): 512 seeds per variable pool (original a-h plus arbitrary string
// names), over <= 8 named variables covering all five constructors, with
//   - the verdict triangle (getSolution sat ⟺ getAllSolutions nonempty ⟺
//     reference count > 0),
//   - verdict stability over three fresh solves of the same expression and
//     assumption subset, with every returned single model reference-checked,
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
// Each pool runs through the public getSolution/getAllSolutions pair and through
// threshold-1 Solvers: PLE-enabled single-shot solving and PLE-disabled persistent
// enumeration using the SAME production Solver.enumerateModels loop.

import { describe, it } from 'node:test';
import assert from 'node:assert';
import { and, getAllSolutions, getSolution, implies, not, or, Value, xor } from '../src';
import { compile } from '../src/compile';
import { getVariables } from '../src/expr';
import { Solver } from '../src/solver';
import type { BooleanExpr, SolveOptions, VariableAssignments } from '../src';
import {
  assertModelListsEqual,
  assertModelShape,
  expressionValue,
  modelKey,
  mulberry32,
  randomAssumptions,
  randomFormula,
  referenceModels,
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

// ≥ 500 seeded formulas (the Phase-2 gate), over ≤ 8 named
// variables so the naive reference enumerator's 2^k bound stays at 256 max.
const SEED_COUNT = 512;
const REPEATED_SOLVES = 3;
const FORMULA_OPTIONS = { maxDepth: 3, maxWidth: 4, maxVariables: 8 };
const VARIABLE_POOLS = [
  { label: 'original a-h', variables: ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] },
  {
    label: 'arbitrary string names',
    variables: [
      '__proto__',
      'constructor',
      'toString',
      'hasOwnProperty',
      '',
      'a=0,b',
      '0',
      'quote"\\\n\u03bb',
    ],
  },
];

// Per-formula assumption draws: 2 consistent + 2 contradictory subsets,
// drawn from PRNG instances seeded deterministically per (formula, draw).
const ASSUMPTIONS_PER_FORMULA = 4;
const ASSUMPTION_SEED_BASE = 100_000;
const MAX_CONSISTENT_ASSUMPTIONS = 3;

interface ReductionCounts {
  reductionCalls: number;
  deletedClauses: number;
}

interface HarnessCounts {
  formulas: number;
  assumptions: number;
  reductions: Record<'singleShot' | 'enumeration' | 'enumerationAfterModel', ReductionCounts>;
}

function createSolvers(useReduction: boolean): {
  solve: typeof getSolution;
  enumerate: typeof getAllSolutions;
  counts: HarnessCounts;
} {
  const counts: HarnessCounts = {
    formulas: 0,
    assumptions: 0,
    reductions: {
      singleShot: { reductionCalls: 0, deletedClauses: 0 },
      enumeration: { reductionCalls: 0, deletedClauses: 0 },
      enumerationAfterModel: { reductionCalls: 0, deletedClauses: 0 },
    },
  };
  if (!useReduction) {
    return { solve: getSolution, enumerate: getAllSolutions, counts };
  }

  // Observe only automatic reductions on genuine learned clauses. Never invoke
  // reduction manually, inject clauses, or change the production deletion policy.
  class ObservedSolver extends Solver {
    lastLearnedTotal = 0;
    solveCalls = 0;
    readonly reductions: ReductionCounts;

    constructor(expr: BooleanExpr, options: SolveOptions | undefined, enablePle: boolean) {
      if (options?.stats !== undefined) {
        Object.assign(options.stats, {
          decisions: 0,
          propagations: 0,
          conflicts: 0,
          restarts: 0,
          learnedClauses: 0,
          learnedClausesCurrent: 0,
        });
      }
      super(compile(expr), {
        assumptions: options?.assumptions,
        variablePriority: options?.variablePriority,
        stats: options?.stats,
        enablePle,
        learnedClauseReductionThreshold: 1,
      });
      this.reductions = enablePle ? counts.reductions.singleShot : counts.reductions.enumeration;
    }

    override solve(): boolean {
      this.solveCalls += 1;
      const totalBefore = this.stats.learnedClauses;
      const sat = super.solve();
      this.checkInvariants();
      assert.ok(this.stats.learnedClauses >= totalBefore, 'total across solve calls');
      assert.ok(this.stats.learnedClauses >= this.lastLearnedTotal, 'total after solving');
      assert.strictEqual(
        this.stats.learnedClausesCurrent,
        this.clauses.filter((clause) => clause.learned).length,
        'live count after every solve on this instance',
      );
      return sat;
    }

    override reduceLearnedClauses(): void {
      this.checkInvariants();
      const database = this.clauses;
      const before = [...database];
      const learnedBefore = before.filter((clause) => clause.learned);
      const metadata = before.map((clause) => ({ ...clause, lits: [...clause.lits] }));
      const reasons = [...this.reason];
      const protectedClauses = before.filter(
        (clause) => !clause.learned || clause.lbd <= 2 || reasons.includes(clause),
      );
      const totalBefore = this.stats.learnedClauses;
      assert.ok(learnedBefore.length > 0, 'automatic reduction must see live learned clauses');
      assert.strictEqual(
        totalBefore,
        this.lastLearnedTotal + 1,
        'threshold 1 reduces after each new learned admission',
      );
      assert.ok(this.stats.conflicts >= totalBefore, 'learned admissions follow real conflicts');
      assert.strictEqual(
        this.stats.learnedClausesCurrent,
        learnedBefore.length,
        'live count before',
      );

      super.reduceLearnedClauses();
      this.checkInvariants();

      const after = new Set(this.clauses);
      const deleted = before.filter((clause) => !after.has(clause));
      const learnedAfter = this.clauses.filter((clause) => clause.learned);
      assert.strictEqual(this.clauses, database, 'stable database identity');
      assert.strictEqual(
        after.size,
        before.length - deleted.length,
        'reduction only removes clauses',
      );
      assert.strictEqual(learnedAfter.length, learnedBefore.length - deleted.length);
      assert.ok(deleted.length <= Math.floor(learnedBefore.length / 2), 'at most the worse half');
      for (const clause of protectedClauses) {
        assert.ok(after.has(clause), 'originals, blockers, all reasons and LBD <= 2 survive');
      }
      for (const [index, reason] of reasons.entries()) {
        assert.strictEqual(this.reason[index], reason, 'every active reason keeps its identity');
      }
      for (const [index, clause] of before.entries()) {
        assert.deepStrictEqual(clause, metadata[index], 'reduction does not rewrite clauses');
      }
      for (const clause of deleted) {
        assert.strictEqual(clause.learned, true, 'only genuine learned clauses are deleted');
        assert.ok(clause.lbd > 2 && !reasons.includes(clause), 'deleted clauses were unprotected');
      }
      assert.strictEqual(this.stats.learnedClausesCurrent, learnedAfter.length, 'live count after');
      assert.strictEqual(this.stats.learnedClauses, totalBefore, 'reduction preserves total');
      this.lastLearnedTotal = totalBefore;
      this.reductions.reductionCalls += 1;
      this.reductions.deletedClauses += deleted.length;
      if (this.reductions === counts.reductions.enumeration && this.solveCalls > 1) {
        counts.reductions.enumerationAfterModel.reductionCalls += 1;
        counts.reductions.enumerationAfterModel.deletedClauses += deleted.length;
      }
    }
  }

  return {
    solve: (expr, options) => {
      const solver = new ObservedSolver(expr, options, true);
      return solver.solve() ? solver.model() : null;
    },
    enumerate: (expr, options) => {
      const solver = new ObservedSolver(expr, options, false);
      const originals = [...solver.clauses];
      const models = solver.enumerateModels();
      assert.strictEqual(
        solver.solveCalls,
        models.length + 1,
        'one instance through terminal UNSAT',
      );
      const permanent = new Set(solver.clauses.filter((clause) => !clause.learned));
      assert.strictEqual(permanent.size, originals.length + models.length, 'one blocker per model');
      for (const clause of originals) {
        assert.ok(permanent.has(clause), 'original clauses remain permanent through enumeration');
      }
      return models;
    },
    counts,
  };
}

// True when `partial` is a subset of `model` (every assigned variable of the
// partial matches the model's value). UNSET is ignored per the public contract.
function modelExtends(model: VariableAssignments, partial: VariableAssignments): boolean {
  return Object.entries(partial).every(
    ([key, value]) => Object.hasOwn(model, key) && (value === Value.UNSET || model[key] === value),
  );
}

// Validate supplied results without calling a solver. Both enumeration paths
// use this oracle, and the negative tests below exercise it with invalid models.
function assertEnumeratedModels(
  label: string,
  expr: BooleanExpr,
  actual: VariableAssignments[],
  expected: VariableAssignments[],
  assumptions: VariableAssignments = {},
): void {
  assert.strictEqual(actual.length, expected.length, `${label} model count`);
  for (const [index, model] of actual.entries()) {
    assertModelShape(model, expr);
    assert.strictEqual(
      expressionValue(expr, model),
      Value.TRUE,
      `${label} model ${index} must satisfy the reference formula`,
    );
    // Check actual results directly, independently of the reference filtering predicate.
    for (const [name, value] of Object.entries(assumptions)) {
      assert.ok(
        Object.hasOwn(model, name),
        `${label} model ${index} must own ${JSON.stringify(name)}`,
      );
      if (value !== Value.UNSET) {
        assert.strictEqual(
          model[name],
          value,
          `${label} model ${index} must extend assumption ${JSON.stringify(name)}`,
        );
      }
    }
  }
  const keys = actual.map(modelKey);
  assert.strictEqual(new Set(keys).size, keys.length, `${label} duplicate models`);
  assertModelListsEqual(actual, expected);
}

// Repeat the SAME input objects, not new random draws. The expected verdict
// comes from the independent reference before any solver call; agreeing with
// an earlier run alone would let a consistently wrong answer pass.
function assertStableSolution(
  solve: typeof getSolution,
  label: string,
  expr: BooleanExpr,
  expectedSat: boolean,
  assumptions: VariableAssignments = {},
): VariableAssignments | null {
  let firstVerdict: boolean | undefined;
  let model: VariableAssignments | null = null;
  for (let run = 0; run < REPEATED_SOLVES; run += 1) {
    model = solve(expr, { assumptions });
    const sat = model !== null;
    assert.strictEqual(sat, expectedSat, `${label} solve ${run} reference verdict`);
    if (run === 0) {
      firstVerdict = sat;
    } else {
      assert.strictEqual(sat, firstVerdict, `${label} solve ${run} repeated verdict`);
    }
    if (model !== null) {
      assertModelShape(model, expr);
      assert.strictEqual(expressionValue(expr, model), Value.TRUE, `${label} solve ${run} model`);
      assert.ok(
        modelExtends(model, assumptions),
        `${label} solve ${run} model must extend the assumptions`,
      );
    }
  }
  return model;
}

// The no-assumption cross-check battery for one formula: verdict triangle,
// exact counts against the reference, duplicate detection, per-model shape,
// and reference validity of every returned model.
const assertEnumerationAgainstReference: (
  solve: typeof getSolution,
  enumerate: typeof getAllSolutions,
  label: string,
  expr: BooleanExpr,
  counts?: HarnessCounts,
) => void = (solve, enumerate, label, expr, counts) => {
  const reference = referenceModels(expr);
  assertStableSolution(solve, label, expr, reference.length > 0);
  const actual = enumerate(expr);

  // Verdict triangle: getSolution sat ⟺ getAllSolutions nonempty ⟺ the
  // reference enumerates at least one model.
  assert.strictEqual(actual.length > 0, reference.length > 0, `${label} enumeration verdict`);

  assertEnumeratedModels(label, expr, actual, reference);
  if (counts !== undefined) {
    counts.formulas += 1;
  }
};

// The assumption cross-check for one partial assignment: `getSolution` under
// the assumptions is null iff no reference model extends them; any returned
// model extends them and satisfies the formula; enumeration under the
// assumptions matches the reference extension count exactly.
const assertAssumptionsAgainstReference: (
  solve: typeof getSolution,
  enumerate: typeof getAllSolutions,
  label: string,
  expr: BooleanExpr,
  partial: VariableAssignments,
  reference: VariableAssignments[],
  counts?: HarnessCounts,
) => void = (solve, enumerate, label, expr, partial, reference, counts) => {
  const extendingReference = reference.filter((model) => modelExtends(model, partial));
  assertStableSolution(solve, label, expr, extendingReference.length > 0, partial);

  const enumerated = enumerate(expr, { assumptions: partial });
  assertEnumeratedModels(label, expr, enumerated, extendingReference, partial);
  if (counts !== undefined) {
    counts.assumptions += 1;
  }
};

describe('enumeration contract oracle', () => {
  const expr = or('a', 'b');
  const assumptions = { a: Value.TRUE };
  // Hand-computed, not obtained from either production solver or referenceModels.
  const expected: VariableAssignments[] = [
    { a: Value.TRUE, b: Value.FALSE },
    { a: Value.TRUE, b: Value.TRUE },
  ];

  it('accepts numeric models in either order and ignores UNSET assumptions', () => {
    assertEnumeratedModels('valid', expr, [...expected].reverse(), expected, assumptions);
    assertEnumeratedModels('UNSET', not('a'), [{ a: Value.FALSE }], [{ a: Value.FALSE }], {
      a: Value.UNSET,
    });
  });

  it('reference extension filtering requires strict own values for arbitrary names', () => {
    for (const name of VARIABLE_POOLS[1].variables) {
      const partial = { [name]: Value.TRUE };
      const booleanValue = { [name]: true } as unknown as VariableAssignments;
      assert.strictEqual(modelExtends(partial, partial), true);
      assert.strictEqual(modelExtends({ [name]: Value.FALSE }, partial), false);
      assert.strictEqual(modelExtends({}, partial), false);
      assert.strictEqual(modelExtends(Object.create(partial), partial), false);
      assert.strictEqual(modelExtends(booleanValue, partial), false);
      assert.strictEqual(modelExtends(partial, booleanValue), false);
      assert.strictEqual(modelExtends(partial, { [name]: Value.UNSET }), true);
    }
  });

  const invalidModels: ReadonlyArray<readonly [string, unknown, RegExp]> = [
    ['boolean TRUE', { a: true, b: Value.FALSE }, /every model value must be TRUE or FALSE/],
    ['boolean FALSE', { a: Value.TRUE, b: false }, /every model value must be TRUE or FALSE/],
    ['UNSET', { a: Value.TRUE, b: Value.UNSET }, /every model value must be TRUE or FALSE/],
    ['a missing key', { a: Value.TRUE }, /model key set must equal/],
    [
      'an extra key',
      { a: Value.TRUE, b: Value.FALSE, extra: Value.TRUE },
      /model key set must equal/,
    ],
    [
      'a falsifying model',
      { a: Value.FALSE, b: Value.FALSE },
      /must satisfy the reference formula/,
    ],
    ['an assumption violation', { a: Value.FALSE, b: Value.TRUE }, /must extend assumption "a"/],
  ];
  for (const [label, invalid, message] of invalidModels) {
    it(`rejects ${label} at every enumeration position`, () => {
      for (let index = 0; index < expected.length; index += 1) {
        const actual = [...expected];
        actual[index] = invalid as VariableAssignments;
        assert.throws(() => assertEnumeratedModels(label, expr, actual, expected, assumptions), {
          name: 'AssertionError',
          message,
        });
      }
    });
  }

  it('rejects incorrect counts and duplicate models', () => {
    assert.throws(
      () => assertEnumeratedModels('count', expr, expected.slice(1), expected, assumptions),
      /model count/,
    );
    assert.throws(
      () =>
        assertEnumeratedModels(
          'duplicates',
          expr,
          [expected[0], expected[0]],
          expected,
          assumptions,
        ),
      /duplicate models/,
    );
  });
});

for (const useReduction of [false, true]) {
  const variant = useReduction ? 'Solver (reduction threshold 1)' : 'getSolution/getAllSolutions';
  describe(`${variant} cross-validation against the reference enumerator`, () => {
    describe('fixed battery', () => {
      const { solve, enumerate } = createSolvers(useReduction);
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
          assertEnumeratedModels(label, expr, enumerate(expr), expected);
        }
      });

      it('passes the count-equality and shape checks on every battery entry', () => {
        for (const [label, expr] of battery) {
          assertEnumerationAgainstReference(solve, enumerate, label, expr);
        }
      });

      for (const name of VARIABLE_POOLS[1].variables) {
        it(`preserves the public model and assumption contracts for ${JSON.stringify(
          name,
        )}`, () => {
          for (const required of [Value.FALSE, Value.TRUE]) {
            const expr = required === Value.TRUE ? and(name) : not(name);
            const expected = { [name]: required };
            for (const assumptions of [{}, expected, { [name]: Value.UNSET }]) {
              const model = assertStableSolution(solve, name, expr, true, assumptions);
              assert.deepStrictEqual(model, expected);
              assertModelShape(model, expr);
              assertEnumeratedModels(
                name,
                expr,
                enumerate(expr, { assumptions }),
                [expected],
                assumptions,
              );
            }
            const assumptions = { [name]: required === Value.TRUE ? Value.FALSE : Value.TRUE };
            assert.strictEqual(assertStableSolution(solve, name, expr, false, assumptions), null);
            assertEnumeratedModels(name, expr, enumerate(expr, { assumptions }), [], assumptions);
          }
          const contradiction = and(name, not(name));
          assert.strictEqual(assertStableSolution(solve, name, contradiction, false), null);
          assertEnumeratedModels(name, contradiction, enumerate(contradiction), []);
        });
      }
    });

    for (const { label, variables } of VARIABLE_POOLS) {
      const options = { ...FORMULA_OPTIONS, variables };
      const { solve, enumerate, counts } = createSolvers(useReduction);
      describe(`seeded random formulas (${label}; 512; >= 500)`, () => {
        it('matches the reference triangle, exact counts, and repeated verdicts on every formula', (context) => {
          const kindsSeen = new Set<string>();
          const formulasSeen = new Set<string>();
          const variablesSeen = new Set<string>();
          for (let seed = 0; seed < SEED_COUNT; seed += 1) {
            const rng = mulberry32(seed);
            const { expr, kinds } = randomFormula(rng, options);
            formulasSeen.add(JSON.stringify(expr));
            for (const name of getVariables(expr)) {
              variablesSeen.add(name);
            }
            for (const kind of kinds) {
              kindsSeen.add(kind);
            }
            assertEnumerationAgainstReference(
              solve,
              enumerate,
              `${label} seed ${seed}`,
              expr,
              counts,
            );
          }
          // Pin completed calls in the test that executes them, rather than a
          // suite-wide hook that would fail intentionally filtered test runs.
          // Both pools require 512 formulas and 988+924 samples EACH: per
          // variant the full suite still enforces 1024 formulas / 3824 samples.
          assert.strictEqual(counts.formulas, SEED_COUNT, `${label} processed formula count`);
          if (useReduction) {
            for (const [path, reductions] of Object.entries(counts.reductions)) {
              assert.ok(
                reductions.reductionCalls > 0,
                `${label} ${path} must exercise automatic reduction`,
              );
              assert.ok(
                reductions.deletedClauses > 0,
                `${label} ${path} must exercise actual clause deletion`,
              );
              context.diagnostic(
                `${path}: ${reductions.reductionCalls} automatic reductions; ${reductions.deletedClauses} actual deletions`,
              );
            }
          }
          // the fixed-seed stream must exercise all five constructors
          assert.deepStrictEqual([...kindsSeen].sort(), ['and', 'implies', 'not', 'or', 'xor']);
          assert.deepStrictEqual([...variablesSeen].sort(), [...variables].sort());
          // Count structurally distinct formulas too, not just seeded draws.
          assert.ok(
            formulasSeen.size >= 500,
            'at least 500 distinct formula ASTs are cross-checked',
          );
          context.diagnostic(
            `${counts.formulas} formulas; ${formulasSeen.size} distinct ASTs; ${kindsSeen.size} constructors; ${variablesSeen.size} variable names`,
          );
        });

        it('draws random assumption subsets per formula - consistent ones cross-checked', (context) => {
          const before = counts.assumptions;
          const assumedVariables = new Set<string>();
          for (let seed = 0; seed < SEED_COUNT; seed += 1) {
            const rng = mulberry32(seed);
            const { expr } = randomFormula(rng, options);
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
              assert.ok(
                reference.some((model) => modelExtends(model, partial)),
                'consistent subset',
              );
              for (const name of Object.keys(partial)) {
                assumedVariables.add(name);
              }
              assertAssumptionsAgainstReference(
                solve,
                enumerate,
                `${label} seed ${seed} draw ${draw}`,
                expr,
                partial,
                reference,
                counts,
              );
            }
          }
          assert.strictEqual(counts.assumptions - before, 988, 'all consistent assumption draws');
          assert.deepStrictEqual([...assumedVariables].sort(), [...variables].sort());
          context.diagnostic(`${counts.assumptions - before} consistent assumption samples`);
        });

        it('draws random assumption subsets per formula - contradictory ones cross-checked', (context) => {
          const before = counts.assumptions;
          const assumedVariables = new Set<string>();
          for (let seed = 0; seed < SEED_COUNT; seed += 1) {
            const rng = mulberry32(seed);
            const { expr } = randomFormula(rng, options);
            const reference = referenceModels(expr);
            const variableCount = getVariables(expr).size;
            if (reference.length === 2 ** variableCount) {
              continue; // tautologies admit no contradictory partial
            }
            for (
              let draw = ASSUMPTIONS_PER_FORMULA / 2;
              draw < ASSUMPTIONS_PER_FORMULA;
              draw += 1
            ) {
              const partial = randomAssumptions(
                mulberry32(ASSUMPTION_SEED_BASE + seed * ASSUMPTIONS_PER_FORMULA + draw),
                expr,
                {
                  kind: 'contradictory',
                },
              );
              assert.ok(
                reference.every((model) => !modelExtends(model, partial)),
                'contradictory subset',
              );
              for (const name of Object.keys(partial)) {
                assumedVariables.add(name);
              }
              assertAssumptionsAgainstReference(
                solve,
                enumerate,
                `${label} seed ${seed} draw ${draw}`,
                expr,
                partial,
                reference,
                counts,
              );
            }
          }
          assert.strictEqual(
            counts.assumptions - before,
            924,
            'all contradictory assumption draws',
          );
          assert.deepStrictEqual([...assumedVariables].sort(), [...variables].sort());
          context.diagnostic(`${counts.assumptions - before} contradictory assumption samples`);
        });

        it('is deterministic under a fixed seed (same formula, model set, and subsets)', (context) => {
          for (let seed = 0; seed < 8; seed += 1) {
            const rngA = mulberry32(seed);
            const rngB = mulberry32(seed);
            const formulaA = randomFormula(rngA, options).expr;
            const formulaB = randomFormula(rngB, options).expr;
            assert.deepStrictEqual(formulaA, formulaB);

            const reference = referenceModels(formulaA);
            const modelsA = enumerate(formulaA);
            const modelsB = enumerate(formulaB);
            assertEnumeratedModels(`${label} seed ${seed} A`, formulaA, modelsA, reference);
            assertEnumeratedModels(`${label} seed ${seed} B`, formulaB, modelsB, reference);
            assertModelListsEqual(modelsA, modelsB);

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
              assert.deepStrictEqual(
                consistentA,
                consistentB,
                `${label} seed ${seed} consistent subset`,
              );
            }
          }
          context.diagnostic(
            `${variant}; ${label}: ${counts.formulas} formulas; ${
              counts.assumptions
            } assumption samples; ${
              useReduction
                ? Object.entries(counts.reductions)
                    .map(
                      ([path, reductions]) =>
                        `${path}: ${reductions.reductionCalls} automatic reductions; ${reductions.deletedClauses} actual deletions`,
                    )
                    .join('; ')
                : 'public reductions not instrumented'
            }`,
          );
        });
      });
    }
  });
}
