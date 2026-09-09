import assert from 'node:assert';
import { describe, it } from 'node:test';
import { createSolver, Value } from '../src/index.js';
import type { BooleanExpr, SatSolver, VariableAssignments } from '../src/index.js';
import { compile } from '../src/compile.js';
import { getVariables } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import { mulberry32, randomAssumptions, randomFormula, referenceModels } from './helpers.js';
import { assertResult, assertRoot, counters, internals } from './incremental-helpers.js';

const POOLS = [
  { label: 'a-h', names: ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'] },
  {
    label: 'arbitrary own string names',
    names: [
      '__proto__',
      'constructor',
      'toString',
      'hasOwnProperty',
      '',
      'a=0,b',
      '0',
      'quote"\\\nλ',
    ],
  },
];
const SEEDS_PER_POOL = 128;
const CALLS_PER_FORMULA = 8;
const WORK_KEYS = ['decisions', 'propagations', 'conflicts', 'restarts', 'learnedClauses'] as const;

interface Variant {
  label: string;
  knobs?: {
    restartPolicy: 'luby';
    restartBaseConflicts: number;
    learnedClauseReductionThreshold: number;
  };
}

const VARIANTS: Variant[] = [
  { label: 'public createSolver defaults' },
  {
    label: 'internal luby base1 / reduction1',
    knobs: { restartPolicy: 'luby', restartBaseConflicts: 1, learnedClauseReductionThreshold: 1 },
  },
  {
    label: 'internal luby base2 / reduction3',
    knobs: { restartPolicy: 'luby', restartBaseConflicts: 2, learnedClauseReductionThreshold: 3 },
  },
];

// Only observe automatic reductions on the production boundary/search. These
// internal knobs are NEVER passed to createSolver or added to public options.
class PropertySolver extends Solver {
  calls = 0;
  reductions = 0;
  deleted = 0;
  laterReductions = 0;
  laterDeleted = 0;
  // Rounds with NO possible deletion under the pinned two-tier policy: the
  // reducible tier's worse-half window was empty or fully reason-locked.
  candidateFreeRounds = 0;
  fullyLockedRounds = 0;
  laterCandidateFreeRounds = 0;
  laterFullyLockedRounds = 0;

  override solveAssuming(...args: Parameters<Solver['solveAssuming']>): VariableAssignments | null {
    this.calls += 1;
    try {
      return super.solveAssuming(...args);
    } finally {
      assertRoot(this);
      assert.strictEqual(internals(this).incrementalCallActive, false);
    }
  }

  override reduceLearnedClauses(): void {
    const before = [...this.clauses];
    const reasons = [...this.reason];
    const total = this.stats.learnedClauses;
    const live = this.stats.learnedClausesCurrent;
    super.reduceLearnedClauses();
    const retained = new Set(this.clauses);
    const removed = before.filter((clause) => !retained.has(clause));
    for (const clause of before) {
      if (!clause.learned || clause.lbd <= 2 || reasons.includes(clause)) {
        assert.ok(retained.has(clause), 'every permanent, low-LBD or reason clause survives');
      }
    }
    // Exact two-tier selection fidelity: the deleted set is precisely the
    // unlocked worse half of the reducible tier (stable activity order over
    // admission order).
    const reducible = before.filter((clause) => clause.learned && clause.lbd > 2);
    const ranked = reducible
      .map((clause, admission) => ({ clause, admission }))
      .sort(
        (left, right) =>
          left.clause.activity - right.clause.activity || left.admission - right.admission,
      );
    const window = ranked.slice(0, Math.floor(ranked.length / 2)).map(({ clause }) => clause);
    assert.deepStrictEqual(
      new Set(removed),
      new Set(window.filter((clause) => !reasons.includes(clause))),
      'exactly the unlocked worse half of the reducible tier',
    );
    assert.strictEqual(this.stats.learnedClauses, total);
    assert.strictEqual(this.stats.learnedClausesCurrent, live - removed.length);
    this.checkInvariants();
    this.reductions += 1;
    this.deleted += removed.length;
    if (removed.length === 0) {
      if (window.length === 0) {
        this.candidateFreeRounds += 1;
      } else {
        this.fullyLockedRounds += 1;
      }
    }
    if (this.calls > 1) {
      this.laterReductions += 1;
      this.laterDeleted += removed.length;
      if (removed.length === 0) {
        if (window.length === 0) {
          this.laterCandidateFreeRounds += 1;
        } else {
          this.laterFullyLockedRounds += 1;
        }
      }
    }
  }
}

function makeSolver(
  expr: BooleanExpr,
  variant: Variant,
): { handle: SatSolver; core?: PropertySolver } {
  if (variant.knobs === undefined) return { handle: createSolver(expr) };
  const core = new PropertySolver(compile(expr), {
    ...variant.knobs,
    enablePle: false,
    maxConflicts: 1000,
  });
  return {
    handle: { solve: (assumptions, stats) => core.solveAssuming(assumptions, stats) },
    core,
  };
}

function assumptionSequence(
  expr: BooleanExpr,
  reference: VariableAssignments[],
  seed: number,
): VariableAssignments[] {
  const names = [...getVariables(expr)];
  const rng = mulberry32(400_000 + seed);
  const shuffledNames = () => {
    const shuffled = [...names];
    for (let index = shuffled.length - 1; index > 0; index -= 1) {
      const other = rng.nextInt(index + 1);
      [shuffled[index], shuffled[other]] = [shuffled[other], shuffled[index]];
    }
    return shuffled;
  };
  const randomSubset = () =>
    Object.fromEntries(
      shuffledNames()
        .filter(() => rng.boolean())
        .map((name) => [name, rng.pick([Value.FALSE, Value.TRUE, Value.UNSET])]),
    );
  // Mix independently drawn subsets, reference-generated consistent and
  // contradictory subsets, a total random assignment, UNSET and base recovery.
  return [
    {},
    randomSubset(),
    reference.length > 0
      ? randomAssumptions(rng, expr, { kind: 'consistent', maxAssumptions: 4 })
      : randomSubset(),
    reference.length < 2 ** names.length
      ? randomAssumptions(rng, expr, { kind: 'contradictory' })
      : randomSubset(),
    Object.fromEntries(shuffledNames().map((name) => [name, rng.pick([Value.FALSE, Value.TRUE])])),
    Object.fromEntries(shuffledNames().map((name) => [name, Value.UNSET])),
    randomSubset(),
    {},
  ].map((assumptions) => Object.freeze(assumptions));
}

for (const variant of VARIANTS) {
  describe(`incremental reference cross-validation: ${variant.label}`, () => {
    it('checks 256 seeded formulas / 2048 sequential calls, not fresh solvers per subset', (t) => {
      const totals = {
        formulas: 0,
        calls: 0,
        sat: 0,
        unsat: 0,
        recoveries: 0,
        learned: 0,
        restarts: 0,
        reductions: 0,
        deleted: 0,
        laterReductions: 0,
        laterDeleted: 0,
        candidateFreeRounds: 0,
        fullyLockedRounds: 0,
        laterCandidateFreeRounds: 0,
        laterFullyLockedRounds: 0,
      };
      for (const pool of POOLS) {
        const distinct = new Set<string>();
        const kinds = new Set<string>();
        const namesSeen = new Set<string>();
        for (let seed = 0; seed < SEEDS_PER_POOL; seed += 1) {
          const generated = randomFormula(mulberry32(seed), {
            maxDepth: 3,
            maxWidth: 4,
            variables: pool.names,
          });
          const expr = generated.expr;
          distinct.add(JSON.stringify(expr));
          for (const kind of generated.kinds) kinds.add(kind);
          for (const name of getVariables(expr)) namesSeen.add(name);
          const reference = referenceModels(expr);
          const sequence = assumptionSequence(expr, reference, seed);
          assert.strictEqual(sequence.length, CALLS_PER_FORMULA);
          const { handle, core } = makeSolver(expr, variant);
          const initial = core === undefined ? undefined : { ...core.stats };
          const work = counters();
          const stats = counters(999);
          let sawUnsat = false;
          for (const [index, assumptions] of sequence.entries()) {
            Object.assign(stats, counters(999));
            const actual = handle.solve(assumptions, stats);
            assertResult(expr, assumptions, reference, actual);
            for (const key of WORK_KEYS) {
              assert.ok(Number.isInteger(stats[key]) && stats[key] >= 0, 'nonnegative actual work');
              work[key] += stats[key];
              if (core !== undefined && initial !== undefined) {
                assert.strictEqual(
                  work[key],
                  core.stats[key] - initial[key],
                  `${key} per-call/lifetime reconciliation`,
                );
              }
            }
            assert.ok(
              Number.isInteger(stats.learnedClausesCurrent) && stats.learnedClausesCurrent >= 0,
            );
            if (core !== undefined) {
              assert.strictEqual(
                stats.learnedClausesCurrent,
                core.clauses.filter((clause) => clause.learned).length,
              );
            }
            if (actual === null) {
              sawUnsat = true;
              totals.unsat += 1;
            } else {
              totals.sat += 1;
            }
            if (index === sequence.length - 1 && sawUnsat && reference.length > 0) {
              assert.ok(actual !== null, 'a previous incompatible call cannot poison the base');
              totals.recoveries += 1;
            }
            totals.calls += 1;
            totals.learned += stats.learnedClauses;
            totals.restarts += stats.restarts;
          }
          if (core !== undefined) {
            assert.strictEqual(core.calls, CALLS_PER_FORMULA);
            totals.reductions += core.reductions;
            totals.deleted += core.deleted;
            totals.laterReductions += core.laterReductions;
            totals.laterDeleted += core.laterDeleted;
            totals.candidateFreeRounds += core.candidateFreeRounds;
            totals.fullyLockedRounds += core.fullyLockedRounds;
            totals.laterCandidateFreeRounds += core.laterCandidateFreeRounds;
            totals.laterFullyLockedRounds += core.laterFullyLockedRounds;
          }
          totals.formulas += 1;
        }
        assert.ok(distinct.size >= 100, 'at least 100 DISTINCT seeded formulas per name pool');
        assert.deepStrictEqual([...kinds].sort(), ['and', 'implies', 'not', 'or', 'xor']);
        assert.deepStrictEqual([...namesSeen].sort(), [...pool.names].sort());
      }
      assert.strictEqual(totals.formulas, 256);
      assert.strictEqual(totals.calls, 2048);
      assert.ok(totals.sat > 0 && totals.unsat > 0 && totals.recoveries > 0);
      assert.ok(totals.learned > 0);
      if (variant.knobs !== undefined) {
        assert.ok(totals.restarts > 0);
        assert.ok(totals.reductions > 0);
        // The pinned two-tier policy deletes only from the reducible tier's
        // worse-half window; small incremental searches may legitimately
        // present no candidates on some knob settings — but a zero-deletion
        // total is acceptable only when EVERY round is explained (empty
        // window or fully locked). The base1/reduction1 variant retains hard
        // deletion evidence (see its diagnostic), and reduction.spec.ts
        // carries deterministic forced-round deletion witnesses.
        assert.ok(
          totals.deleted > 0 ||
            totals.candidateFreeRounds + totals.fullyLockedRounds === totals.reductions,
          'zero-deletion rounds must all be candidate-free or fully locked',
        );
        assert.ok(totals.laterReductions > 0, 'real reduction rounds after earlier calls');
        assert.ok(
          totals.laterDeleted > 0 ||
            totals.laterCandidateFreeRounds + totals.laterFullyLockedRounds ===
              totals.laterReductions,
          'zero-deletion later rounds must all be candidate-free or fully locked',
        );
      }
      t.diagnostic(JSON.stringify(totals));
    });

    it('is deterministic for the same ordered call sequence on two independent handles', () => {
      let calls = 0;
      for (const pool of POOLS) {
        for (let seed = 0; seed < 8; seed += 1) {
          const expr = randomFormula(mulberry32(seed), {
            maxDepth: 3,
            maxWidth: 4,
            variables: pool.names,
          }).expr;
          const reference = referenceModels(expr);
          const first = makeSolver(expr, variant).handle;
          const second = makeSolver(expr, variant).handle;
          for (const assumptions of assumptionSequence(expr, reference, seed)) {
            const statsA = counters(999);
            const statsB = counters(-1);
            const modelA = first.solve(assumptions, statsA);
            const modelB = second.solve(assumptions, statsB);
            assertResult(expr, assumptions, reference, modelA);
            assertResult(expr, assumptions, reference, modelB);
            assert.deepStrictEqual(modelA, modelB);
            assert.deepStrictEqual(statsA, statsB);
            calls += 2;
          }
        }
      }
      assert.strictEqual(calls, 256);
    });
  });
}
