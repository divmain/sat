import assert from 'node:assert';
import { describe, it } from 'node:test';
import { and, createSolver, Value } from '../src/index.js';
import type {
  BooleanExpr,
  SatSolver,
  VariableAssignments,
  VariablePriority,
} from '../src/index.js';
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

  override solveAssuming(
    ...args: Parameters<Solver['solveAssuming']>
  ): ReturnType<Solver['solveAssuming']> {
    this.calls += 1;
    try {
      return super.solveAssuming(...args);
    } finally {
      assertRoot(this);
      assert.strictEqual(internals(this).incrementalCallActive, false);
    }
  }

  // add() is audited like the solve boundary: after every admission the
  // handle is back at a coherent root state (named-flag heap accounting
  // included), even with fresh root units pending propagation.
  override add(expr: BooleanExpr): void {
    super.add(expr);
    assertRoot(this);
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
  variablePriority?: VariablePriority,
): { handle: SatSolver; core?: PropertySolver } {
  if (variant.knobs === undefined) return { handle: createSolver(expr, { variablePriority }) };
  const core = new PropertySolver(compile(expr), {
    ...variant.knobs,
    enablePle: false,
    variablePriority,
  });
  return {
    handle: {
      // The runaway guard is now a per-call conflict budget: verdicts are
      // oracle-checked, so an 'unknown' would fail loudly rather than pass
      // for exhaustion.
      solve: (assumptions, options) => core.solveAssuming(assumptions, options?.stats, 1000),
      solveAsync: (assumptions, options) =>
        core.solveAssumingAsync(
          assumptions,
          options?.stats,
          1000,
          options?.signal,
          options?.yieldQuantum,
        ),
      add: (addExpr) => core.add(addExpr),
      variables: () => core.variables(),
    },
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
            const actual = handle.solve(assumptions, { stats });
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
            if (actual.status === 'unsat') {
              sawUnsat = true;
              totals.unsat += 1;
            } else {
              totals.sat += 1;
            }
            if (index === sequence.length - 1 && sawUnsat && reference.length > 0) {
              assert.ok(
                actual.status === 'sat',
                'a previous incompatible call cannot poison the base',
              );
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
            const modelA = first.solve(assumptions, { stats: statsA });
            const modelB = second.solve(assumptions, { stats: statsB });
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

// ---------------------------------------------------------------------------
// Incremental add() equivalence (Design § Incremental Clause Addition)
// ---------------------------------------------------------------------------

const ADD_SEEDS_PER_POOL = 64;
const ADD_BATCHES = 3;

interface AddHistory {
  readonly batches: BooleanExpr[];
  // Assumption sets solved at each stage (stage i covers batches 0..i).
  readonly calls: ReadonlyArray<readonly VariableAssignments[]>;
  // The first new name each batch introduces (undefined when a batch reuses
  // only known names): the hook target that addresses appended variables.
  readonly hookTargets: ReadonlyArray<string | undefined>;
}

// A seeded history: three random batches over the pool, plus per-stage
// assumption sets drawn against the growing conjunction's reference models.
// Deterministic under the seed, so every variant and twin replays it exactly.
function addHistory(poolNames: readonly string[], seed: number): AddHistory {
  const rng = mulberry32(700_000 + seed);
  const batches: BooleanExpr[] = [];
  const calls: VariableAssignments[][] = [];
  const hookTargets: Array<string | undefined> = [];
  const known = new Set<string>();
  for (let batch = 0; batch < ADD_BATCHES; batch += 1) {
    const expr = randomFormula(rng, { maxDepth: 2, maxWidth: 3, variables: poolNames }).expr;
    batches.push(expr);
    const fresh = [...getVariables(expr)].filter((name) => !known.has(name)).sort();
    hookTargets.push(fresh[0]);
    for (const name of fresh) known.add(name);
    const conjunction = and(...batches);
    const reference = referenceModels(conjunction);
    const names = [...known].sort();
    // Fisher-Yates, like the main battery: an inconsistent sort comparator
    // would make the stream depend on the engine's sort implementation.
    const shuffledNames = (): string[] => {
      const shuffled = [...names];
      for (let index = shuffled.length - 1; index > 0; index -= 1) {
        const other = rng.nextInt(index + 1);
        [shuffled[index], shuffled[other]] = [shuffled[other], shuffled[index]];
      }
      return shuffled;
    };
    const randomSubset = (): VariableAssignments =>
      Object.fromEntries(
        shuffledNames()
          .filter(() => rng.boolean())
          .map((name) => [name, rng.pick([Value.FALSE, Value.TRUE, Value.UNSET])]),
      );
    calls.push([
      {},
      randomSubset(),
      reference.length > 0
        ? randomAssumptions(rng, conjunction, { kind: 'consistent', maxAssumptions: 4 })
        : randomSubset(),
      reference.length < 2 ** names.length
        ? randomAssumptions(rng, conjunction, { kind: 'contradictory' })
        : randomSubset(),
    ]);
  }
  return { batches, calls, hookTargets };
}

// Replay one history on one handle, oracle-checking every result against the
// growing conjunction reference. Returns the per-call (result, stats) pairs
// for cross-handle determinism comparison.
function replayAddHistory(
  variant: Variant,
  history: AddHistory,
  options?: { failAt?: { batch: number; exprs: unknown[] }; trackHook?: (hit: string) => void },
): Array<{ result: ReturnType<SatSolver['solve']>; stats: ReturnType<typeof counters> }> {
  let hookTarget: string | undefined;
  const variablePriority: VariablePriority = (unassigned) => {
    if (hookTarget !== undefined && unassigned.includes(hookTarget)) {
      options?.trackHook?.(hookTarget);
      return [hookTarget, true];
    }
    return null;
  };
  const observations: Array<{
    result: ReturnType<SatSolver['solve']>;
    stats: ReturnType<typeof counters>;
  }> = [];
  let handle: SatSolver | undefined;
  for (let batch = 0; batch < history.batches.length; batch += 1) {
    const conjunction = and(...history.batches.slice(0, batch + 1));
    const reference = referenceModels(conjunction);
    const staged = history.batches[batch];
    if (batch === 0) {
      handle = makeSolver(staged, variant, variablePriority).handle;
    } else {
      if (handle === undefined) throw new Error('history replay lost its handle');
      const established: SatSolver = handle;
      if (options?.failAt !== undefined && options.failAt.batch === batch) {
        for (const bad of options.failAt.exprs) {
          assert.throws(() => established.add(bad as BooleanExpr), /invalid BooleanExpr/);
        }
      }
      established.add(staged);
      // The named universe grows exactly by this batch's new names, always
      // presented globally sorted.
      assert.deepStrictEqual(established.variables(), [...getVariables(conjunction)].sort());
    }
    if (handle === undefined) throw new Error('history replay lost its handle');
    const active: SatSolver = handle;
    hookTarget = history.hookTargets[batch];
    for (const assumptions of history.calls[batch]) {
      const stats = counters(999);
      const result = active.solve(assumptions, { stats });
      // The equivalence contract: verdicts and model-set validity agree with
      // single-shot solving of the conjunction (assertResult embeds the
      // reference verdict, model validity/shape, and sound-core oracles).
      assertResult(conjunction, assumptions, reference, result);
      observations.push({ result, stats });
    }
  }
  return observations;
}

for (const variant of VARIANTS) {
  describe(`incremental add() cross-validation: ${variant.label}`, () => {
    it('checks seeded add+solve sequences against the growing conjunction reference', (t) => {
      let hookHits = 0;
      let sat = 0;
      let unsat = 0;
      let additions = 0;
      for (const pool of POOLS) {
        for (let seed = 0; seed < ADD_SEEDS_PER_POOL; seed += 1) {
          const history = addHistory(pool.names, seed);
          additions += history.batches.length - 1;
          const observations = replayAddHistory(variant, history, {
            trackHook: () => {
              hookHits += 1;
            },
          });
          for (const { result } of observations) {
            if (result.status === 'sat') sat += 1;
            else unsat += 1;
          }
        }
      }
      assert.ok(sat > 0 && unsat > 0, 'both verdicts exercised across the battery');
      assert.ok(hookHits > 0, 'hooks addressed appended variables');
      t.diagnostic(
        `${
          2 * ADD_SEEDS_PER_POOL
        } seeded histories; ${additions} adds; ${sat} SAT / ${unsat} UNSAT calls; ${hookHits} appended-variable hook picks`,
      );
    });

    it('is deterministic for identical add histories, including per-call stats', () => {
      let calls = 0;
      for (const pool of POOLS) {
        for (let seed = 0; seed < 8; seed += 1) {
          const history = addHistory(pool.names, 40_000 + seed);
          const first = replayAddHistory(variant, history);
          const second = replayAddHistory(variant, history);
          assert.deepStrictEqual(first, second);
          calls += first.length;
        }
      }
      assert.strictEqual(calls, 2 * 8 * (ADD_BATCHES * 4));
    });

    it('keeps failed adds atomic inside a seeded history', () => {
      const failures: unknown[] = [
        { and: ['a'], or: ['b'] }, // ambiguous multi-key node
        { not: ['a'] }, // non-node payload
        { or: 7 }, // non-array operands
      ];
      let comparisons = 0;
      for (const pool of POOLS) {
        for (let seed = 0; seed < 8; seed += 1) {
          const history = addHistory(pool.names, 80_000 + seed);
          const reference = replayAddHistory(variant, history);
          const withFailure = replayAddHistory(variant, history, {
            failAt: { batch: 1, exprs: failures },
          });
          assert.deepStrictEqual(
            withFailure,
            reference,
            'a failed add leaves the history byte-for-byte equivalent',
          );
          comparisons += 1;
        }
      }
      assert.strictEqual(comparisons, 2 * 8);
    });
  });
}
