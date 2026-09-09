// Public behavior tests, ported to the v2 API. Per-case
// dispositions follow Design § Testing and Benchmarking Strategy:
//
//   - Exact expected models: and, not, xor, the complex worked example, and
//     the unsolvable case (asserted with deepStrictEqual against `Value`).
//   - Verified with forced-variable + reference-validity + model-shape
//     assertions: or (PLE forces {a: TRUE, b: TRUE}) and implies (the trap:
//     PLE yields {a: FALSE, b: TRUE}, not v1's FALSE-first {a: FALSE,
//     b: FALSE} — both models are valid).
//   - Hypergraph: stats oracle (calibrated decisions, propagations >= 10),
//     forced subset {a, b, c, g, h} TRUE, and reference validity; the
//     don't-care region legitimately varies under PLE, and the hypergraph
//     is proven by the stats oracle rather than a wall-clock measurement.
//   - Enumeration (describe('getAllSolutions')): order-insensitive
//     comparison (assertModelListsEqual), per-model shape assertions,
//     count cross-checks against the reference enumerator, the empty-formula
//     corner cases (and() -> [{}], or() -> []), the PLE-disabled regression
//     (or('a','b') must enumerate all three models — PLE would pin {a: TRUE,
//     b: TRUE} first and silently drop two), and the 40-variable smoke test
//     (no array-length-cap regression class).

import { describe, it } from 'node:test';
import assert from 'node:assert';
import * as publicApi from '../src';
import {
  and,
  createSolver,
  getAllSolutions,
  getAllSolutionsAsync,
  getSolution,
  getSolutionAsync,
  implies,
  not,
  or,
  Value,
  xor,
} from '../src';
import type { BooleanExpr, Variable, VariablePriority } from '../src';
import {
  assertModelListsEqual,
  assertModelShape,
  expectCompleteModels,
  expectSatModel,
  expressionValue,
  hypergraphFormula,
  hypergraphPrereqs,
  modelKey,
  referenceModels,
} from './helpers';

// Decisions remaining after the hypergraph's UP+PLE fixpoint, calibrated
// against the pinned reference implementation (HYPERGRAPH_DECISIONS in
// test/solver.spec.ts). The pinned global-sweep PLE assigns the whole chain
// except the two zero-occurrence don't-cares e and n (every clause mentioning
// them is satisfied before they could become pure), so the search loop
// decides those two FALSE-first. Design § Testing requires the actual value
// here, not zero.
const HYPERGRAPH_DECISIONS = 2;

// v2 `variablePriority` counterpart of v1's `selectNextVar` (Design §
// Branching Heuristics): `assignments[var] === Value.UNSET` maps to
// `=== undefined` against the partial record, and the candidates filter maps
// to the `unassigned` parameter. The "rank by satisfied parents, branch TRUE
// on ready nodes" logic is unchanged.
const relationships = hypergraphPrereqs.reduce((memo, [target, prereq]) => {
  const connectedVars = memo.get(prereq);
  if (connectedVars === undefined) {
    memo.set(prereq, [target]);
  } else {
    connectedVars.push(target);
  }
  return memo;
}, new Map<Variable, Variable[]>());

const visitOrder: VariablePriority = (unassigned, assignments) => {
  if (unassigned.length === 0) {
    return null;
  }

  const satisfiedRelationships = Object.fromEntries(
    unassigned.map((candidate) => [candidate, 0]),
  ) as Record<string, number>;

  // for each variable under consideration
  for (const candidate of unassigned) {
    // identify its "parent" variables/nodes
    const connectedVars = relationships.get(candidate);
    if (connectedVars) {
      // and track how many parents are already satisfied
      for (const connectedVar of connectedVars) {
        if (assignments[connectedVar] === Value.TRUE) {
          satisfiedRelationships[candidate] += 1;
        } else if (assignments[connectedVar] === Value.FALSE) {
          satisfiedRelationships[candidate] = -1 * unassigned.length;
        }
      }
    }
  }

  let topCandidate: Variable = unassigned[0];
  let topCandidateRank = Number.NEGATIVE_INFINITY;
  for (const candidate of unassigned) {
    const rank = satisfiedRelationships[candidate];
    if (rank > topCandidateRank) {
      topCandidate = candidate;
      topCandidateRank = rank;
    }
  }

  return topCandidateRank >= 1 ? [topCandidate, true] : [topCandidate, false];
};

describe('getSolution', () => {
  describe('solvable', () => {
    it('supports and operator (exact model)', () => {
      const model = expectSatModel(getSolution(and('a', 'b')));
      assert.deepStrictEqual(model, { a: Value.TRUE, b: Value.TRUE });
      assertModelShape(model, and('a', 'b'));
      assert.strictEqual(expressionValue(and('a', 'b'), model), Value.TRUE);
    });

    it('supports or operator (PLE forces the oneOf case)', () => {
      const formula = or('a', 'b');
      const model = expectSatModel(getSolution(formula));
      // The plain clause (a ∨ b) makes both literals pure, so scoped PLE
      // forces {a: TRUE, b: TRUE} — no search, no choices.
      assert.deepStrictEqual(model, { a: Value.TRUE, b: Value.TRUE });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    });

    it('supports not operator (exact model)', () => {
      const model = expectSatModel(getSolution(not('b')));
      assert.deepStrictEqual(model, { b: Value.FALSE });
      assertModelShape(model, not('b'));
      assert.strictEqual(expressionValue(not('b'), model), Value.TRUE);
    });

    it('supports implies operator (PLE trap: {a: FALSE, b: TRUE})', () => {
      const formula = implies('a', 'b');
      const model = expectSatModel(getSolution(formula));
      // Trap (Design § Testing): the plain clause (¬a ∨ b) leaves both
      // variables pure, so scoped PLE yields {a: FALSE, b: TRUE} — NOT v1's
      // FALSE-first {a: FALSE, b: FALSE}. Both are valid models of implies.
      assert.deepStrictEqual(model, { a: Value.FALSE, b: Value.TRUE });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      // Implies is not a biconditional: a=FALSE leaves b unconstrained, so
      // the non-forced model {a: FALSE, b: FALSE} is valid too.
      assert.strictEqual(expressionValue(formula, { a: Value.FALSE, b: Value.FALSE }), Value.TRUE);
      assert.strictEqual(expressionValue(formula, { a: Value.TRUE, b: Value.TRUE }), Value.TRUE);
    });

    it('supports xor operator (exact model)', () => {
      const formula = xor('a', 'b');
      const model = expectSatModel(getSolution(formula));
      // Symmetric gate encodings make PLE inert; FALSE-first/index-order
      // branching reproduces v1's {a: false, b: true}.
      assert.deepStrictEqual(model, { a: Value.FALSE, b: Value.TRUE });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    });

    it('supports complex clauses (exact unique model)', () => {
      const formula = and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')));
      const model = expectSatModel(getSolution(formula));
      assert.deepStrictEqual(model, {
        a: Value.TRUE,
        b: Value.FALSE,
        c: Value.TRUE,
        d: Value.TRUE,
        e: Value.TRUE,
      });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    });

    it('implements the v1-compatible empty-formula semantics', () => {
      assert.deepStrictEqual(getSolution(and()), { status: 'sat', model: {} });
      assert.deepStrictEqual(getSolution(or()), { status: 'unsat', core: {} });
    });

    describe('hypergraph traversal problems', () => {
      // With the following graph, each node can only be visited if _all_
      // parent nodes were already visited.
      //        ╭─╮
      //     ┌─▶│b│────────┐
      // ╭─╮ │  ╰─╯    ╭─╮ │
      // │a│─┤      ┌─▶│g│─┤
      // ╰─╯ │  ╭─╮ │  ╰─╯ │  ╭─╮
      //     └─▶│c│─┤      ├─▶│h│
      //        ╰─╯ │  ╭─╮ │  ╰─╯
      //            ├─▶│f│─┘
      // ╭─╮    ╭─╮ │  ╰─╯
      // │d│───▶│e│─┘
      // ╰─╯    ╰─╯
      //
      // plus the disjoint chain i→j→…→s (see nodePrereqs).

      it('solves with the calibrated stats oracle and the forced subset', () => {
        const stats = {
          decisions: 999,
          propagations: 999,
          conflicts: 999,
          restarts: 999,
          learnedClauses: 999,
          learnedClausesCurrent: 999,
          learnedLiterals: 999,
          minimizedLiterals: 999,
        };
        const model = expectSatModel(
          getSolution(hypergraphFormula(), { assumptions: { h: Value.TRUE }, stats }),
        );

        // With { h: TRUE } asserted at level 0, unit propagation forces
        // {h, b, g, a, c} and the pinned global-sweep PLE assigns the rest of
        // the chain; only the two zero-occurrence don't-cares remain for the
        // search loop (see HYPERGRAPH_DECISIONS above).
        assert.strictEqual(stats.decisions, HYPERGRAPH_DECISIONS);
        assert.ok(stats.propagations >= 10, 'PLE enqueues count as propagations');
        assert.strictEqual(stats.conflicts, 0);
        assert.strictEqual(stats.restarts, 0);
        assert.strictEqual(stats.learnedClauses, 0);
        assert.strictEqual(stats.learnedClausesCurrent, 0);

        assertModelShape(model, hypergraphFormula());
        // The assumption-forced subset is identical in every solver run.
        for (const required of ['a', 'b', 'c', 'g', 'h']) {
          assert.strictEqual(model[required], Value.TRUE);
        }
        // The don't-care region legitimately varies under PLE; reference
        // evaluation of the full model is the ground truth.
        assert.strictEqual(expressionValue(hypergraphFormula(), model), Value.TRUE);
      });

      it('honors a domain variablePriority with equal forced subset', () => {
        const defaultModel = expectSatModel(
          getSolution(hypergraphFormula(), { assumptions: { h: Value.TRUE } }),
        );
        const candidates: Variable[][] = [];
        const customModel = expectSatModel(
          getSolution(hypergraphFormula(), {
            assumptions: { h: Value.TRUE },
            variablePriority: (unassigned, assignments) => {
              candidates.push([...unassigned]);
              return visitOrder(unassigned, assignments);
            },
          }),
        );

        assert.deepEqual(candidates, [['e', 'n'], ['n']], 'two ordinary completion decisions');
        assertModelShape(customModel, hypergraphFormula());
        assert.strictEqual(expressionValue(hypergraphFormula(), customModel), Value.TRUE);
        for (const required of ['a', 'b', 'c', 'g', 'h']) {
          assert.strictEqual(customModel[required], Value.TRUE);
          assert.strictEqual(defaultModel[required], Value.TRUE);
        }
      });
    });
  });

  describe('assumptions', () => {
    it('throws a descriptive error for an unknown assumption variable', () => {
      assert.throws(
        () => getSolution(and('a', 'b'), { assumptions: { missing: Value.TRUE } }),
        /unknown assumption variable: "missing"/,
      );
    });

    it('throws for assumption values outside {UNSET, FALSE, TRUE}', () => {
      assert.throws(
        () => getSolution(and('a'), { assumptions: { a: 2 as Value } }),
        /invalid assumption value for "a": 2/,
      );
    });

    it('ignores UNSET assumption entries', () => {
      assert.deepStrictEqual(getSolution(not('b'), { assumptions: { b: Value.UNSET } }), {
        status: 'sat',
        model: { b: Value.FALSE },
      });
    });

    it('propagates assumptions immediately at level zero', () => {
      // (¬a ∨ b) with a assumed TRUE forces b=TRUE before any decision.
      assert.deepStrictEqual(getSolution(implies('a', 'b'), { assumptions: { a: Value.TRUE } }), {
        status: 'sat',
        model: { a: Value.TRUE, b: Value.TRUE },
      });
    });

    it('returns the failed-assumption core fast when assumptions contradict the formula', () => {
      // The tainted-implication witness, single-shot: the implied x is NOT an
      // assumption; the walk resolves through it to both supplied leaves.
      assert.deepStrictEqual(
        getSolution(implies('a', 'b'), { assumptions: { a: Value.TRUE, b: Value.FALSE } }),
        { status: 'unsat', core: { a: Value.TRUE, b: Value.FALSE } },
      );
    });
  });

  describe('stats out-param', () => {
    it('zeroes the provided stats object, then populates it in place', () => {
      const stats = {
        decisions: 999,
        propagations: 999,
        conflicts: 999,
        restarts: 999,
        learnedClauses: 999,
        learnedClausesCurrent: 999,
        learnedLiterals: 999,
        minimizedLiterals: 999,
      };
      const model = expectSatModel(getSolution(and('a', 'b'), { stats }));
      assert.deepStrictEqual(model, { a: Value.TRUE, b: Value.TRUE });
      // Zeroing is the callee's responsibility; the same reference is then
      // populated by the solver (both unit clause enqueues count as
      // propagations; zero decisions on an all-unit formula).
      assert.strictEqual(stats.decisions, 0);
      assert.strictEqual(stats.propagations, 2);
      assert.strictEqual(stats.conflicts, 0);
      assert.strictEqual(stats.restarts, 0);
      assert.strictEqual(stats.learnedClauses, 0);
      assert.strictEqual(stats.learnedClausesCurrent, 0);
    });
  });

  describe('variablePriority contract', () => {
    it('invokes the hook only at decision points', () => {
      let hookCalls = 0;
      const hook: VariablePriority = (unassigned, _assignments) => {
        hookCalls += 1;
        assert.deepEqual(unassigned, ['a', 'b']);
        return ['a', true];
      };

      // Gate-symmetric xor: PLE is inert and at least one decision is
      // unavoidable, so the hook fires exactly once — at the single decision
      // point. Keep this PLE-inert cadence witness in addition to the two
      // ordinary don't-care decisions on the hypergraph.
      const model = expectSatModel(getSolution(xor('a', 'b'), { variablePriority: hook }));
      assert.strictEqual(hookCalls, 1);
      assertModelShape(model, xor('a', 'b'));
      assert.strictEqual(expressionValue(xor('a', 'b'), model), Value.TRUE);

      const totalAfterXor = hookCalls;
      const silentHook: VariablePriority = () => {
        hookCalls += 1;
        return null;
      };
      assert.deepStrictEqual(getSolution(and('a', 'b'), { variablePriority: silentHook }), {
        status: 'sat',
        model: { a: Value.TRUE, b: Value.TRUE },
      });
      // The all-unit formula needs no decisions, so the hook is never called.
      assert.strictEqual(hookCalls, totalAfterXor);
    });
  });

  describe('unsolvable', () => {
    it('returns an assumption-independent empty core for the unsolvable worked example', () => {
      assert.deepStrictEqual(
        getSolution(
          and(
            not('b'),
            or('a', 'b'),
            xor('b', 'c'),
            implies('c', and('d', 'e')),
            not('d'),
            xor('b', 'e'),
          ),
        ),
        { status: 'unsat', core: {} },
      );
    });
  });
});

describe('getAllSolutions', () => {
  describe('solvable', () => {
    it('supports and operator (exact model)', () => {
      const formula = and('a', 'b');
      const models = expectCompleteModels(getAllSolutions(formula));
      assertModelListsEqual(models, [{ a: Value.TRUE, b: Value.TRUE }]);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports or operator — enumerates all three models (PLE-unsoundness regression)', () => {
      const formula = or('a', 'b');
      const models = expectCompleteModels(getAllSolutions(formula));
      // PLE is disabled in enumeration mode (Design § Solver Core): with PLE
      // on, iteration 1 pins {a: TRUE, b: TRUE} (both literals pure), then the
      // blocking clause (¬a ∨ ¬b) conflicts with the stale pins and the
      // solver reports UNSAT — silently dropping two valid models. Only a 3
      // count proves PLE is off.
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.FALSE },
        { a: Value.TRUE, b: Value.TRUE },
      ]);
      assert.strictEqual(models.length, 3);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('enumerates the worked (v∨a) PLE counterexample completely', () => {
      // Design § Solver Core: with PLE on, a persistent solver pins v=TRUE
      // (pure-positive) in iteration 1, and the blocking clauses (¬v∨a) and
      // (¬v∨¬a) then conflict with the stale pin — the valid model
      // {v: FALSE, a: TRUE} is silently dropped (2 models instead of 3).
      // Enumeration must therefore return all three.
      const formula = or('v', 'a');
      assertModelListsEqual(expectCompleteModels(getAllSolutions(formula)), [
        { v: Value.FALSE, a: Value.TRUE },
        { v: Value.TRUE, a: Value.FALSE },
        { v: Value.TRUE, a: Value.TRUE },
      ]);
    });

    it('supports not operator (exact model)', () => {
      const formula = not('b');
      const models = expectCompleteModels(getAllSolutions(formula));
      assertModelListsEqual(models, [{ b: Value.FALSE }]);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports implies operator (all three models)', () => {
      const formula = implies('a', 'b');
      const models = expectCompleteModels(getAllSolutions(formula));
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.FALSE },
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.TRUE },
      ]);
      assert.strictEqual(models.length, referenceModels(formula).length);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports xor operator (both models)', () => {
      const formula = xor('a', 'b');
      const models = expectCompleteModels(getAllSolutions(formula));
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.FALSE },
      ]);
      assert.strictEqual(models.length, referenceModels(formula).length);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports complex clauses (exact unique model)', () => {
      const formula = and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')));
      const models = expectCompleteModels(getAllSolutions(formula));
      assertModelListsEqual(models, [
        {
          a: Value.TRUE,
          b: Value.FALSE,
          c: Value.TRUE,
          d: Value.TRUE,
          e: Value.TRUE,
        },
      ]);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });
  });

  describe('unsolvable', () => {
    it('returns [] for the original v1 unsolvable worked example', () => {
      const formula = and(
        not('b'),
        or('a', 'b'),
        xor('b', 'c'),
        implies('c', and('d', 'e')),
        not('d'),
        xor('b', 'e'),
      );
      // b=FALSE forces c=TRUE, hence d=TRUE, contradicting not(d).
      // Independently check all 32 assignments over a,b,c,d,e as well.
      assert.deepStrictEqual(referenceModels(formula), []);
      assert.deepStrictEqual(getAllSolutions(formula), { status: 'complete', models: [] });
    });
  });

  describe('edge cases', () => {
    it('implements the v1-compatible empty-formula semantics', () => {
      // and(): the empty conjunction has one model, {}; the blocking clause
      // over zero named variables is the empty clause — terminal UNSAT for
      // enumeration after the first iteration.
      assert.deepStrictEqual(getAllSolutions(and()), { status: 'complete', models: [{}] });
      // or(): the empty disjunction compiles to the empty clause.
      assert.deepStrictEqual(getAllSolutions(or()), { status: 'complete', models: [] });
    });

    it('returns [] immediately for a levelZeroUnsat formula', () => {
      // and(or(), 'a') constant-folds to the empty clause (or() annihilates
      // the conjunction; 'a' stays in the named universe), so levelZeroUnsat
      // short-circuits before any solve.
      assert.deepStrictEqual(getAllSolutions(and(or(), 'a')), { status: 'complete', models: [] });
    });

    it('enumerates a 40-variable chain without an array-length cap', () => {
      // A brute-force enumerator materializes all 2^n assignments and throws
      // RangeError past n = 32; the chain of 40 implication clauses has
      // exactly 41 models (a TRUE prefix), so this is output-sensitive: one
      // solve per model, no 2^n materialization.
      const prereqClauses: Array<ReturnType<typeof implies>> = [];
      for (let index = 2; index <= 40; index += 1) {
        prereqClauses.push(implies(`v${index}`, `v${index - 1}`));
      }
      const formula = and(...prereqClauses);
      const models = expectCompleteModels(getAllSolutions(formula));

      assert.strictEqual(models.length, 41);
      assert.strictEqual(models.length, new Set(models.map(modelKey)).size);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });
  });

  describe('assumptions', () => {
    it('throws a descriptive error for an unknown assumption variable', () => {
      assert.throws(
        () => getAllSolutions(and('a', 'b'), { assumptions: { missing: Value.TRUE } }),
        /unknown assumption variable: "missing"/,
      );
    });

    it('throws for assumption values outside {UNSET, FALSE, TRUE}', () => {
      assert.throws(
        () => getAllSolutions(and('a'), { assumptions: { a: 2 as Value } }),
        /invalid assumption value for "a": 2/,
      );
    });

    it('ignores UNSET assumption entries', () => {
      const models = expectCompleteModels(
        getAllSolutions(or('a', 'b'), { assumptions: { a: Value.UNSET } }),
      );
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.FALSE },
        { a: Value.TRUE, b: Value.TRUE },
      ]);
    });

    it('filters enumeration to models extending the assumptions', () => {
      const models = expectCompleteModels(
        getAllSolutions(implies('a', 'b'), { assumptions: { b: Value.FALSE } }),
      );
      assertModelListsEqual(models, [{ a: Value.FALSE, b: Value.FALSE }]);
    });

    it('returns an empty model list when the assumptions contradict the formula', () => {
      // EnumerateResult carries no core; UNSAT shows as the empty list.
      assert.deepStrictEqual(getAllSolutions(and('a'), { assumptions: { a: Value.FALSE } }), {
        status: 'complete',
        models: [],
      });
    });
  });

  describe('stats out-param', () => {
    it('zeroes once and accumulates across all per-model iterations', () => {
      const stats = {
        decisions: 999,
        propagations: 999,
        conflicts: 999,
        restarts: 999,
        learnedClauses: 999,
        learnedClausesCurrent: 999,
        learnedLiterals: 999,
        minimizedLiterals: 999,
      };
      const models = expectCompleteModels(getAllSolutions(or('a', 'b'), { stats }));
      assert.strictEqual(models.length, 3);
      // One persistent solver: decide a=F -> b=T; after blocking, retry a=F
      // and conflict, learn/assert a=T, decide b=F. The next blocker is now
      // root-unit b=T (one immediate propagation); its model needs no decision.
      // The final blocker conflicts at root. Thus only a's one learned unit
      // lives in the database, not three units summed over discarded solvers.
      // enumeration.spec.ts independently audits the per-search/root trace.
      assert.strictEqual(stats.decisions, 3);
      assert.strictEqual(stats.propagations, 4);
      assert.strictEqual(stats.conflicts, 2);
      assert.strictEqual(stats.restarts, 0);
      assert.strictEqual(stats.learnedClauses, 1);
      assert.strictEqual(stats.learnedClausesCurrent, 1);
    });
  });

  describe('variablePriority contract', () => {
    it('consults the hook at enumeration decision points', () => {
      let hookCalls = 0;
      const hook: VariablePriority = (unassigned) => {
        hookCalls += 1;
        return unassigned.length === 0 ? null : [unassigned[0], true];
      };
      const models = expectCompleteModels(
        getAllSolutions(or('a', 'b'), { variablePriority: hook }),
      );

      assert.ok(hookCalls > 0, 'the hook must be consulted for at least one decision');
      // The preferred polarity changes enumeration order but never the model
      // set: three models, compared order-insensitively.
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.FALSE },
        { a: Value.TRUE, b: Value.TRUE },
      ]);
    });
  });
});

describe('top-level formula validation', () => {
  // A bare variable string is a valid OPERAND at any nested position but
  // never a valid top-level BooleanExpr (the formula type is an operator
  // object). It previously slipped through compile-time validation and died
  // on a raw engine TypeError inside variable collection (`'and' in expr`
  // on a primitive); every entry point must now surface the same style of
  // descriptive validation Error as any other malformed node.
  const bare = 'a' as unknown as BooleanExpr;
  const message =
    /invalid BooleanExpr at \$: expected an and\/or\/not\/atMost\/atLeast object, got string a/;

  it('rejects a bare variable string at the synchronous entry points', () => {
    assert.throws(() => getSolution(bare), { name: 'Error', message });
    assert.throws(() => getAllSolutions(bare), { name: 'Error', message });
    assert.throws(() => createSolver(bare), { name: 'Error', message });
  });

  it('rejects a bare variable string at the asynchronous entry points', async () => {
    // Async entry points validate before the first yield, so the failure
    // rejects the returned Promise (never a synchronous throw).
    await assert.rejects(getSolutionAsync(bare), { name: 'Error', message });
    await assert.rejects(getAllSolutionsAsync(bare), { name: 'Error', message });
  });

  it('rejects a bare variable string in SatSolver.add without touching the handle', () => {
    const solver = createSolver(and('x'));
    assert.throws(() => solver.add(bare), { name: 'Error', message });
    assert.deepStrictEqual(solver.variables(), ['x'], 'the named universe is unchanged');
    assert.deepStrictEqual(solver.solve(), { status: 'sat', model: { x: Value.TRUE } });
  });

  it('keeps bare variable operands valid at every nesting position', () => {
    const formula = and('a', or('b', not('c')));
    const model = expectSatModel(getSolution(formula));
    assertModelShape(model, formula);
    assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    // A single nested variable operand still folds to its unit assertion.
    assert.deepStrictEqual(getSolution(not('z')), { status: 'sat', model: { z: Value.FALSE } });
    assert.deepStrictEqual(createSolver(and('y')).variables(), ['y']);
  });
});

describe('public surface', () => {
  it('exports exactly the v3 symbol list', () => {
    // Runtime values: the frozen formula API plus the cardinality
    // constructors (atMostOne/atMost/atLeast/exactly), getSolution,
    // getAllSolutions, their async counterparts, createSolver and the
    // createSolverStats factory. Types (BooleanExpr, Variable,
    // VariableAssignments, SolverStats, SolverStatsInput, SolveResult,
    // EnumerateResult, SolveOptions, AsyncSolveOptions, SatSolver,
    // SatSolverCallOptions, SatSolverAsyncOptions, VariablePriority) are
    // exported by name but erased at runtime; no v1 entry point
    // (bruteForceAllSolutions, getInitialAssignments, selectNextVar) may
    // survive.
    assert.deepStrictEqual(Object.keys(publicApi).sort(), [
      'Value',
      'and',
      'atLeast',
      'atMost',
      'atMostOne',
      'createSolver',
      'createSolverStats',
      'exactly',
      'getAllSolutions',
      'getAllSolutionsAsync',
      'getSolution',
      'getSolutionAsync',
      'implies',
      'not',
      'or',
      'xor',
    ]);
  });
});
