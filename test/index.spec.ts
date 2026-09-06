// Public behavior tests, ported to the v2 API (task-e476). Per-case
// dispositions follow Design § Testing and Benchmarking Strategy:
//
//   - Exact expected models: and, not, xor, the complex worked example, and
//     the unsolvable case (asserted with deepStrictEqual against `Value`).
//   - Rewritten as forced-variable + reference-validity + model-shape
//     assertions: or (PLE forces {a: TRUE, b: TRUE}) and implies (the trap:
//     PLE yields {a: FALSE, b: TRUE}, not v1's FALSE-first {a: FALSE,
//     b: FALSE} — both models are valid).
//   - Hypergraph: stats oracle (calibrated decisions, propagations >= 10),
//     forced subset {a, b, c, g, h} TRUE, and reference validity; the
//     don't-care region legitimately differs from v1 under PLE. The wall-clock
//     `slowTime > fastTime * 1000n` assertion was deleted with v1; the
//     hypergraph is proven by the stats oracle instead.
//   - Enumeration (describe('getAllSolutions')): the v1
//     `bruteForceAllSolutions` tests ported with order-insensitive
//     comparison (assertModelListsEqual), per-model shape assertions,
//     count cross-checks against the reference enumerator, the empty-formula
//     corner cases (and() -> [{}], or() -> []), the PLE-disabled regression
//     (or('a','b') must enumerate all three models — PLE would pin {a: TRUE,
//     b: TRUE} first and silently drop two), and the 40-variable smoke test
//     (v1's array-length-cap regression class).

import { describe, it } from 'node:test';
import assert from 'node:assert';
import * as publicApi from '../src';
import { and, getAllSolutions, getSolution, implies, not, or, Value, xor } from '../src';
import type { Variable, VariablePriority } from '../src';
import {
  assertModelListsEqual,
  assertModelShape,
  expressionValue,
  hypergraphFormula,
  hypergraphPrereqs,
  modelKey,
  referenceModels,
} from './helpers';

// Decisions remaining after the hypergraph's UP+PLE fixpoint, calibrated in
// the previous task (task-101f, HYPERGRAPH_DECISIONS in test/solver.spec.ts).
// The pinned global-sweep PLE assigns the whole chain except the two
// zero-occurrence don't-cares e and n (every clause mentioning them is
// satisfied before they could become pure), so the search loop decides those
// two FALSE-first. The owner-approved Design § Testing correction in
// task-f746 now requires this actual Phase-1 value, not the former zero claim.
const HYPERGRAPH_DECISIONS = 2;

// v1's `selectNextVar` ported to the v2 `variablePriority` contract per
// Design § Branching Heuristics: `assignments[var] === Value.UNSET` checks
// become `=== undefined` against the partial record, and the candidates
// filter is replaced by the `unassigned` parameter. The "rank by satisfied
// parents, branch TRUE on ready nodes" logic is otherwise unchanged.
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
      const model = getSolution(and('a', 'b'));
      assert.deepStrictEqual(model, { a: Value.TRUE, b: Value.TRUE });
      assertModelShape(model, and('a', 'b'));
      assert.strictEqual(expressionValue(and('a', 'b'), model), Value.TRUE);
    });

    it('supports or operator (PLE forces the oneOf case)', () => {
      const formula = or('a', 'b');
      const model = getSolution(formula);
      // The plain clause (a ∨ b) makes both literals pure, so scoped PLE
      // forces {a: TRUE, b: TRUE} — no search, no choices.
      assert.deepStrictEqual(model, { a: Value.TRUE, b: Value.TRUE });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    });

    it('supports not operator (exact model)', () => {
      const model = getSolution(not('b'));
      assert.deepStrictEqual(model, { b: Value.FALSE });
      assertModelShape(model, not('b'));
      assert.strictEqual(expressionValue(not('b'), model), Value.TRUE);
    });

    it('supports implies operator (PLE trap: {a: FALSE, b: TRUE})', () => {
      const formula = implies('a', 'b');
      const model = getSolution(formula);
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
      const model = getSolution(formula);
      // Symmetric gate encodings make PLE inert; FALSE-first/index-order
      // branching reproduces v1's {a: false, b: true}.
      assert.deepStrictEqual(model, { a: Value.FALSE, b: Value.TRUE });
      assertModelShape(model, formula);
      assert.strictEqual(expressionValue(formula, model), Value.TRUE);
    });

    it('supports complex clauses (exact unique model)', () => {
      const formula = and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')));
      const model = getSolution(formula);
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
      assert.deepStrictEqual(getSolution(and()), {});
      assert.strictEqual(getSolution(or()), null);
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
        };
        const model = getSolution(hypergraphFormula(), { assumptions: { h: Value.TRUE }, stats });

        assert.ok(model !== null);
        // Stats oracle replaces the deleted wall-clock assertion: with
        // { h: TRUE } asserted at level 0, unit propagation forces
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
        // The don't-care region legitimately differs from v1 under PLE;
        // reference evaluation of the full model is the ground truth.
        assert.strictEqual(expressionValue(hypergraphFormula(), model), Value.TRUE);
      });

      it('honors a domain variablePriority with equal forced subset', () => {
        const defaultModel = getSolution(hypergraphFormula(), { assumptions: { h: Value.TRUE } });
        const candidates: Variable[][] = [];
        const customModel = getSolution(hypergraphFormula(), {
          assumptions: { h: Value.TRUE },
          variablePriority: (unassigned, assignments) => {
            candidates.push([...unassigned]);
            return visitOrder(unassigned, assignments);
          },
        });

        assert.deepEqual(candidates, [['e', 'n'], ['n']], 'two ordinary completion decisions');
        assert.ok(defaultModel !== null);
        assert.ok(customModel !== null);
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
        b: Value.FALSE,
      });
    });

    it('propagates assumptions immediately at level zero', () => {
      // (¬a ∨ b) with a assumed TRUE forces b=TRUE before any decision.
      assert.deepStrictEqual(getSolution(implies('a', 'b'), { assumptions: { a: Value.TRUE } }), {
        a: Value.TRUE,
        b: Value.TRUE,
      });
    });

    it('returns null fast when assumptions contradict the formula', () => {
      assert.strictEqual(
        getSolution(implies('a', 'b'), { assumptions: { a: Value.TRUE, b: Value.FALSE } }),
        null,
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
      };
      const model = getSolution(and('a', 'b'), { stats });
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
      const model = getSolution(xor('a', 'b'), { variablePriority: hook });
      assert.strictEqual(hookCalls, 1);
      assert.ok(model !== null);
      assertModelShape(model, xor('a', 'b'));
      assert.strictEqual(expressionValue(xor('a', 'b'), model), Value.TRUE);

      const totalAfterXor = hookCalls;
      const silentHook: VariablePriority = () => {
        hookCalls += 1;
        return null;
      };
      assert.deepStrictEqual(getSolution(and('a', 'b'), { variablePriority: silentHook }), {
        a: Value.TRUE,
        b: Value.TRUE,
      });
      // The all-unit formula needs no decisions, so the hook is never called.
      assert.strictEqual(hookCalls, totalAfterXor);
    });
  });

  describe('unsolvable', () => {
    it('returns null for the unsolvable worked example', () => {
      assert.strictEqual(
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
        null,
      );
    });
  });
});

describe('getAllSolutions', () => {
  describe('solvable', () => {
    it('supports and operator (exact model)', () => {
      const formula = and('a', 'b');
      const models = getAllSolutions(formula);
      assertModelListsEqual(models, [{ a: Value.TRUE, b: Value.TRUE }]);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports or operator — enumerates all three models (PLE-unsoundness regression)', () => {
      const formula = or('a', 'b');
      const models = getAllSolutions(formula);
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
      assertModelListsEqual(getAllSolutions(formula), [
        { v: Value.FALSE, a: Value.TRUE },
        { v: Value.TRUE, a: Value.FALSE },
        { v: Value.TRUE, a: Value.TRUE },
      ]);
    });

    it('supports not operator (exact model)', () => {
      const formula = not('b');
      const models = getAllSolutions(formula);
      assertModelListsEqual(models, [{ b: Value.FALSE }]);
      for (const model of models) {
        assertModelShape(model, formula);
        assert.strictEqual(expressionValue(formula, model), Value.TRUE);
      }
    });

    it('supports implies operator (all three models)', () => {
      const formula = implies('a', 'b');
      const models = getAllSolutions(formula);
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
      const models = getAllSolutions(formula);
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
      const models = getAllSolutions(formula);
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

  describe('edge cases', () => {
    it('implements the v1-compatible empty-formula semantics', () => {
      // and(): the empty conjunction has one model, {}; the blocking clause
      // over zero named variables is the empty clause — terminal UNSAT for
      // enumeration after the first iteration.
      assert.deepStrictEqual(getAllSolutions(and()), [{}]);
      // or(): the empty disjunction compiles to the empty clause.
      assert.deepStrictEqual(getAllSolutions(or()), []);
    });

    it('returns [] immediately for a levelZeroUnsat formula', () => {
      // and(or(), 'a') compiles to the empty clause plus a unit clause:
      // levelZeroUnsat short-circuits before any solve.
      assert.deepStrictEqual(getAllSolutions(and(or(), 'a')), []);
    });

    it('enumerates a 40-variable chain without an array-length cap', () => {
      // v1's bruteForceAllSolutions materialized all 2^n assignments and
      // threw RangeError at n >= 32; the chain of 40 implication clauses has
      // exactly 41 models (a TRUE prefix), so this is output-sensitive: one
      // solve per model, no 2^n materialization.
      const prereqClauses: Array<ReturnType<typeof implies>> = [];
      for (let index = 2; index <= 40; index += 1) {
        prereqClauses.push(implies(`v${index}`, `v${index - 1}`));
      }
      const formula = and(...prereqClauses);
      const models = getAllSolutions(formula);

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
      const models = getAllSolutions(or('a', 'b'), { assumptions: { a: Value.UNSET } });
      assertModelListsEqual(models, [
        { a: Value.FALSE, b: Value.TRUE },
        { a: Value.TRUE, b: Value.FALSE },
        { a: Value.TRUE, b: Value.TRUE },
      ]);
    });

    it('filters enumeration to models extending the assumptions', () => {
      const models = getAllSolutions(implies('a', 'b'), { assumptions: { b: Value.FALSE } });
      assertModelListsEqual(models, [{ a: Value.FALSE, b: Value.FALSE }]);
    });

    it('returns [] when the assumptions contradict the formula', () => {
      assert.deepStrictEqual(getAllSolutions(and('a'), { assumptions: { a: Value.FALSE } }), []);
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
      };
      const models = getAllSolutions(or('a', 'b'), { stats });
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
      const models = getAllSolutions(or('a', 'b'), { variablePriority: hook });

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

describe('public surface', () => {
  it('exports exactly the v2 symbol list', () => {
    // Runtime values: the frozen formula API plus getSolution and
    // getAllSolutions. Types (BooleanExpr, Variable, VariableAssignments,
    // SolverStats, SolveOptions, VariablePriority) are exported by name but
    // erased at runtime; no v1 entry point (bruteForceAllSolutions,
    // getInitialAssignments, selectNextVar) may survive.
    assert.deepStrictEqual(Object.keys(publicApi).sort(), [
      'Value',
      'and',
      'getAllSolutions',
      'getSolution',
      'implies',
      'not',
      'or',
      'xor',
    ]);
  });
});
