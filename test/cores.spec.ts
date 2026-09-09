// Failed-assumption UNSAT cores (Design § UNSAT Cores). Targeted witnesses
// with exact known cores plus a seeded brute-force soundness battery:
// core ⊆ assumptions and base ∧ core UNSAT for every UNSAT answer, with `{}`
// permitted only for no-assumption or assumption-independent proofs. The
// generic oracles in helpers.ts (assertSoundCore) also run inside the
// property.spec.ts and incremental-*.spec.ts harnesses; this file pins the
// hand-computed cases and the dedicated seeded stream.

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
  and,
  atLeast,
  atMost,
  createSolver,
  getSolution,
  implies,
  not,
  or,
  Value,
  xor,
} from '../src/index.js';
import type { BooleanExpr, VariableAssignments } from '../src/index.js';
import { getVariables } from '../src/expr.js';
import {
  assertSoundCore,
  expectSatModel,
  mulberry32,
  randomAssumptions,
  randomFormula,
  referenceModels,
} from './helpers.js';

// (¬a ∨ x) ∧ (¬x ∨ b): the tainted-implication witness. Under
// {a: TRUE, b: FALSE} the implied x is NOT an assumption; the walk resolves
// through it and collects exactly the two supplied assumption leaves.
const taintedImplication = () => and(implies('a', 'x'), implies('x', 'b'));

// (¬a∨x∨t) ∧ (¬a∨x∨¬t) ∧ (¬x∨t) ∧ (¬x∨¬t): the probe witness. Under
// a=TRUE, propagation and learning derive x and ¬x from a alone; the core is
// exactly {a: TRUE} even though x and t participate in every conflict.
const probeChain = () =>
  and(
    or(not('a'), 'x', 't'),
    or(not('a'), 'x', not('t')),
    or(not('x'), 't'),
    or(not('x'), not('t')),
  );

describe('UNSAT cores: seeded rejection', () => {
  it('single-shot: the rejected assumption seeds the core even though it never entered the trail', () => {
    // and('a') forces a=TRUE at root; the explaining unit clause is SATISFIED
    // by that assignment, so walking it alone would yield a bogus empty core.
    assert.deepStrictEqual(getSolution(and('a'), { assumptions: { a: Value.FALSE } }), {
      status: 'unsat',
      core: { a: Value.FALSE },
    });
  });

  it('incremental: an assumption found already-false at the prefix is the seed', () => {
    const solver = createSolver(and('a'));
    assert.deepStrictEqual(solver.solve({ a: Value.FALSE }), {
      status: 'unsat',
      core: { a: Value.FALSE },
    });
    // The handle stays usable; the rejection never poisons the base.
    assert.deepStrictEqual(solver.solve(), { status: 'sat', model: { a: Value.TRUE } });
  });

  it('seeds the FIRST rejected assumption when several contradict the base', () => {
    // and('a', 'b') under {a: FALSE, b: FALSE}: each singleton core is sound
    // (base ∧ ¬a is already UNSAT); the walk reports the first rejection.
    assert.deepStrictEqual(
      getSolution(and('a', 'b'), { assumptions: { a: Value.FALSE, b: Value.FALSE } }),
      {
        status: 'unsat',
        core: { a: Value.FALSE },
      },
    );
    assert.deepStrictEqual(
      getSolution(and('a', 'b'), { assumptions: { b: Value.FALSE, a: Value.FALSE } }),
      { status: 'unsat', core: { b: Value.FALSE } },
    );
  });
});

describe('UNSAT cores: tainted implications and learned-unit reasons', () => {
  for (const mode of ['single-shot', 'incremental'] as const) {
    it(`${mode}: {a: TRUE, b: FALSE} is the core and the implied x is never collected`, () => {
      const expr = taintedImplication();
      const assumptions = { a: Value.TRUE, b: Value.FALSE };
      const result =
        mode === 'single-shot'
          ? getSolution(expr, { assumptions })
          : createSolver(expr).solve(assumptions);
      assert.deepStrictEqual(result, { status: 'unsat', core: assumptions });
    });

    it(`${mode}: the probe chain cores on exactly {a: TRUE}`, () => {
      const expr = probeChain();
      const result =
        mode === 'single-shot'
          ? getSolution(expr, { assumptions: { a: Value.TRUE } })
          : createSolver(expr).solve({ a: Value.TRUE });
      assert.deepStrictEqual(result, { status: 'unsat', core: { a: Value.TRUE } });
    });
  }

  it('incremental: a learned root unit explains the rejected assumption on the replayed prefix', () => {
    // (¬a∨x) ∧ (¬a∨¬x): a=TRUE learns the unit ¬a; the NEXT call's prefix
    // rejection walks that learned reason and still cores on {a: TRUE}.
    const solver = createSolver(and(or(not('a'), 'x'), or(not('a'), not('x'))));
    assert.deepStrictEqual(solver.solve({ a: Value.TRUE }), {
      status: 'unsat',
      core: { a: Value.TRUE },
    });
    assert.deepStrictEqual(solver.solve({ a: Value.TRUE }), {
      status: 'unsat',
      core: { a: Value.TRUE },
    });
  });
});

describe('UNSAT cores: empty-core permission', () => {
  it('no assumptions supplied: base UNSAT cores on {}', () => {
    assert.deepStrictEqual(getSolution(and('a', not('a'))), { status: 'unsat', core: {} });
    assert.deepStrictEqual(getSolution(or()), { status: 'unsat', core: {} });
    assert.deepStrictEqual(createSolver(and('a', not('a'))).solve(), {
      status: 'unsat',
      core: {},
    });
    assert.deepStrictEqual(createSolver(or()).solve(), { status: 'unsat', core: {} });
  });

  it('assumption-independent proofs permit {} even with valid supplied assumptions', () => {
    // a ∧ ¬a is UNSAT regardless of b; b is never needed by the proof.
    const expr = and('a', not('a'), or('b', not('b')));
    assert.deepStrictEqual(getSolution(expr, { assumptions: { b: Value.TRUE } }), {
      status: 'unsat',
      core: {},
    });
    const solver = createSolver(expr);
    assert.deepStrictEqual(solver.solve({ b: Value.TRUE }), { status: 'unsat', core: {} });
  });

  it('cached base UNSAT keeps the {} core across later valid calls', () => {
    const solver = createSolver(
      and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'), or(not('a'), not('b'))),
    );
    assert.deepStrictEqual(solver.solve({ a: Value.TRUE }), { status: 'unsat', core: {} });
    assert.deepStrictEqual(solver.solve({ b: Value.FALSE }), { status: 'unsat', core: {} });
  });
});

describe('UNSAT cores: seeded soundness battery', () => {
  // A dedicated stream, disjoint from the preserved 512-seed property harness
  // streams (ASSUMPTION_SEED_BASE 100_000) and the incremental stream
  // (400_000): this battery uses 700_000 + draw.
  const CORE_SEED_BASE = 700_000;
  const DRAWS_PER_FORMULA = 2;

  it('core ⊆ assumptions and base ∧ core brute-force UNSAT on every seeded draw', (t) => {
    let formulas = 0;
    let unsatAnswers = 0;
    for (let seed = 0; seed < 128; seed += 1) {
      const { expr } = randomFormula(mulberry32(seed), {
        maxDepth: 3,
        maxWidth: 4,
        maxVariables: 8,
      });
      const reference = referenceModels(expr);
      const variableCount = getVariables(expr).size;
      if (reference.length === 0 || reference.length === 2 ** variableCount) {
        continue; // need a SAT base that is not a tautology for both draw kinds
      }
      formulas += 1;
      for (let draw = 0; draw < DRAWS_PER_FORMULA; draw += 1) {
        const assumptions = randomAssumptions(
          mulberry32(CORE_SEED_BASE + seed * DRAWS_PER_FORMULA + draw),
          expr,
          { kind: 'contradictory' },
        );
        // Single-shot (PLE-enabled) and incremental paths agree on the
        // verdict and each produce a sound core.
        for (const result of [
          getSolution(expr, { assumptions }),
          createSolver(expr).solve(assumptions),
        ]) {
          assert.strictEqual(result.status, 'unsat', `seed ${seed} draw ${draw} verdict`);
          assertSoundCore(`seed ${seed} draw ${draw}`, reference, assumptions, result.core);
          // A SAT base with contradictory assumptions must name at least one
          // failed assumption: the empty core is never an escape hatch here.
          assert.ok(
            Object.keys(result.core).length > 0,
            `seed ${seed} draw ${draw}: assumption-dependent UNSAT has a non-empty core`,
          );
          unsatAnswers += 1;
        }
      }
      // A consistent draw never yields UNSAT (and hence never a bogus core).
      const consistent = randomAssumptions(
        mulberry32(CORE_SEED_BASE + seed * DRAWS_PER_FORMULA + 9),
        expr,
        { kind: 'consistent', maxAssumptions: 3 },
      );
      assert.ok(
        reference.some((model) =>
          Object.entries(consistent).every(
            ([name, value]) => Object.hasOwn(model, name) && model[name] === value,
          ),
        ),
      );
      expectSatModel(getSolution(expr, { assumptions: consistent }));
      expectSatModel(createSolver(expr).solve(consistent));
    }
    assert.ok(formulas > 100, 'the battery covers a non-trivial seeded corpus');
    assert.ok(unsatAnswers > 0, 'the battery actually produced UNSAT cores');
    t.diagnostic(`${formulas} formulas; ${unsatAnswers} UNSAT cores verified`);
  });

  it('base-UNSAT formulas permit {} and never invent assumptions', () => {
    for (let seed = 0; seed < 32; seed += 1) {
      // and(x, not(x), ...) is UNSAT independent of the rest of the formula.
      const { expr: inner } = randomFormula(mulberry32(CORE_SEED_BASE + seed), {
        maxDepth: 2,
        maxWidth: 3,
        maxVariables: 6,
      });
      const expr: BooleanExpr = and('zz', not('zz'), inner);
      const assumptions: VariableAssignments = { zz: Value.TRUE };
      for (const result of [
        getSolution(expr, { assumptions }),
        createSolver(expr).solve(assumptions),
      ]) {
        assert.strictEqual(result.status, 'unsat');
        assertSoundCore(`base-unsat seed ${seed}`, referenceModels(expr), assumptions, result.core);
      }
    }
  });
});

describe('UNSAT cores: cardinality constraints', () => {
  it('pairwise AMO: both violating assumptions are the exact core, in both modes', () => {
    // The pairwise clause (¬a ∨ ¬b) is falsified only when both hold.
    const expr = atMost(1, 'a', 'b');
    const assumptions = { a: Value.TRUE, b: Value.TRUE };
    assert.deepStrictEqual(getSolution(expr, { assumptions }), {
      status: 'unsat',
      core: { a: Value.TRUE, b: Value.TRUE },
    });
    assert.deepStrictEqual(createSolver(expr).solve(assumptions), {
      status: 'unsat',
      core: { a: Value.TRUE, b: Value.TRUE },
    });
  });

  it('sequential counter: the core names only the violated capacity, never the free variable', () => {
    // atLeast(2, seven) rewrites to a Sinz atMost(5, ¬…) counter: six FALSE
    // assumptions leave one free variable, which can satisfy at most one —
    // UNSAT. The core stays within the supplied assumptions (any five of the
    // six would still be sound; only subset+soundness are asserted).
    const expr = atLeast(2, 'a', 'b', 'c', 'd', 'e', 'f', 'g');
    const assumptions: VariableAssignments = {
      a: Value.FALSE,
      b: Value.FALSE,
      c: Value.FALSE,
      d: Value.FALSE,
      e: Value.FALSE,
      f: Value.FALSE,
    };
    for (const result of [
      getSolution(expr, { assumptions }),
      createSolver(expr).solve(assumptions),
    ]) {
      assert.strictEqual(result.status, 'unsat');
      assertSoundCore('Sinz atLeast core', referenceModels(expr), assumptions, result.core);
      assert.ok(Object.keys(result.core).length > 0, 'the violation is assumption-driven');
    }
    // And with one more variable free the base is satisfiable: the core must
    // never accuse g.
    const satisfiable = getSolution(expr, { assumptions: { a: Value.FALSE } });
    assert.strictEqual(satisfiable.status, 'sat');
  });

  it('nested totalizer thresholds core through their reified outputs under not/or', () => {
    // (¬atLeast(1, a, b) ∨ c): the reified output u_1 is derived from a, so
    // under {a: TRUE, c: FALSE} the walk resolves through the totalizer to
    // exactly the two supplied assumption leaves — never an auxiliary.
    const expr = or(not(atLeast(1, 'a', 'b')), 'c');
    const assumptions = { a: Value.TRUE, c: Value.FALSE };
    assert.deepStrictEqual(getSolution(expr, { assumptions }), {
      status: 'unsat',
      core: { a: Value.TRUE, c: Value.FALSE },
    });
    assert.deepStrictEqual(createSolver(expr).solve(assumptions), {
      status: 'unsat',
      core: { a: Value.TRUE, c: Value.FALSE },
    });
    // atMost under not, the other polarity: ¬atMost(1, a, b) ⟺ a ∧ b. The
    // reified totalizer output is a base-derived root unit that forces b, so
    // under {a: TRUE, b: FALSE} the conflict accuses b alone (sound: b=FALSE
    // already makes ¬atMost(1, a, b) unsatisfiable) — a is never collected.
    const dual = and(not(atMost(1, 'a', 'b')));
    const dualAssumptions = { a: Value.TRUE, b: Value.FALSE };
    assert.deepStrictEqual(getSolution(dual, { assumptions: dualAssumptions }), {
      status: 'unsat',
      core: { b: Value.FALSE },
    });
    assert.deepStrictEqual(createSolver(dual).solve(dualAssumptions), {
      status: 'unsat',
      core: { b: Value.FALSE },
    });
  });
});

describe('UNSAT cores: stats interplay', () => {
  it('zero-fills sparse stats and still reports the exact core', () => {
    const stats = { decisions: 12345 };
    const result = getSolution(and('a'), {
      assumptions: { a: Value.FALSE },
      stats,
    });
    assert.deepStrictEqual(result, { status: 'unsat', core: { a: Value.FALSE } });
    assert.deepStrictEqual(stats, {
      decisions: 0,
      propagations: 1, // the constructor unit enqueue, in the single-shot scope
      conflicts: 1,
      restarts: 0,
      learnedClauses: 0,
      learnedClausesCurrent: 0,
      learnedLiterals: 0,
      minimizedLiterals: 0,
    });
  });

  it('the options bag takes only stats at this step', () => {
    const solver = createSolver(xor('a', 'b'));
    assert.deepStrictEqual(solver.solve({ a: Value.TRUE, b: Value.TRUE }), {
      status: 'unsat',
      core: { a: Value.TRUE, b: Value.TRUE },
    });
  });
});
