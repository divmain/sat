import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, isNeg, litValue, negLit, posLit, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, not, or, Value } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import {
  assertWatchListsSurvive,
  cnfToExpr,
  expressionValue,
  mulberry32,
  phpCnf,
  random3Cnf,
  referenceModels,
  snapshotWatches,
  watchesClause,
} from './helpers';

function cnf(names: string[], clauses: number[][]): CompiledCnf {
  assert.deepEqual(names, [...names].sort(), 'fixtures use sorted named-variable indices');
  return {
    numVars: names.length,
    numNamedVars: names.length,
    clauses: clauses.map((lits) => ({
      lits: [...lits].sort((a, b) => a - b),
      learned: false,
      activity: 0,
      lbd: 0,
    })),
    indexToName: names,
    nameToIndex: new Map(names.map((name, index) => [name, index])),
    levelZeroUnsat: false,
  };
}

function decide(solver: Solver, lit: number): void {
  assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
  solver.newDecisionLevel();
  assert.strictEqual(solver.enqueue(lit, null), true);
}

// Reconstruct the implication graph independently of analyze(). In particular,
// a non-null reason must be a registered clause that was UNIT at enqueue time,
// not just a clause containing the assigned literal. Pending propagation is
// allowed for operation-local fixtures; forged reasons/trail/queue state is not.
function assertReasonGraph(solver: Solver, conflict?: Clause): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (let index = 0; index < solver.trail.length; index += 1) {
    const lit = solver.trail[index];
    const variable = varOf(lit);
    assert.strictEqual(prefix[variable], Value.UNSET);
    const level = solver.trailLim.filter((boundary) => boundary <= index).length;
    assert.strictEqual(solver.level[variable], level);
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.ok(solver.clauses.includes(reason), 'reason has canonical database identity');
      assert.ok(reason.lits.includes(lit), 'reason contains the implied literal');
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(
            litValue(other, prefix),
            Value.FALSE,
            'antecedent precedes implication',
          );
        }
      }
    } else if (level > 0) {
      assert.strictEqual(index, solver.trailLim[level - 1], 'one decision at the start of a level');
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepEqual(prefix, solver.assigns);
  if (conflict !== undefined) {
    assert.ok(solver.clauses.includes(conflict));
    assert.ok(conflict.lits.every((lit) => litValue(lit, prefix) === Value.FALSE));
  }
}

function assertWatchMembership(solver: Solver): void {
  for (const list of solver.watches) {
    assert.strictEqual(new Set(list).size, list.length, 'no repeated entry within a watch list');
    assert.ok(list.every((entry) => solver.clauses.includes(entry.clause)));
  }
  for (const list of solver.binaryWatches) {
    assert.strictEqual(
      new Set(list).size,
      list.length,
      'no repeated entry within a binary watch list',
    );
    assert.ok(list.every((entry) => solver.clauses.includes(entry.clause)));
  }
  for (const clause of solver.clauses) {
    const watched: number[] = [];
    for (let lit = 0; lit < solver.watches.length; lit += 1) {
      if (watchesClause(solver.watches[lit], clause)) {
        watched.push(lit);
      }
      if (solver.binaryWatches[lit].some((entry) => entry.clause === clause)) {
        watched.push(lit);
      }
    }
    const expected = clause.lits.length < 2 ? [] : clause.lits.slice(0, 2).sort((a, b) => a - b);
    assert.deepEqual(
      watched,
      expected,
      'exact watch membership; structural units are never watched',
    );
  }
}

function assertFixpoint(solver: Solver): void {
  assert.strictEqual(solver.qhead, solver.trail.length);
  for (const clause of solver.clauses) {
    if (!clause.lits.some((lit) => litValue(lit, solver.assigns) === Value.TRUE)) {
      assert.ok(
        clause.lits.filter((lit) => litValue(lit, solver.assigns) === Value.UNSET).length >= 2,
        'no pending unit or conflict before an eager-search decision',
      );
    }
  }
}

// Small-fixture truth tables check unconditional entailment, including models
// that violate the assumptions used to expose a conflict. This is independent
// of the resolution walk and does not assume the solver's verdict is correct.
function assertEntailed(base: CompiledCnf, learned: Clause): void {
  assert.ok(base.numVars <= 8, 'truth-table checks are deliberately small');
  for (let mask = 0; mask < 2 ** base.numVars; mask += 1) {
    const satisfied = (clause: Clause) =>
      clause.lits.some((lit) => ((mask >> varOf(lit)) & 1) === (isNeg(lit) ? 0 : 1));
    if (base.clauses.every(satisfied)) {
      assert.ok(satisfied(learned), `learned clause must hold in base model ${mask}`);
    }
  }
}

// Observes real search operations without changing their inputs or outputs.
class TracedSolver extends Solver {
  readonly analyses: Array<{ from: number; learned: number[]; backjumpLevel: number }> = [];
  readonly jumps: Array<{ from: number; to: number; retained: number[] }> = [];
  readonly decisions: number[] = [];

  override enqueue(lit: number, reason: Clause | null): boolean {
    const wasUnset = this.assigns[varOf(lit)] === Value.UNSET;
    const result = super.enqueue(lit, reason);
    // Root enqueues during construction occur before subclass fields exist,
    // and are not decisions. Implications/learned assertions have a reason.
    if (result && wasUnset && reason === null && this.trailLim.length > 0) {
      this.decisions.push(lit);
    }
    return result;
  }

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    assertReasonGraph(this, conflict);
    const result = super.analyze(conflict);
    this.analyses.push({
      from: this.trailLim.length,
      learned: [...result.learned.lits],
      backjumpLevel: result.backjumpLevel,
    });
    return result;
  }

  override cancelUntil(level: number): void {
    const from = this.trailLim.length;
    const watches = snapshotWatches(this.watches, this.binaryWatches);
    super.cancelUntil(level);
    assertWatchListsSurvive(
      this.watches,
      this.binaryWatches,
      watches,
      'cancellation must not rebuild watches',
    );
    this.jumps.push({ from, to: this.trailLim.length, retained: [...this.trail] });
  }
}

describe('Solver first-UIP conflict analysis', () => {
  const resolutionWitness = () =>
    cnf(
      ['x1', 'x2', 'x3', 'x4'],
      [
        [negLit(0), posLit(1)],
        [negLit(0), posLit(2)],
        [negLit(1), negLit(2), posLit(3)],
        [negLit(2), negLit(3)],
      ],
    );

  it('derives exactly (¬x1) from the ticket (a) unit-reason graph', () => {
    const base = resolutionWitness();
    const [A, B, C, D] = base.clauses;
    const solver = new Solver(base);
    decide(solver, posLit(0));
    assert.strictEqual(solver.enqueue(posLit(1), A), true);
    assert.strictEqual(solver.enqueue(posLit(2), B), true);
    assert.strictEqual(solver.enqueue(posLit(3), C), true);
    assertReasonGraph(solver, D);
    assert.strictEqual(
      solver.qhead,
      0,
      'this fixture drives enqueues, not the watch-list scheduler',
    );

    // D resolve C on x4 -> (¬x2∨¬x3); resolve B on x3 -> (¬x2∨¬x1);
    // resolve A on x2 -> (¬x1). Three resolutions reach the first UIP x1.
    const { learned, backjumpLevel } = solver.analyze(D);
    assert.deepEqual(learned.lits, [negLit(0)]);
    assert.strictEqual(backjumpLevel, 0);
    assert.strictEqual(learned.learned, true);
    assertEntailed(base, learned);
    assert.deepEqual(
      base.clauses.map((clause) => clause.activity),
      [1, 1, 1, 1],
    );
    assert.strictEqual(learned.activity, 0);
    assert.deepEqual(Array.from(solver.activity), [1, 1, 1, 1]);
    assert.strictEqual(solver.stats.conflicts, 0, 'analysis does not count propagation conflicts');
    assert.strictEqual(solver.stats.learnedClauses, 0, 'analysis alone does not insert a clause');
  });

  it('also derives (¬x1) from the actual, opposite-x4 propagation order', () => {
    const base = resolutionWitness();
    const solver = new Solver(base);
    assert.strictEqual(solver.propagate(), null);
    decide(solver, posLit(0));
    const conflict = solver.propagate();
    assert.strictEqual(conflict, base.clauses[2]);
    assert.deepEqual(solver.trail, [posLit(0), posLit(2), posLit(1), negLit(3)]);
    assert.ok(
      solver.qhead < solver.trail.length,
      'analysis must include enqueued, unprocessed literals',
    );
    assertReasonGraph(solver, base.clauses[2]);
    assert.ok(conflict !== null);

    // C resolve D on x4 gives the same (¬x2∨¬x3), then A and B give (¬x1).
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepEqual(learned.lits, [negLit(0)]);
    assert.strictEqual(backjumpLevel, 0);
    assertEntailed(base, learned);
    assert.deepEqual(
      base.clauses.map((clause) => clause.activity),
      [1, 1, 1, 1],
    );
    assert.strictEqual(solver.stats.conflicts, 1, 'the conflict was counted only by propagate');
    assert.strictEqual(solver.stats.propagations, 3);
    // x2,x3,x4 disappear by resolution; repeated encounters with x1/x3
    // still bump only once. This is not learned-clause-only activity.
    assert.deepEqual(Array.from(solver.activity), [1, 1, 1, 1]);
  });

  it('stops at implied x2 in ticket (b), an explicitly analysis-local, pending-propagation graph', () => {
    const base = cnf(
      ['free1', 'free2', 'v1', 'x1', 'x2'],
      [
        [negLit(3), posLit(4)],
        [negLit(4), negLit(2)],
      ],
    );
    const [E, F] = base.clauses;
    const solver = new Solver(base);
    // NOT a solve() trace: eager propagation of v1 would imply ¬x2, ¬x1
    // immediately. The ticket allows direct operation driving. Leave the
    // queue untouched and verify the narrower analyze preconditions instead.
    decide(solver, posLit(2));
    decide(solver, posLit(0));
    decide(solver, posLit(1));
    decide(solver, posLit(3));
    assert.strictEqual(solver.enqueue(posLit(4), E), true);
    assertReasonGraph(solver, F);
    assert.strictEqual(solver.qhead, 0);
    assert.strictEqual(solver.trailLim.length, 4);

    // F already has exactly one level-4 literal (¬x2). Zero resolutions:
    // resolving E would go PAST the first UIP to the decision x1.
    for (let analysis = 1; analysis <= 2; analysis += 1) {
      const { learned, backjumpLevel } = solver.analyze(F);
      assert.deepEqual(learned.lits, [negLit(4), negLit(2)]);
      assert.strictEqual(backjumpLevel, 1);
      assertEntailed(base, learned);
      assert.strictEqual(E.activity, 0, 'the UIP reason must not be resolved with');
      assert.strictEqual(F.activity, analysis, 'the conflict seed is used once per analysis');
      assert.strictEqual(
        solver.addLearnedClause(learned),
        F,
        'reuse the canonical original clause',
      );
      assert.strictEqual(
        F.learned,
        false,
        'rediscovery must not turn an original into a learned clause',
      );
      assert.strictEqual(solver.clauses.length, 2);
      assert.strictEqual(solver.stats.learnedClauses, 0);
      assert.strictEqual(solver.stats.learnedClausesCurrent, 0);
      assertWatchMembership(solver);
    }

    const watches = snapshotWatches(solver.watches, solver.binaryWatches);
    solver.cancelUntil(1);
    assert.strictEqual(solver.trailLim.length, 1, 'backjump 4→1 skips levels 2 and 3');
    assert.deepEqual(solver.trail, [posLit(2)]);
    assertWatchListsSurvive(
      solver.watches,
      solver.binaryWatches,
      watches,
      'backjump does not rebuild watches',
    );
    assert.strictEqual(solver.enqueue(negLit(4), F), true);
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.level[4], 1);
    assert.strictEqual(solver.reason[4], F);
    assert.strictEqual(solver.reason[3], E);
    assertReasonGraph(solver);
    assertWatchMembership(solver);
  });

  it('confirms why ticket (b) cannot occur after exhaustive propagation', () => {
    const base = cnf(
      ['free1', 'free2', 'v1', 'x1', 'x2'],
      [
        [negLit(3), posLit(4)],
        [negLit(4), negLit(2)],
      ],
    );
    const solver = new Solver(base);
    decide(solver, posLit(2));
    assert.strictEqual(solver.propagate(), null);
    assert.deepEqual(solver.trail, [posLit(2), negLit(4), negLit(3)]);
    assert.strictEqual(solver.level[3], 1);
    assert.strictEqual(solver.level[4], 1);
    assert.strictEqual(
      solver.enqueue(posLit(3), null),
      false,
      'x1 is no longer an available decision',
    );
    assertReasonGraph(solver);
    assertFixpoint(solver);
  });

  it('rejects root analysis and a non-conflicting clause rather than inventing a learned clause', () => {
    const base = cnf(['a', 'b'], [[posLit(0), posLit(1)]]);
    const solver = new Solver(base);
    assert.throws(() => solver.analyze(base.clauses[0]), /nonzero decision level/);
    decide(solver, negLit(0));
    assert.throws(() => solver.analyze(base.clauses[0]), /falsified/);
    assert.strictEqual(solver.stats.learnedClauses, 0);
  });
});

describe('Solver learned clauses and non-chronological search', () => {
  it('performs a genuine eager-search backjump 4→1, stopping before the decision UIP', () => {
    // Unlike ticket (b), v1 alone does not imply ¬x2 here. At level 4, x1
    // implies x2; the dedicated binary lists drain FIRST, so the binary
    // (¬x2∨t) implies t=TRUE before the long (¬x2∨¬t∨¬v1) is visited and
    // conflicts. Resolving t's reason (the binary) still gives (¬x2∨¬v1),
    // whose first UIP is implied x2 and whose assertion level is 1 — the
    // learned clause and backjump are unchanged; only t's implied polarity
    // (and thereby its saved phase) differs from the combined-list order.
    const base = cnf(
      ['free1', 'free2', 't', 'v1', 'x1', 'x2'],
      [
        [negLit(4), posLit(5)],
        [negLit(5), posLit(2)],
        [negLit(5), negLit(2), negLit(3)],
      ],
    );
    const script = ['v1', 'free1', 'free2', 'x1'];
    let calls = 0;
    const solver = new TracedSolver(base, {
      variablePriority: (unassigned) => {
        assertFixpoint(solver);
        const name = script[calls++];
        if (name === undefined) {
          return null;
        }
        assert.ok(unassigned.includes(name));
        return [name, true];
      },
    });
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.analyses, [
      { from: 4, learned: [negLit(5), negLit(3)], backjumpLevel: 1 },
    ]);
    assert.deepEqual(solver.jumps, [{ from: 4, to: 1, retained: [posLit(3)] }]);
    const learned = solver.clauses.find((clause) => clause.learned);
    assert.ok(learned !== undefined);
    assertEntailed(base, learned);
    assert.strictEqual(solver.reason[5], learned);
    assert.strictEqual(solver.level[5], 1);
    assert.strictEqual(solver.reason[4], base.clauses[0]);
    assert.deepEqual(
      base.clauses.map((clause) => clause.activity),
      [0, 1, 1],
    );
    assert.strictEqual(solver.clauses.length, base.clauses.length + 1);
    // Only t, v1 and the implied UIP x2 were seen. VSIDS picks t ahead of
    // lower-index free1/free2; their saved TRUE phases survive the backjump.
    // x1 is untouched because analysis stops before resolving x2's reason.
    assert.deepEqual(Array.from(solver.activity), [0, 0, 1, 1, 0, 1]);
    assert.deepEqual(solver.decisions, [
      posLit(3),
      posLit(0),
      posLit(1),
      posLit(4),
      posLit(2),
      posLit(0),
      posLit(1),
    ]);
    // Four attempted decisions before learning, then t and the two free
    // variables; implications x2,t + asserting ¬x2 + implied ¬x1. t's saved
    // phase is TRUE (its binary implication), so the post-backjump heap
    // decision re-picks t as TRUE. The two-literal learned clause has no
    // removable literal (¬v1 is a decision).
    assert.deepEqual(solver.stats, {
      decisions: 7,
      propagations: 4,
      conflicts: 1,
      restarts: 0,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
      learnedLiterals: 2,
      minimizedLiterals: 0,
    });
    assertReasonGraph(solver);
    assertWatchMembership(solver);
  });

  it('watches the assertion and maximum other level, deduplicating independently of watch permutations', () => {
    // Resolving t gives (¬a∨¬b∨¬x2). a@1, b@2, free@3, x1@4→x2@4,
    // so assertion ¬x2 must watch ¬b (level 2), NOT sorted-first ¬a (level 1).
    const base = cnf(
      ['a', 'b', 'free', 't', 'x1', 'x2'],
      [
        [negLit(4), posLit(5)],
        [negLit(0), negLit(5), posLit(3)],
        [negLit(1), negLit(5), negLit(3)],
      ],
    );
    const solver = new Solver(base);
    for (const variable of [0, 1, 2]) {
      decide(solver, posLit(variable));
      assert.strictEqual(solver.propagate(), null);
      assertFixpoint(solver);
    }
    decide(solver, posLit(4));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    assertReasonGraph(solver, conflict);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepEqual(learned.lits, [negLit(5), negLit(1), negLit(0)]);
    assert.strictEqual(backjumpLevel, 2);
    assert.deepEqual(Array.from(solver.activity), [1, 1, 0, 1, 0, 1]);
    assertEntailed(base, learned);
    assert.strictEqual(solver.addLearnedClause(learned), learned);
    assertWatchMembership(solver);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(negLit(5), learned), true);
    assert.strictEqual(solver.propagate(), null);
    assertReasonGraph(solver);

    // After cancelling below b, deciding b again must trigger this learned
    // clause directly. Watching ¬a instead would miss its new unit status.
    solver.cancelUntil(1);
    decide(solver, posLit(1));
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.assigns[5], Value.FALSE);
    assert.strictEqual(solver.reason[5], learned);
    assertReasonGraph(solver);
    assertWatchMembership(solver);

    // Actual propagation moves the assertion out of the watched slots.
    solver.cancelUntil(0);
    decide(solver, posLit(5));
    assert.strictEqual(solver.propagate(), null);
    assert.deepEqual(
      learned.lits.slice(0, 2).sort((a, b) => a - b),
      [negLit(0), negLit(1)],
    );
    assertWatchMembership(solver);
    solver.cancelUntil(0);
    // Re-register the already-proved consequence at an all-unset root. Its
    // input is permuted and has a repeated literal; semantic identity must
    // survive both normalization and the live clause's previous watch moves.
    const duplicate = {
      lits: [negLit(5), negLit(0), negLit(1), negLit(0)],
      learned: true,
      activity: 0,
      lbd: 0,
    };
    assert.strictEqual(solver.addLearnedClause(duplicate), learned);
    assert.strictEqual(solver.clauses.length, base.clauses.length + 1);
    assert.strictEqual(solver.stats.learnedClauses, 1);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 1);
    assert.strictEqual(learned.lits.length, 3);
    assertWatchMembership(solver);
  });

  it('retains root assumption antecedents, so learning is an unconditional formula consequence', () => {
    // Under a@0, deciding x forces incompatible values of t. Resolution
    // yields (¬a∨¬x), NOT the assumption-dependent unary ¬x: a=FALSE,x=TRUE
    // is a model of the base formula. Both literals stay watched, despite
    // the assertion being enqueued at level zero.
    const base = cnf(
      ['a', 't', 'x'],
      [
        [negLit(0), negLit(2), posLit(1)],
        [negLit(0), negLit(2), negLit(1)],
      ],
    );
    const solver = new TracedSolver(base, {
      assumptions: { a: Value.TRUE },
      variablePriority: (unassigned) => (unassigned.includes('x') ? ['x', true] : null),
    });
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.analyses, [
      { from: 1, learned: [negLit(2), negLit(0)], backjumpLevel: 0 },
    ]);
    const learned = solver.reason[2];
    assert.ok(learned !== null);
    assert.strictEqual(learned.learned, true);
    assertEntailed(base, learned);
    assert.strictEqual(solver.level[2], 0);
    assert.strictEqual(learned.lits.length, 2);
    // After a's watch relocations, the positive-t clause is processed first:
    // x=TRUE implies t=TRUE before the other clause conflicts. Backjumping
    // frees t; it is now a don't-care and its saved TRUE phase is reused.
    assert.deepEqual(solver.model(), { a: Value.TRUE, t: Value.TRUE, x: Value.FALSE });
    assert.deepEqual(solver.decisions, [posLit(2), posLit(1)]);
    assert.deepEqual(Array.from(solver.activity), [1, 1, 1], 'root antecedent a is bumped too');
    // (¬x∨¬a) is already minimal: the tainted root literal is poison for
    // minimization and the asserting literal is never a candidate.
    assert.deepEqual(solver.stats, {
      decisions: 2,
      propagations: 2,
      conflicts: 1,
      restarts: 0,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
      learnedLiterals: 2,
      minimizedLiterals: 0,
    });
    assertWatchMembership(solver);
  });

  it('learns genuinely new clauses on PHP(6,5) with exact live counts and canonical reasons', () => {
    const solver = new Solver(compile(cnfToExpr(phpCnf(6, 5))), { maxConflicts: 10_000 });
    assert.strictEqual(solver.solve(), false);
    assert.ok(solver.stats.learnedClauses > 0, 'conflicts alone do not prove CDCL learning');
    const live = solver.clauses.filter((clause) => clause.learned);
    assert.strictEqual(solver.stats.learnedClausesCurrent, live.length);
    assert.strictEqual(
      solver.stats.learnedClauses,
      live.length,
      'no learned clauses were reduced in this run',
    );
    const keys = solver.clauses.map((clause) => [...clause.lits].sort((a, b) => a - b).join(','));
    assert.strictEqual(new Set(keys).size, keys.length);
    assertReasonGraph(solver);
    assertWatchMembership(solver);
  });

  it('checks every learned consequence against small seeded CNF truth tables, including root assumptions', () => {
    let learnedCount = 0;
    for (let seed = 0; seed < 64; seed += 1) {
      const formula = cnfToExpr(random3Cnf(mulberry32(seed), 6, 24));
      const base = compile(formula);
      const name = base.indexToName[0];
      const value = seed % 2 === 0 ? Value.FALSE : Value.TRUE;
      const assumptions = seed % 3 === 0 ? { [name]: value } : {};
      const solver = new TracedSolver(base, { assumptions });
      const models = referenceModels(formula).filter((model) =>
        Object.entries(assumptions).every(([key, value]) => model[key] === value),
      );
      assert.strictEqual(solver.solve(), models.length > 0, `seed ${seed} verdict`);
      for (const clause of solver.clauses) {
        if (clause.learned) {
          assertEntailed(base, clause);
          learnedCount += 1;
        }
      }
      assertWatchMembership(solver);
    }
    assert.ok(learnedCount > 0, 'the consequence checks must exercise actual learning');
  });
});

describe('Solver learned-clause minimization and root provenance', () => {
  it('removes a known-redundant literal, counted by the analysis-work counters', () => {
    // u is implied by a alone, so in the learned clause (¬a∨¬u∨¬b) the
    // literal ¬u is redundant: its reason's antecedent ¬a is already in the
    // clause. Minimization resolves it away, leaving (¬a∨¬b).
    const base = cnf(
      ['a', 'b', 'u', 'z1', 'z2'],
      [
        [negLit(0), posLit(2)],
        [negLit(1), posLit(3)],
        [negLit(1), posLit(4)],
        [negLit(0), negLit(2), negLit(3), negLit(4)],
      ],
    );
    const solver = new Solver(base);
    decide(solver, posLit(0));
    assert.strictEqual(solver.enqueue(posLit(2), base.clauses[0]), true);
    decide(solver, posLit(1));
    assert.strictEqual(solver.enqueue(posLit(3), base.clauses[1]), true);
    assert.strictEqual(solver.enqueue(posLit(4), base.clauses[2]), true);
    const conflict = base.clauses[3];
    assertReasonGraph(solver, conflict);

    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepEqual(learned.lits, [negLit(1), negLit(0)]);
    assert.strictEqual(backjumpLevel, 1);
    assert.strictEqual(learned.lbd, 2);
    assertEntailed(base, learned);
    assert.strictEqual(solver.stats.learnedLiterals, 2, 'post-minimization literals produced');
    assert.strictEqual(solver.stats.minimizedLiterals, 1, 'the redundant ¬u was removed');
  });

  it('keeps a literal whose only explanation passes through a tainted root (minimization poison)', () => {
    // Same shape as the known-redundant fixture, but u's reason reaches the
    // ASSUMPTION a at level zero. Resolving ¬u away would silently drop the
    // a-dependency, so minimization must refuse: tainted roots are poison.
    const base = cnf(
      ['a', 'b', 'd', 'u', 'z1', 'z2'],
      [
        [negLit(0), negLit(2), posLit(3)],
        [negLit(1), posLit(4)],
        [negLit(1), posLit(5)],
        [negLit(2), negLit(3), negLit(4), negLit(5)],
      ],
    );
    const solver = new Solver(base, { assumptions: { a: Value.TRUE } });
    assert.strictEqual(solver.rootBasis[0], 1);
    decide(solver, posLit(2));
    assert.strictEqual(solver.enqueue(posLit(3), base.clauses[0]), true);
    decide(solver, posLit(1));
    assert.strictEqual(solver.enqueue(posLit(4), base.clauses[1]), true);
    assert.strictEqual(solver.enqueue(posLit(5), base.clauses[2]), true);
    const conflict = base.clauses[3];
    assertReasonGraph(solver, conflict);

    const { learned, backjumpLevel } = solver.analyze(conflict);
    // (¬b∨¬d∨¬u): without the poison rule, recursive minimization would
    // resolve ¬u through (¬a∨¬d∨u) and drop the a-dependent literal.
    assert.deepEqual(learned.lits, [negLit(1), negLit(2), negLit(3)]);
    assert.strictEqual(backjumpLevel, 1);
    assertEntailed(base, learned);
    assert.strictEqual(solver.stats.learnedLiterals, 3);
    assert.strictEqual(solver.stats.minimizedLiterals, 0, 'poisoned tainted root kept ¬u');
  });

  it('drops only BASE-DERIVED root literals, never assumption-tainted ones', () => {
    // Unit u is base-derived (rootBasis 0); a is an assumption (rootBasis 1).
    // Both sit at level zero in the same conflict: the learned clause drops
    // ¬u but must retain ¬a.
    const base = cnf(
      ['a', 'b', 'u', 'z'],
      [[posLit(2)], [negLit(1), posLit(3)], [negLit(0), negLit(1), negLit(2), negLit(3)]],
    );
    const solver = new Solver(base, { assumptions: { a: Value.TRUE } });
    assert.strictEqual(solver.rootBasis[2], 0, 'unit clause is base-derived');
    assert.strictEqual(solver.rootBasis[0], 1, 'assumption leaf is tainted');
    decide(solver, posLit(1));
    assert.strictEqual(solver.enqueue(posLit(3), base.clauses[1]), true);
    const conflict = base.clauses[2];
    assertReasonGraph(solver, conflict);

    const { learned, backjumpLevel } = solver.analyze(conflict);
    // (¬b∨¬a): ¬u resolved away as a base consequence; ¬a retained.
    assert.deepEqual(learned.lits, [negLit(1), negLit(0)]);
    assert.strictEqual(backjumpLevel, 0, 'the only other literal is the retained root literal');
    assert.strictEqual(learned.lbd, 1, 'the retained root literal does not inflate LBD');
    assertEntailed(base, learned);
    assert.strictEqual(solver.stats.learnedLiterals, 2);
    assert.strictEqual(
      solver.stats.minimizedLiterals,
      0,
      'first-UIP, not minimization, dropped ¬u',
    );
  });

  it('tracks tainted implications and mixed ancestry in the root reason graph', () => {
    // u is a base unit; a is an assumption. m is implied at root by
    // (¬u∨¬a∨m) — MIXED base+assumption ancestry — and n is implied by m
    // alone. p and x are scoped PLE pins. Every root implication must keep a
    // non-null reason: taint never turns an implication into an assumption
    // leaf, and no caller assumption is invented for implied variables.
    const expr = and('u', or(not('u'), not('a'), 'm'), implies('m', 'n'), or('p', 'x'));
    const base = compile(expr);
    const solver = new Solver(base, { assumptions: { a: Value.TRUE }, enablePle: true });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.decisions, 0, 'everything is forced at root');
    assert.strictEqual(expressionValue(expr, solver.model()), Value.TRUE);

    const index = (name: string) => {
      const variable = base.nameToIndex.get(name);
      assert.ok(variable !== undefined);
      return variable;
    };
    const expectBasis = (name: string, basis: number, reasonNull: boolean) => {
      const variable = index(name);
      assert.strictEqual(solver.level[variable], 0, `${name} is a root assignment`);
      assert.strictEqual(solver.rootBasis[variable], basis, `${name} provenance`);
      assert.strictEqual(solver.reason[variable] === null, reasonNull, `${name} reason shape`);
    };
    expectBasis('u', 0, false);
    expectBasis('a', 1, true);
    expectBasis('m', 1, false);
    expectBasis('n', 1, false);
    expectBasis('p', 2, true);
    expectBasis('x', 2, true);
    // The mixed antecedents are genuine: m's reason mentions both the base
    // unit u and the assumption a.
    const mReason = solver.reason[index('m')];
    assert.ok(mReason !== null);
    assert.ok(mReason.lits.includes(negLit(index('u'))));
    assert.ok(mReason.lits.includes(negLit(index('a'))));
    // A core walk collecting reason-null assumption leaves finds exactly the
    // supplied assumption set — tainted implications are not collectable.
    const collectable: string[] = [];
    for (let variable = 0; variable < base.numVars; variable += 1) {
      if (
        solver.level[variable] === 0 &&
        solver.reason[variable] === null &&
        solver.rootBasis[variable] === 1
      ) {
        collectable.push(base.indexToName[variable]);
      }
    }
    assert.deepEqual(collectable, ['a']);
  });

  it('retains a learnable dependency on the assumption in the probe witness', () => {
    // Regression: (¬a∨x∨t)∧(¬a∨x∨¬t)∧(¬x∨t)∧(¬x∨¬t) under a=TRUE. The first
    // conflict learns (¬a∨t), NOT the unit (t): unconditional root dropping
    // would erase the a-dependency that core extraction (Phase 3) needs —
    // the walk from the terminal root conflict must reach the assumption.
    const base = cnf(
      ['a', 't', 'x'],
      [
        [negLit(0), posLit(1), posLit(2)],
        [negLit(0), posLit(2), negLit(1)],
        [negLit(2), posLit(1)],
        [negLit(2), negLit(1)],
      ],
    );
    const solver = new Solver(base, { assumptions: { a: Value.TRUE } });
    assert.strictEqual(solver.solve(), false, 'base ∧ a=TRUE is UNSAT');
    const learned = solver.clauses.find((clause) => clause.learned);
    assert.ok(learned !== undefined, 'a clause was learned before the terminal conflict');
    assert.deepEqual(
      [...learned.lits].sort((left, right) => left - right),
      [negLit(0), posLit(1)],
      'the learned (¬a∨t) keeps its assumption dependency',
    );
    assertEntailed(base, learned);
    // The asserting root assignment is itself tainted through that reason.
    assert.strictEqual(solver.reason[1], learned);
    assert.strictEqual(solver.rootBasis[1], 1, 't is a tainted root implication, not a leaf');
    assert.strictEqual(solver.stats.minimizedLiterals, 0, 'the tainted root literal is poison');
  });
});
