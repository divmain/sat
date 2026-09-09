import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, isNeg, litValue, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, not, or, Value } from '../src/expr.js';
import type { BooleanExpr } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats, VariablePriority } from '../src/solver.js';
import { assertModelShape, cnfToExpr, expressionValue, phpCnf, watchesClause } from './helpers';

interface Internals {
  readonly learnedClauseReductionThreshold: number;
  readonly learnedSinceReduction: number;
  readonly decisionHeap: readonly number[];
  readonly heapPosition: Int32Array;
  readonly unassignedNamed: number;
  readonly varInc: number;
  readonly claInc: number;
  readonly clauseByKey: Map<string, Clause>;
}

// Read-only observations except in explicitly isolated checker-negative tests.
// No valid fixture injects activities, LBDs, assignments, reasons or counters.
const internals = (solver: Solver): Internals => solver as unknown as Internals;
const key = (clause: Clause): string => [...clause.lits].sort((a, b) => a - b).join(',');

function literal(base: CompiledCnf, name: string, value = Value.TRUE): number {
  const variable = base.nameToIndex.get(name);
  assert.ok(variable !== undefined);
  return variable * 2 + (value === Value.FALSE ? 1 : 0);
}

// Reconstruct each reason's unit antecedents at enqueue time, independently of
// analysis and watch slots. Operation-local tests may leave propagation queued,
// but every implication must still have a real, already-unit database reason.
function assertGraph(solver: Solver, conflict?: Clause): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (let index = 0; index < solver.trail.length; index += 1) {
    const lit = solver.trail[index];
    const variable = varOf(lit);
    const level = solver.trailLim.filter((boundary) => boundary <= index).length;
    assert.strictEqual(prefix[variable], Value.UNSET);
    assert.strictEqual(solver.level[variable], level);
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.ok(solver.clauses.includes(reason), 'reason has canonical live identity');
      assert.ok(reason.lits.includes(lit));
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(litValue(other, prefix), Value.FALSE, 'reason was unit at enqueue');
        }
      }
    } else if (level > 0) {
      assert.strictEqual(index, solver.trailLim[level - 1], 'one decision starts each level');
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepStrictEqual(prefix, solver.assigns);
  if (conflict !== undefined) {
    assert.ok(solver.clauses.includes(conflict));
    assert.ok(conflict.lits.every((lit) => litValue(lit, prefix) === Value.FALSE));
  }
}

function decide(solver: Solver, lit: number): void {
  assert.strictEqual(solver.propagate(), null);
  assert.strictEqual(solver.qhead, solver.trail.length);
  assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
  solver.newDecisionLevel();
  assert.strictEqual(solver.enqueue(lit, null), true);
}

// Exhaustive independent CNF truth table, including real auxiliaries and models
// violating the conflict's assumptions. A SAT witness is mandatory here: an
// UNSAT premise would make every proposed entailment vacuously pass.
function assertEntailed(base: CompiledCnf, learned: Clause): void {
  assert.ok(base.numVars <= 12, 'operation-local truth tables remain small');
  let models = 0;
  for (let mask = 0; mask < 2 ** base.numVars; mask += 1) {
    const satisfied = (clause: Clause) =>
      clause.lits.some((lit) => ((mask >> varOf(lit)) & 1) === (isNeg(lit) ? 0 : 1));
    if (base.clauses.every(satisfied)) {
      models += 1;
      assert.ok(satisfied(learned), `unconditional consequence in base model ${mask}`);
    }
  }
  assert.ok(models > 0, 'non-vacuous entailment check on a satisfiable base');
}

// Resolving t gives (¬a∨¬b∨¬xi). The last clause prevents startup PLE and is
// satisfied when a=b=TRUE. Thus a=b=TRUE, all xi=FALSE, any t is a known model,
// independently of either solver or analyze(). Shared t keeps truth tables small.
function gadgets(count: number): BooleanExpr {
  return and(
    ...Array.from({ length: count }, (_, index) =>
      and(
        or(not('a'), not(`x${index}`), 't'),
        or(not('b'), not(`x${index}`), not('t')),
        or('a', 'b', `x${index}`, 't'),
      ),
    ),
  );
}

const priority: VariablePriority = (unassigned) => {
  const name = ['a', 'b'].find((name) => unassigned.includes(name));
  const x = unassigned.find((name) => name.startsWith('x'));
  return name !== undefined ? [name, true] : x !== undefined ? [x, true] : null;
};

// Drive the real propagate/analyze/register/assert operations, then release the
// decision context. This is an operation-local fixture, not a claimed solve trace.
function learnGadget(solver: Solver, base: CompiledCnf, index: number): Clause {
  assert.strictEqual(solver.trailLim.length, 0);
  for (const name of ['a', 'b', `x${index}`]) {
    decide(solver, literal(base, name));
  }
  const conflict = solver.propagate();
  assert.ok(conflict !== null);
  assertGraph(solver, conflict);
  const { learned, backjumpLevel } = solver.analyze(conflict);
  assert.strictEqual(
    key(learned),
    ['a', 'b', `x${index}`]
      .map((name) => literal(base, name, Value.FALSE))
      .sort((a, b) => a - b)
      .join(','),
  );
  assert.strictEqual(learned.lbd, 3);
  assert.strictEqual(backjumpLevel, 2);
  assertEntailed(base, learned);
  const registered = solver.addLearnedClause(learned);
  solver.cancelUntil(backjumpLevel);
  assert.strictEqual(solver.enqueue(learned.lits[0], registered), true);
  assertGraph(solver);
  solver.cancelUntil(0);
  return registered;
}

function searchState(solver: Solver) {
  const state = internals(solver);
  return {
    assigns: solver.assigns.slice(),
    levels: solver.level.slice(),
    trail: [...solver.trail],
    boundaries: [...solver.trailLim],
    qhead: solver.qhead,
    activity: solver.activity.slice(),
    phases: solver.polarity.slice(),
    heap: [...state.decisionHeap],
    positions: state.heapPosition.slice(),
    unassigned: state.unassignedNamed,
    increment: state.varInc,
  };
}

interface Reduction {
  admissions: number;
  conflict: number;
  before: number;
  after: number;
  removed: string[];
}

class AuditedSolver extends Solver {
  readonly reductions: Reduction[] = [];
  readonly learnedLevels: Array<{ lits: number[]; levels: number[]; lbd: number }> = [];
  // Low-level constructor fixtures deliberately supply inherited counter offsets
  // to ensure cadence is instance-local. Public enumeration now zeroes ONCE and
  // uses ONE solver; it never sums live counts from discarded instances.
  readonly initialTotal = this.stats.learnedClauses;
  readonly initialCurrent = this.stats.learnedClausesCurrent;

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    assertGraph(this, conflict);
    const result = super.analyze(conflict);
    const levels = result.learned.lits.map((lit) => this.level[varOf(lit)]);
    assert.strictEqual(
      result.learned.lbd,
      new Set(levels.filter((level) => level !== 0)).size,
      'learning-time distinct nonzero levels',
    );
    this.learnedLevels.push({ lits: [...result.learned.lits], levels, lbd: result.learned.lbd });
    return result;
  }

  override reduceLearnedClauses(): void {
    this.checkInvariants();
    assertGraph(this);
    const database = this.clauses;
    const before = [...database];
    const metadata = before.map((clause) => ({
      lits: [...clause.lits],
      learned: clause.learned,
      activity: clause.activity,
      lbd: clause.lbd,
    }));
    const watches = [...this.watches];
    const reasons = [...this.reason];
    const state = searchState(this);
    const stats = { ...this.stats };
    const claIncBefore = internals(this).claInc;
    const liveBefore = before.filter((clause) => clause.learned).length;
    assert.strictEqual(stats.learnedClausesCurrent - this.initialCurrent, liveBefore);

    super.reduceLearnedClauses();
    // Mandatory after EVERY forced round, including protected-only rounds.
    this.checkInvariants();
    assertGraph(this);
    assert.strictEqual(
      internals(this).claInc,
      claIncBefore * (1 / 0.999),
      'relative clause-activity decay fires after EVERY round',
    );
    const retained = new Set(this.clauses);
    const removed = before.filter((clause) => !retained.has(clause));
    // Exact two-tier selection: the deleted set is precisely the unlocked
    // worse half of the REDUCIBLE tier (stable activity order over admission
    // order). Glue-tier clauses are never candidates, so they can neither be
    // deleted nor consume a deletion slot.
    const reducible = before.filter((clause) => clause.learned && clause.lbd > 2);
    const ranked = reducible
      .map((clause, admission) => ({ clause, admission }))
      .sort(
        (left, right) =>
          left.clause.activity - right.clause.activity || left.admission - right.admission,
      );
    const expectedRemoved = new Set(
      ranked
        .slice(0, Math.floor(ranked.length / 2))
        .map(({ clause }) => clause)
        .filter((clause) => !reasons.includes(clause)),
    );
    assert.deepStrictEqual(
      new Set(removed),
      expectedRemoved,
      'exactly the unlocked worse half of the reducible tier',
    );
    for (const clause of removed) {
      assert.strictEqual(clause.learned, true, 'permanent clauses are never reduced');
      assert.ok(clause.lbd > 2, 'glue-tier clauses are never deletion candidates');
      assert.ok(!reasons.includes(clause), 'EVERY active reason is protected');
    }
    assert.strictEqual(this.clauses, database, 'the database array itself stays stable');
    const survivors = before.filter((clause) => retained.has(clause));
    assert.strictEqual(this.clauses.length, survivors.length, 'no newly invented clauses');
    for (let index = 0; index < survivors.length; index += 1) {
      assert.strictEqual(this.clauses[index], survivors[index], 'stable survivor identity/order');
    }
    for (let index = 0; index < before.length; index += 1) {
      assert.deepStrictEqual(before[index], metadata[index], 'reduction does not rewrite clauses');
    }
    for (let lit = 0; lit < watches.length; lit += 1) {
      assert.strictEqual(this.watches[lit], watches[lit], 'watch list identities stay stable');
    }
    for (let variable = 0; variable < reasons.length; variable += 1) {
      assert.strictEqual(this.reason[variable], reasons[variable], 'reason identity is untouched');
    }
    assert.deepStrictEqual(searchState(this), state, 'root facts, trail, queue, VSIDS/phases/heap');
    assert.deepStrictEqual(this.stats, {
      ...stats,
      learnedClausesCurrent: stats.learnedClausesCurrent - removed.length,
    });
    assert.strictEqual(
      this.stats.learnedClausesCurrent - this.initialCurrent,
      this.clauses.filter((clause) => clause.learned).length,
      'live count includes protected clauses even if no candidates can be deleted',
    );
    assert.strictEqual(internals(this).learnedSinceReduction, 0, 'consume protected-only rounds');
    const admissions = this.stats.learnedClauses - this.initialTotal;
    assert.ok(
      admissions >= (this.reductions.at(-1)?.admissions ?? 0),
      'monotonic total admissions',
    );
    this.reductions.push({
      admissions,
      conflict: this.stats.conflicts,
      before: liveBefore,
      after: liveBefore - removed.length,
      removed: removed.map(key),
    });
  }
}

describe('Solver learning-time LBD', () => {
  it('counts distinct levels before a non-chronological backjump, not depth or post-assertion levels', () => {
    const base = compile(and(gadgets(1), or('free', not('free'))));
    const solver = new AuditedSolver(base);
    for (const name of ['a', 'b', 'free', 'x0']) {
      decide(solver, literal(base, name));
    }
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [4, 2, 1],
    );
    assert.strictEqual(learned.lbd, 3);
    assert.strictEqual(backjumpLevel, 2);
    assertEntailed(base, learned);
    assert.strictEqual(solver.addLearnedClause(learned), learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [2, 2, 1],
    );
    assert.strictEqual(learned.lbd, 3, 'the recorded learning-time score is not recomputed');
    solver.cancelUntil(0);
    const duplicate = { ...learned, lits: [...learned.lits].reverse() };
    assert.strictEqual(solver.addLearnedClause(duplicate), learned);
    assert.strictEqual(learned.lbd, 3, 'canonical rediscovery preserves recorded metadata');
    assert.strictEqual(solver.stats.learnedClauses, 1);
    solver.checkInvariants();
  });

  it('retains tainted root antecedents without inflating LBD, preserving unconditional entailment', () => {
    const base = compile(gadgets(1));
    const solver = new AuditedSolver(base, { assumptions: { a: Value.TRUE, b: Value.TRUE } });
    decide(solver, literal(base, 'x0'));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [1, 0, 0],
    );
    // The assumption-tainted root literals stay (they are not base
    // consequences), but level zero contributes NOTHING to the score.
    assert.strictEqual(learned.lbd, 1, 'only the distinct nonzero levels count');
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(backjumpLevel, 0);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    assert.ok(learned.lits.every((lit) => solver.level[varOf(lit)] === 0));
    assert.strictEqual(learned.lbd, 1);
    solver.reduceLearnedClauses();
  });

  it('assigns LBD 1 to a genuinely learned unit even when its decision depth exceeds one', () => {
    const base = compile(and(or('free', not('free')), or('x', 't'), or('x', not('t'))));
    const solver = new AuditedSolver(base);
    decide(solver, literal(base, 'free'));
    decide(solver, literal(base, 'x', Value.FALSE));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(learned.lits, [literal(base, 'x')]);
    assert.strictEqual(learned.lbd, 1);
    assert.strictEqual(backjumpLevel, 0);
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(0);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    solver.reduceLearnedClauses();
    assert.strictEqual(solver.reason[varOf(learned.lits[0])], learned);
    assert.ok(
      solver.watches.every((list) => !watchesClause(list, learned)),
      'units remain unwatched',
    );
  });

  it('protects a long LBD-2 clause with repeated implication levels after it is unlocked', () => {
    const base = compile(
      and(
        implies('s', 'a'),
        implies('s', 'b'),
        implies('s', 'c'),
        or(not('a'), not('x'), 't'),
        or(not('b'), not('c'), not('x'), not('t')),
        gadgets(2),
      ),
    );
    const solver = new AuditedSolver(base);
    decide(solver, literal(base, 's'));
    decide(solver, literal(base, 'x'));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.strictEqual(learned.lits.length, 4);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [2, 1, 1, 1],
    );
    assert.strictEqual(learned.lbd, 2, 'length four still has glue two');
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    solver.cancelUntil(0);
    learnGadget(solver, base, 0);
    learnGadget(solver, base, 1);
    assert.ok(!solver.reason.includes(learned), 'protection cannot be explained by a reason lock');
    assert.deepStrictEqual(
      solver.clauses.filter((clause) => clause.learned).map((c) => c.lbd),
      [2, 3, 3],
    );
    // The glue clause is NEVER a candidate, so it cannot consume a deletion
    // slot: the reducible tier's worse half is one of the two LBD-3 clauses
    // (admission order breaks the activity tie), and it is deleted.
    const reducible = solver.clauses.filter((clause) => clause.learned && clause.lbd > 2);
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(solver.reductions[0], {
      admissions: 3,
      conflict: 3,
      before: 3,
      after: 2,
      removed: [key(reducible[0])],
    });
    assert.ok(solver.clauses.includes(learned), 'the glue tier is untouchable');
    assert.ok(solver.clauses.includes(reducible[1]));
    assert.strictEqual(solver.stats.learnedClausesCurrent, 2);
  });

  it('never deletes the glue tier even when it holds the strictly worst activity', () => {
    // Inverted-activity witness: give BOTH reducible clauses more real usage
    // than the glue clause, so a ranking over ALL learned clauses would call
    // the glue clause the worst. Tiering, not ranking, protects it — and
    // exactly one reducible clause (the admission-older activity tie) goes.
    const base = compile(
      and(
        implies('s', 'a'),
        implies('s', 'b'),
        implies('s', 'c'),
        or(not('a'), not('x'), 't'),
        or(not('b'), not('c'), not('x'), not('t')),
        gadgets(2),
      ),
    );
    const solver = new AuditedSolver(base);
    decide(solver, literal(base, 's'));
    decide(solver, literal(base, 'x'));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.strictEqual(learned.lbd, 2);
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    solver.cancelUntil(0);
    const reducible = [0, 1].map((index) => learnGadget(solver, base, index));
    // Real usage only: consume each reducible clause as a conflict seed via
    // the analysis-local fixture (no fabricated activity, no propagation —
    // the learned clause would otherwise unit-fire before it is falsified).
    // The glue clause keeps the zero usage it had at creation.
    for (const [index, clause] of reducible.entries()) {
      for (const name of ['a', 'b', `x${index}`]) {
        const lit = literal(base, name);
        assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
        solver.newDecisionLevel();
        assert.strictEqual(solver.enqueue(lit, null), true);
      }
      assertGraph(solver, clause);
      solver.analyze(clause);
      solver.cancelUntil(0);
    }
    assert.strictEqual(learned.activity, 0, 'the glue clause is the strict global minimum');
    assert.ok(
      reducible.every((clause) => clause.activity > learned.activity),
      'a global ranking would call the glue clause the worst',
    );
    assert.ok(reducible.every((clause) => clause.lbd === 3 && !solver.reason.includes(clause)));
    assert.ok(!solver.reason.includes(learned));
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(solver.reductions[0].removed, [key(reducible[0])]);
    assert.ok(solver.clauses.includes(learned), 'tier membership, not activity, protects');
    assert.ok(solver.clauses.includes(reducible[1]));
    assert.strictEqual(solver.stats.learnedClausesCurrent, 2);
  });
});

describe('Solver learned reduction selection and identity', () => {
  it('removes the worse half by real usage, breaks ties by admission, detaches moved watches, and re-derives deleted keys', () => {
    const base = compile(gadgets(5));
    const solver = new AuditedSolver(base);
    const clauses = Array.from({ length: 5 }, (_, index) => learnGadget(solver, base, index));

    // Real propagation moves x2's old asserting watch out of BOTH watched slots.
    decide(solver, literal(base, 'x2'));
    assert.strictEqual(solver.propagate(), null);
    assert.ok(!clauses[2].lits.slice(0, 2).includes(literal(base, 'x2', Value.FALSE)));
    solver.cancelUntil(0);

    // Analysis-local usage-count fixture: delay propagation, falsify a proved
    // consequence using ordinary decisions, and consume it as a conflict seed.
    // No fabricated activity or reason. This is NOT an eager-search trace.
    for (const [index, usages] of [1, 3, 0, 2, 1].entries()) {
      for (let usage = 0; usage < usages; usage += 1) {
        for (const name of ['a', 'b', `x${index}`]) {
          const lit = literal(base, name);
          assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
          solver.newDecisionLevel();
          assert.strictEqual(solver.enqueue(lit, null), true);
        }
        assertGraph(solver, clauses[index]);
        const { learned } = solver.analyze(clauses[index]);
        assertEntailed(base, learned);
        assert.strictEqual(key(learned), key(clauses[index]));
        solver.cancelUntil(0);
      }
    }
    assert.deepStrictEqual(
      clauses.map((clause) => clause.activity),
      [1, 3, 0, 2, 1],
    );
    assert.ok(clauses.every((clause) => clause.lbd === 3 && !solver.reason.includes(clause)));
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(solver.reductions[0].removed, [key(clauses[0]), key(clauses[2])]);
    assert.deepStrictEqual(
      solver.clauses.filter((clause) => clause.learned),
      [clauses[1], clauses[3], clauses[4]],
    );
    assert.strictEqual(solver.stats.learnedClauses, 5);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 3);
    assert.ok(solver.watches.every((list) => !watchesClause(list, clauses[2])));
    for (const index of [0, 2]) {
      assert.ok(!internals(solver).clauseByKey.has(key(clauses[index])), 'no stale canonical key');
    }

    const rederived = learnGadget(solver, base, 2);
    assert.notStrictEqual(
      rederived,
      clauses[2],
      'deleted identity is not returned from a stale map',
    );
    assert.strictEqual(key(rederived), key(clauses[2]));
    assert.strictEqual(solver.stats.learnedClauses, 6, 'a new admission after real re-derivation');
    assert.strictEqual(solver.stats.learnedClausesCurrent, 4);
    const duplicate = { ...rederived, lits: [...rederived.lits].reverse() };
    assert.strictEqual(solver.addLearnedClause(duplicate), rederived);
    assert.strictEqual(solver.stats.learnedClauses, 6);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 4);
    solver.checkInvariants();
  });

  it('protects EVERY pending high-LBD reason, even outside both watched slots, without backfilling', () => {
    const base = compile(gadgets(6));
    const solver = new AuditedSolver(base);
    const clauses = Array.from({ length: 6 }, (_, index) => learnGadget(solver, base, index));
    decide(solver, literal(base, 'a'));
    decide(solver, literal(base, 'b'));
    // Leave b's propagation queued; all six consequences are now unit. Enqueue
    // three legitimately, so the entire WORSE half is locked but the better
    // half is not. This catches protection of only the latest assertion/reason.
    for (let index = 0; index < 3; index += 1) {
      const clause = clauses[index];
      const implied = literal(base, `x${index}`, Value.FALSE);
      assert.strictEqual(solver.enqueue(implied, clause), true);
      const permuted = {
        ...clause,
        lits: [literal(base, 'a', Value.FALSE), literal(base, 'b', Value.FALSE), implied],
      };
      assert.strictEqual(solver.addLearnedClause(permuted), clause);
      assert.ok(!clause.lits.slice(0, 2).includes(implied), 'implied literal is not a watch');
    }
    assert.strictEqual(solver.qhead, 1);
    assertGraph(solver);
    assert.ok(clauses.slice(0, 3).every((clause) => solver.reason.includes(clause)));
    assert.ok(clauses.slice(3).every((clause) => !solver.reason.includes(clause)));
    solver.reduceLearnedClauses();
    assert.strictEqual(solver.reductions[0].after, 6);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 6);
    solver.cancelUntil(0);
    solver.reduceLearnedClauses();
    assert.strictEqual(
      solver.reductions[1].after,
      3,
      'the same clauses become deletable when unlocked',
    );
    assert.strictEqual(solver.stats.learnedClauses, 6);
  });

  it('protects a root auxiliary reason with its genuine high learning-time LBD', () => {
    // A COMPLETE bidirectional u ↔ (x ∧ y) gate, not an unconstrained named
    // variable relabelled as auxiliary. The two extra clauses conflict on t
    // after u is implied, so the first UIP really is the auxiliary u.
    const base = compile(and(gadgets(2), or('x', not('x')), or('y', not('y'))));
    const u = base.numVars * 2;
    base.numVars += 1;
    const x = literal(base, 'x');
    const y = literal(base, 'y');
    const a = literal(base, 'a');
    const b = literal(base, 'b');
    const t = literal(base, 't');
    for (const lits of [
      [u ^ 1, x],
      [u ^ 1, y],
      [u, x ^ 1, y ^ 1],
      [a ^ 1, u ^ 1, t],
      [b ^ 1, u ^ 1, t ^ 1],
    ]) {
      base.clauses.push({ lits, learned: false, activity: 0, lbd: 0 });
    }
    const solver = new AuditedSolver(base);
    for (const lit of [a, b, x, y]) {
      decide(solver, lit);
    }
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(learned.lits, [u ^ 1, b ^ 1, a ^ 1]);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [4, 2, 1],
    );
    assert.strictEqual(learned.lbd, 3);
    assert.strictEqual(backjumpLevel, 2);
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(u ^ 1, learned), true);
    solver.cancelUntil(0);
    learnGadget(solver, base, 0);
    learnGadget(solver, base, 1);

    // Replay the unit reason under root facts using the existing operations.
    // This is not a new assumption-call API. No reason or assignment is forged.
    assert.strictEqual(solver.enqueue(a, null), true);
    assert.strictEqual(solver.enqueue(b, null), true);
    assert.strictEqual(solver.enqueue(u ^ 1, learned), true);
    assert.strictEqual(
      solver.addLearnedClause({ ...learned, lits: [a ^ 1, b ^ 1, u ^ 1] }),
      learned,
    );
    assert.ok(!learned.lits.slice(0, 2).includes(u ^ 1));
    assert.strictEqual(solver.reason[varOf(u)], learned);
    assert.strictEqual(solver.level[varOf(u)], 0);
    assert.strictEqual(learned.lbd, 3, 'root replay does not relabel its learned LBD as one');
    assert.ok(solver.qhead < solver.trail.length, 'the root auxiliary assertion is pending');
    solver.reduceLearnedClauses();
    assert.strictEqual(
      solver.reductions[0].after,
      3,
      'the worst clause is locked at auxiliary root',
    );
    assert.strictEqual(solver.propagate(), null);
    solver.cancelUntil(0);
    assert.strictEqual(solver.reason[varOf(u)], learned, 'root reason survives cancellation');
    solver.reduceLearnedClauses();
    assert.strictEqual(solver.stats.learnedClausesCurrent, 3);
  });

  it('preserves permanent original and blocking roles, even with a previously measured high LBD', () => {
    const expr = gadgets(4);
    const donorBase = compile(expr);
    const donor = new AuditedSolver(donorBase);
    const proved = learnGadget(donor, donorBase, 0);
    assert.strictEqual(proved.lbd, 3);

    const base = compile(expr);
    // Install a previously proved consequence as a PERMANENT initial constraint
    // in a fresh solver. Its LBD is genuinely measured, not manufactured to beat
    // the filter: only its role differs. Reduction must not infer role from LBD.
    const permanent = { ...proved, lits: [...proved.lits], learned: false };
    base.clauses.push(permanent);
    // An actual blocking constraint over every named variable, excluding this
    // independently constructed base model. Dynamic admission and promotion are
    // covered separately by enumeration.spec.ts on the production admission path.
    const excluded = Object.fromEntries(
      base.indexToName.map((name) => [name, name === 't' ? Value.TRUE : Value.FALSE]),
    );
    assert.strictEqual(expressionValue(expr, excluded), Value.TRUE);
    const blocking: Clause = {
      lits: base.indexToName.map((name) =>
        literal(base, name, excluded[name] === Value.TRUE ? Value.FALSE : Value.TRUE),
      ),
      learned: false,
      activity: 0,
      lbd: 0,
    };
    base.clauses.push(blocking);
    assertEntailed(base, permanent);
    const solver = new AuditedSolver(base);
    const removable = [1, 2, 3].map((index) => learnGadget(solver, base, index));
    assert.strictEqual(solver.addLearnedClause({ ...proved, lits: [...proved.lits] }), permanent);
    assert.strictEqual(permanent.learned, false, 'rediscovery does not convert permanent role');
    assert.strictEqual(permanent.lbd, 3);
    assert.strictEqual(permanent.activity, 0);
    assert.ok(!solver.reason.includes(permanent), 'not incidentally protected by a reason');
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(solver.reductions[0].removed, [key(removable[0])]);
    assert.ok(solver.clauses.includes(permanent));
    assert.ok(solver.clauses.includes(blocking));
    assert.strictEqual(internals(solver).clauseByKey.get(key(permanent)), permanent);
    assert.strictEqual(internals(solver).clauseByKey.get(key(blocking)), blocking);
    assert.strictEqual(solver.stats.learnedClauses, 3);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 2);
    const excludedAssignments = Int8Array.from(base.indexToName.map((name) => excluded[name]));
    assert.ok(blocking.lits.every((lit) => litValue(lit, excludedAssignments) === Value.FALSE));
  });
});

describe('Solver decayed clause activity and dynamic LBD', () => {
  // Consume a genuinely learned clause as a conflict seed: decide its gadget
  // witnesses (WITHOUT propagation, which would unit-fire the clause first),
  // then run the real analyze. This is operation-local usage, not a solve
  // trace and not fabricated activity.
  function consumeAsSeed(solver: Solver, base: CompiledCnf, clause: Clause, index: number): void {
    for (const name of ['a', 'b', `x${index}`]) {
      const lit = literal(base, name);
      assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
      solver.newDecisionLevel();
      assert.strictEqual(solver.enqueue(lit, null), true);
    }
    assertGraph(solver, clause);
    solver.analyze(clause);
    solver.cancelUntil(0);
  }

  it('decays older bumps: equal usage counts rank by bump recency after a round', () => {
    const base = compile(gadgets(8));
    const solver = new AuditedSolver(base);
    const clauses = Array.from({ length: 8 }, (_, index) => learnGadget(solver, base, index));
    // Pre-round usage: every clause once; clauses 6 and 7 a second time.
    for (const [index, clause] of clauses.entries()) {
      consumeAsSeed(solver, base, clause, index);
    }
    consumeAsSeed(solver, base, clauses[6], 6);
    consumeAsSeed(solver, base, clauses[7], 7);
    assert.deepStrictEqual(
      clauses.map((clause) => clause.activity),
      [1, 1, 1, 1, 1, 1, 2, 2],
      'the increment is still exactly one before the first round',
    );
    assert.strictEqual(internals(solver).claInc, 1);
    solver.reduceLearnedClauses();
    // Ties at activity 1 resolve by admission: the oldest four are deleted.
    assert.deepStrictEqual(
      solver.reductions[0].removed,
      [0, 1, 2, 3].map((index) => key(clauses[index])),
    );
    assert.strictEqual(internals(solver).claInc, 1 / 0.999, 'relative decay after the round');

    // Post-round usage: clauses 4 and 5 each get ONE more bump — the same
    // lifetime usage count as 6/7's two pre-round bumps, but each post-round
    // bump carries the grown increment.
    consumeAsSeed(solver, base, clauses[4], 4);
    consumeAsSeed(solver, base, clauses[5], 5);
    assert.strictEqual(clauses[4].activity, 1 + 1 / 0.999);
    assert.strictEqual(clauses[5].activity, 1 + 1 / 0.999);
    assert.strictEqual(clauses[6].activity, 2);
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(
      solver.reductions[1].removed,
      [key(clauses[6]), key(clauses[7])],
      'decay: two fresher bumps outweigh two older bumps',
    );
    assert.ok(solver.clauses.includes(clauses[4]));
    assert.ok(solver.clauses.includes(clauses[5]));
    solver.checkInvariants();
  });

  it('tightens LBD on analysis reuse by two or more levels, promoting the clause into the glue tier', () => {
    // Learn (¬a∨¬b∨¬c∨¬x) at FOUR distinct nonzero levels (lbd 4): x@4 forces
    // t@4, the second clause conflicts, and resolving t's reason folds in a@1.
    const base = compile(
      and(or(not('a'), not('x'), 't'), or(not('b'), not('c'), not('x'), not('t')), gadgets(3)),
    );
    const solver = new AuditedSolver(base);
    const gadgets3 = [0, 1, 2].map((index) => learnGadget(solver, base, index));
    for (const name of ['a', 'b', 'c', 'x']) {
      decide(solver, literal(base, name));
    }
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(
      [...learned.lits].sort(
        (left, right) => solver.level[varOf(left)] - solver.level[varOf(right)],
      ),
      ['a', 'b', 'c', 'x'].map((name) => literal(base, name, Value.FALSE)),
    );
    assert.strictEqual(learned.lbd, 4);
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    solver.cancelUntil(0);

    // Reuse with a and b pinned at ROOT (the root-replay idiom): the shared
    // metric recomputes to the two distinct nonzero levels of c and x — an
    // improvement of two, so the stored score tightens 4 -> 2.
    assert.strictEqual(solver.enqueue(literal(base, 'a'), null), true);
    assert.strictEqual(solver.enqueue(literal(base, 'b'), null), true);
    for (const name of ['c', 'x']) {
      const lit = literal(base, name);
      assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
      solver.newDecisionLevel();
      assert.strictEqual(solver.enqueue(lit, null), true);
    }
    assertGraph(solver, learned);
    solver.analyze(learned);
    assert.strictEqual(learned.lbd, 2, 'two-level improvement tightens into the glue tier');
    solver.cancelUntil(0);

    // Promotion is observable in selection: the reducible tier is now exactly
    // the three gadget clauses, so ONE deletion results — had the clause
    // stayed reducible (tier of four), the worse half would be two.
    solver.reduceLearnedClauses();
    assert.deepStrictEqual(solver.reductions[0].removed, [key(gadgets3[0])]);
    assert.ok(solver.clauses.includes(learned), 'promoted clause is glue and survives');
    assert.ok(solver.clauses.includes(gadgets3[1]), 'tier shrinkage protects the next-worst');
    assert.ok(solver.clauses.includes(gadgets3[2]));
    solver.checkInvariants();
  });

  it('ignores single-step recomputes, so incidental level drift never erodes the reducible tier', () => {
    const base = compile(gadgets(3));
    const solver = new AuditedSolver(base);
    const clauses = Array.from({ length: 3 }, (_, index) => learnGadget(solver, base, index));
    assert.ok(clauses.every((clause) => clause.lbd === 3));
    // Root-replay idiom: with 'a' pinned at ROOT, reuse of clause 0 recomputes
    // to two distinct nonzero levels — a single-step improvement, which the
    // hysteresis deliberately does not apply.
    assert.strictEqual(solver.enqueue(literal(base, 'a'), null), true);
    for (const name of ['b', 'x0']) {
      const lit = literal(base, name);
      assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
      solver.newDecisionLevel();
      assert.strictEqual(solver.enqueue(lit, null), true);
    }
    assertGraph(solver, clauses[0]);
    solver.analyze(clauses[0]);
    assert.strictEqual(clauses[0].lbd, 3, 'one-step drift is not a tightening');
    solver.cancelUntil(0);
    assert.strictEqual(solver.assigns[varOf(literal(base, 'a'))], Value.TRUE, 'root fact survives');
    solver.checkInvariants();
  });

  it('never raises a stored LBD, even when a later reuse spans more distinct levels', () => {
    const base = compile(
      and(
        implies('s', 'a'),
        implies('s', 'b'),
        implies('s', 'c'),
        or(not('a'), not('x'), 't'),
        or(not('b'), not('c'), not('x'), not('t')),
      ),
    );
    const solver = new AuditedSolver(base);
    decide(solver, literal(base, 's'));
    decide(solver, literal(base, 'x'));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned, backjumpLevel } = solver.analyze(conflict);
    assert.deepStrictEqual(
      learned.lits.map((lit) => solver.level[varOf(lit)]),
      [2, 1, 1, 1],
    );
    assert.strictEqual(learned.lbd, 2);
    assertEntailed(base, learned);
    solver.addLearnedClause(learned);
    solver.cancelUntil(backjumpLevel);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    solver.cancelUntil(0);

    // Later reuse with all four literals at DISTINCT nonzero levels: the
    // recomputed score (four) exceeds the stored one and must NOT be applied.
    for (const name of ['a', 'b', 'c', 'x']) {
      const lit = literal(base, name);
      assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
      solver.newDecisionLevel();
      assert.strictEqual(solver.enqueue(lit, null), true);
    }
    assertGraph(solver, learned);
    const activityBefore = learned.activity;
    solver.analyze(learned);
    assert.ok(learned.activity > activityBefore, 'participation still bumps activity');
    assert.strictEqual(learned.lbd, 2, 'tightening is monotone: never an increase');
    solver.cancelUntil(0);
    solver.checkInvariants();
  });

  it('keeps lifetime clause-aging accounting across per-call incremental stat resets', () => {
    const base = compile(gadgets(6));
    const solver = new AuditedSolver(base, {
      variablePriority: priority,
      learnedClauseReductionThreshold: 2,
    });
    const stats1: SolverStats = {
      decisions: 0,
      propagations: 0,
      conflicts: 0,
      restarts: 0,
      learnedClauses: 0,
      learnedClausesCurrent: 0,
      learnedLiterals: 0,
      minimizedLiterals: 0,
    };
    assert.ok(solver.solveAssuming(undefined, stats1) !== null);
    const roundsAfterCall1 = solver.reductions.length;
    assert.ok(roundsAfterCall1 > 0, 'call 1 engaged real reduction rounds');
    let expected = 1;
    for (let round = 0; round < roundsAfterCall1; round += 1) {
      expected *= 1 / 0.999;
    }
    assert.strictEqual(internals(solver).claInc, expected);
    assert.strictEqual(stats1.learnedClauses, solver.stats.learnedClauses, 'call 1 owns all work');

    // A second per-call scope zeroes and refills its own output object…
    const stats2: SolverStats = {
      decisions: 999,
      propagations: 999,
      conflicts: 999,
      restarts: 999,
      learnedClauses: 999,
      learnedClausesCurrent: 999,
      learnedLiterals: 999,
      minimizedLiterals: 999,
    };
    const lifetimeBefore = { ...solver.stats };
    solver.solveAssuming({ x0: Value.TRUE }, stats2);
    assert.strictEqual(
      internals(solver).claInc,
      expected,
      'per-call output zeroing must not reset the lifetime increment',
    );
    assert.strictEqual(
      stats2.conflicts,
      solver.stats.conflicts - lifetimeBefore.conflicts,
      'per-call output carries only call-2 work',
    );
    assert.strictEqual(
      stats2.learnedClausesCurrent,
      solver.stats.learnedClausesCurrent,
      'the live gauge stays absolute',
    );

    // …and the next round CONTINUES the same lifetime decay sequence rather
    // than restarting from one.
    solver.reduceLearnedClauses();
    assert.strictEqual(internals(solver).claInc, expected * (1 / 0.999));
    solver.checkInvariants();
  });
});

describe('Solver automatic reduction cadence', () => {
  it('validates the internal knob and keeps the default exactly 10000', () => {
    for (const value of [
      0,
      -1,
      0.5,
      Number.NaN,
      Number.POSITIVE_INFINITY,
      Number.MAX_SAFE_INTEGER + 1,
    ]) {
      assert.throws(
        () => new Solver(compile(and()), { learnedClauseReductionThreshold: value }),
        /learnedClauseReductionThreshold must be a positive safe integer/,
      );
    }
    for (const value of [undefined, 1, 7, 10_000, Number.MAX_SAFE_INTEGER]) {
      const solver = new Solver(compile(and()), { learnedClauseReductionThreshold: value });
      assert.strictEqual(internals(solver).learnedClauseReductionThreshold, value ?? 10_000);
    }
    assert.strictEqual(
      internals(new Solver(compile(and()))).learnedClauseReductionThreshold,
      10_000,
    );
  });

  it('advances protected-only rounds periodically, independently of restarts and shared stats', () => {
    // Each gadget resolves to (¬a∨¬xi), LBD 2 at levels a@1, xi@2. The
    // positive clause prevents startup PLE without obstructing a=TRUE, xi=FALSE.
    const expr = and(
      ...Array.from({ length: 12 }, (_, index) =>
        and(
          or(not(`x${index}`), 't'),
          or(not('a'), not(`x${index}`), not('t')),
          or('a', `x${index}`, 't'),
        ),
      ),
    );
    const stats: SolverStats = {
      decisions: 999,
      propagations: 999,
      conflicts: 999,
      restarts: 999,
      learnedClauses: 999,
      learnedClausesCurrent: 999,
      learnedLiterals: 999,
      minimizedLiterals: 999,
    };
    for (let run = 0; run < 2; run += 1) {
      const before = { ...stats };
      const solver = new AuditedSolver(compile(expr), {
        stats,
        enablePle: true,
        variablePriority: priority,
        restartPolicy: 'luby',
        restartBaseConflicts: 1,
        learnedClauseReductionThreshold: 3,
        maxConflicts: 13,
      });
      assert.strictEqual(solver.solve(), true);
      assert.strictEqual(expressionValue(expr, solver.model()), Value.TRUE);
      assertModelShape(solver.model(), expr);
      assert.deepStrictEqual(
        solver.reductions.map((round) => round.admissions),
        [3, 6, 9, 12],
      );
      assert.deepStrictEqual(
        solver.reductions.map((round) => round.conflict - before.conflicts),
        [3, 6, 9, 12],
      );
      assert.deepStrictEqual(
        solver.reductions.map((round) => round.after),
        [3, 6, 9, 12],
      );
      assert.ok(solver.reductions.every((round) => round.removed.length === 0));
      assert.ok(solver.learnedLevels.every(({ lbd }) => lbd === 2));
      assert.strictEqual(stats.learnedClauses - before.learnedClauses, 12);
      assert.strictEqual(stats.learnedClausesCurrent - before.learnedClausesCurrent, 12);
      assert.strictEqual(
        stats.restarts - before.restarts,
        7,
        'independent Luby epochs are preserved',
      );
    }
  });

  it('counts admissions, not canonical rediscoveries, toward the next round', () => {
    const base = compile(gadgets(3));
    const solver = new AuditedSolver(base, {
      learnedClauseReductionThreshold: 2,
      variablePriority: priority,
    });
    const first = learnGadget(solver, base, 0);
    for (let repeat = 0; repeat < 5; repeat += 1) {
      assert.strictEqual(
        solver.addLearnedClause({ ...first, lits: [...first.lits].reverse() }),
        first,
      );
    }
    assert.strictEqual(internals(solver).learnedSinceReduction, 1);
    assert.strictEqual(solver.stats.learnedClauses, 1);
    assert.strictEqual(solver.solve(), true);
    assert.deepStrictEqual(
      solver.reductions.map((round) => round.admissions),
      [2],
    );
    assert.strictEqual(internals(solver).learnedSinceReduction, 1);
    assert.strictEqual(solver.stats.learnedClauses, 3);
    assert.strictEqual(expressionValue(gadgets(3), solver.model()), Value.TRUE);
  });

  it('subtracts actual deletions without resetting inherited output-counter offsets', () => {
    const stats: SolverStats = {
      decisions: 999,
      propagations: 999,
      conflicts: 999,
      restarts: 999,
      learnedClauses: 999,
      learnedClausesCurrent: 999,
      learnedLiterals: 999,
      minimizedLiterals: 999,
    };
    for (let run = 0; run < 2; run += 1) {
      const before = { ...stats };
      const base = compile(gadgets(4));
      const solver = new AuditedSolver(base, { stats });
      for (let index = 0; index < 4; index += 1) {
        learnGadget(solver, base, index);
      }
      solver.reduceLearnedClauses();
      assert.strictEqual(solver.reductions[0].removed.length, 2);
      assert.strictEqual(stats.learnedClauses - before.learnedClauses, 4);
      assert.strictEqual(stats.learnedClausesCurrent - before.learnedClausesCurrent, 2);
    }
  });

  it('does not reduce on conflict-free, startup-UNSAT, or below-default-threshold searches', () => {
    for (const [expr, sat] of [
      [and(), true],
      [or(), false],
      [and('a'), true],
      [and('a', not('a')), false],
    ] as const) {
      const solver = new AuditedSolver(compile(expr), { learnedClauseReductionThreshold: 1 });
      assert.strictEqual(solver.solve(), sat);
      assert.deepStrictEqual(solver.reductions, []);
      solver.checkInvariants();
    }
    const solver = new AuditedSolver(compile(gadgets(12)), {
      variablePriority: priority,
      maxConflicts: 13,
    });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.learnedClauses, 12);
    assert.deepStrictEqual(solver.reductions, []);
  });
});

describe('Solver forced reduction search acceptance', () => {
  it('repeatedly deletes real clauses on PHP(6,5), audits every round, and remains deterministic within the unchanged bound', (t) => {
    let first: string | undefined;
    for (let run = 0; run < 2; run += 1) {
      const solver = new AuditedSolver(compile(cnfToExpr(phpCnf(6, 5))), {
        learnedClauseReductionThreshold: 8,
        maxConflicts: 10_000,
      });
      // Independent UNSAT proof: six pigeons cannot occupy five distinct holes.
      assert.strictEqual(solver.solve(), false);
      assert.ok(solver.stats.conflicts < 10_000, 'existing PHP(6,5) learning-test bound');
      assert.ok(solver.reductions.length > 1, 'multiple real reduction rounds');
      const deleting = solver.reductions.filter((round) => round.after < round.before);
      assert.ok(deleting.length > 1, 'multiple OBSERVABLE live-count decreases');
      const removed = solver.reductions.reduce((sum, round) => sum + round.removed.length, 0);
      assert.ok(removed > 0);
      assert.strictEqual(solver.stats.learnedClausesCurrent, solver.stats.learnedClauses - removed);
      assert.ok(
        solver.learnedLevels.some(({ lbd }) => lbd > 2),
        'genuine high-LBD learning',
      );
      for (let index = 0; index < solver.reductions.length; index += 1) {
        assert.strictEqual(solver.reductions[index].admissions, (index + 1) * 8);
      }
      solver.checkInvariants();
      assertGraph(solver);
      const actual = JSON.stringify({
        stats: solver.stats,
        reductions: solver.reductions,
        learning: solver.learnedLevels,
      });
      first ??= actual;
      assert.strictEqual(actual, first, 'identical stats, LBDs, deletions and boundary trace');
      if (run === 0) {
        const lbds = solver.learnedLevels.map(({ lbd }) => lbd);
        t.diagnostic(
          `PHP(6,5), threshold8, cap10000: ${JSON.stringify(solver.stats)}; ${
            solver.reductions.length
          } rounds, ${deleting.length} deleting, ${removed} removed; LBD ${Math.min(
            ...lbds,
          )}..${Math.max(...lbds)}`,
        );
      }
    }
  });

  it('also deletes on a satisfiable implication family with genuine restart interaction', (t) => {
    const expr = and('r', implies('u', 'v'), or('p', 'q'), gadgets(12));
    const base = compile(expr);
    const solver = new AuditedSolver(base, {
      assumptions: { u: Value.TRUE },
      enablePle: true,
      variablePriority: priority,
      learnedClauseReductionThreshold: 3,
      restartPolicy: 'luby',
      restartBaseConflicts: 1,
      maxConflicts: 1_000,
    });
    // Construct and evaluate the independent witness BEFORE asking the solver.
    const witness = Object.fromEntries([
      ['r', Value.TRUE],
      ['u', Value.TRUE],
      ['v', Value.TRUE],
      ['p', Value.TRUE],
      ['q', Value.TRUE],
      ['a', Value.TRUE],
      ['b', Value.TRUE],
      ['t', Value.FALSE],
      ...Array.from({ length: 12 }, (_, index) => [`x${index}`, Value.FALSE]),
    ]);
    assert.strictEqual(expressionValue(expr, witness), Value.TRUE);
    assert.strictEqual(solver.solve(), true);
    assertModelShape(solver.model(), expr);
    assert.strictEqual(expressionValue(expr, solver.model()), Value.TRUE);
    const removed = solver.reductions.reduce((sum, round) => sum + round.removed.length, 0);
    assert.ok(removed > 0, 'SAT acceptance must also exercise actual deletion');
    assert.ok(solver.stats.restarts > 0);
    assert.ok(solver.learnedLevels.every(({ lbd }) => lbd === 3));
    assert.strictEqual(solver.stats.learnedClausesCurrent, solver.stats.learnedClauses - removed);
    for (const name of ['r', 'u', 'v', 'p', 'q']) {
      const variable = base.nameToIndex.get(name);
      assert.ok(variable !== undefined);
      assert.strictEqual(solver.assigns[variable], Value.TRUE);
      assert.strictEqual(solver.level[variable], 0, 'constructor/assumption/implication/PLE roots');
      if (name === 'p' || name === 'q') {
        assert.strictEqual(solver.reason[variable], null, 'actual scoped startup PLE pin');
      }
    }
    t.diagnostic(
      `SAT gadgets, threshold3/base1/cap1000: ${JSON.stringify(solver.stats)}; ${
        solver.reductions.length
      } rounds, ${removed} removed; all learned LBD3`,
    );
  });
});

describe('Solver explicit database/watch/reason invariant checker', () => {
  it('audits empty and singleton learned populations without changing state or counters', () => {
    const base = compile(gadgets(1));
    const solver = new AuditedSolver(base);
    solver.reduceLearnedClauses();
    assert.strictEqual(solver.reductions[0].before, 0);
    assert.strictEqual(solver.reductions[0].after, 0);
    const learned = learnGadget(solver, base, 0);
    solver.reduceLearnedClauses();
    assert.strictEqual(solver.reductions[1].before, 1);
    assert.strictEqual(solver.reductions[1].after, 1, 'floor(1/2) is zero');
    assert.ok(solver.clauses.includes(learned));
    assert.strictEqual(solver.stats.learnedClausesCurrent, 1);
  });

  // These intentionally corrupt isolated fixtures ONLY to prove the checker
  // is effective. They are never solved and are not used as learning premises.
  it('rejects a dangling watch even when the dead object has equal clause contents', () => {
    const solver = new Solver(compile(or('a', 'b', 'c')));
    const clause = solver.clauses[0];
    const dead = { ...clause, lits: [...clause.lits] };
    solver.watches[clause.lits[0]].push({ clause: dead, blocker: dead.lits[1], twin: null });
    assert.throws(() => solver.checkInvariants(), /watch invariant.*not live/);
  });

  it('rejects a dangling reason with equal clause contents', () => {
    const solver = new Solver(compile(and('a')));
    const clause = solver.clauses[0];
    solver.reason[0] = { ...clause, lits: [...clause.lits] };
    assert.throws(() => solver.checkInvariants(), /reason invariant.*not live/);
  });

  it('rejects a missing watch', () => {
    const solver = new Solver(compile(or('a', 'b', 'c')));
    solver.watches[solver.clauses[0].lits[0]].pop();
    assert.throws(() => solver.checkInvariants(), /watch invariant.*missing/);
  });

  it('rejects a duplicate watch reference', () => {
    const solver = new Solver(compile(or('a', 'b', 'c')));
    const clause = solver.clauses[0];
    solver.watches[clause.lits[0]].push({ clause, blocker: clause.lits[1], twin: null });
    assert.throws(() => solver.checkInvariants(), /watch invariant.*duplicate/);
  });

  it('rejects an incorrect watch position and an illegally watched unit', () => {
    const solver = new Solver(compile(or('a', 'b', 'c')));
    const clause = solver.clauses[0];
    solver.watches[clause.lits[0]].pop();
    solver.watches[clause.lits[2]].push({ clause, blocker: clause.lits[1], twin: null });
    assert.throws(() => solver.checkInvariants(), /watch invariant.*incorrect/);
    const unitSolver = new Solver(compile(and('a')));
    unitSolver.watches[0].push({ clause: unitSolver.clauses[0], blocker: 0, twin: null });
    assert.throws(() => unitSolver.checkInvariants(), /watch invariant.*incorrect/);
  });

  it('rejects a stale blocker or a broken twin link', () => {
    // The blocker parity audit: each entry's blocker must be the clause's
    // current OTHER watch, and twins must cross-refer consistently.
    const stale = new Solver(compile(or('a', 'b', 'c')));
    const staleClause = stale.clauses[0];
    const staleEntry = stale.watches[staleClause.lits[0]].find(
      (entry) => entry.clause === staleClause,
    );
    assert.ok(staleEntry !== undefined);
    staleEntry.blocker = staleClause.lits[0];
    assert.throws(() => stale.checkInvariants(), /watch invariant.*stale blocker or twin/);

    const brokenTwin = new Solver(compile(or('a', 'b', 'c')));
    const twinClause = brokenTwin.clauses[0];
    const twinEntry = brokenTwin.watches[twinClause.lits[0]].find(
      (entry) => entry.clause === twinClause,
    );
    assert.ok(twinEntry !== undefined);
    twinEntry.twin = null;
    assert.throws(() => brokenTwin.checkInvariants(), /watch invariant.*stale blocker or twin/);

    const swapped = new Solver(compile(or('a', 'b', 'c')));
    const swappedClause = swapped.clauses[0];
    const first = swapped.watches[swappedClause.lits[0]].find(
      (entry) => entry.clause === swappedClause,
    );
    const second = swapped.watches[swappedClause.lits[1]].find(
      (entry) => entry.clause === swappedClause,
    );
    assert.ok(first !== undefined && second !== undefined);
    // Twins point at the same clause but must track OPPOSITE blockers.
    first.twin = first;
    assert.throws(() => swapped.checkInvariants(), /watch invariant.*stale blocker or twin/);
    assert.strictEqual(second.blocker, swappedClause.lits[0], 'the other entry is untouched');
  });

  it('rejects duplicate database identities and stale, missing, or non-canonical registry entries', () => {
    const duplicate = new Solver(compile(or('a', 'b')));
    duplicate.clauses.push(duplicate.clauses[0]);
    assert.throws(() => duplicate.checkInvariants(), /database invariant.*duplicate/);
    const stale = new Solver(compile(or('a', 'b')));
    internals(stale).clauseByKey.set('stale', stale.clauses[0]);
    assert.throws(() => stale.checkInvariants(), /database invariant.*stale/);
    const missing = new Solver(compile(or('a', 'b')));
    internals(missing).clauseByKey.delete(key(missing.clauses[0]));
    assert.throws(() => missing.checkInvariants(), /database invariant/);
    const wrong = new Solver(compile(and(or('a', 'b'), or('a', 'c'))));
    internals(wrong).clauseByKey.set(key(wrong.clauses[0]), wrong.clauses[1]);
    assert.throws(() => wrong.checkInvariants(), /database invariant.*non-canonical/);
  });

  it('rejects an invalid clause literal or an assignment not explained by its live reason', () => {
    const duplicate = new Solver(compile(or('a', 'b')));
    duplicate.clauses[0].lits.push(duplicate.clauses[0].lits[0]);
    assert.throws(() => duplicate.checkInvariants(), /database invariant.*invalid clause literals/);
    const outOfRange = new Solver(compile(and('a')));
    outOfRange.clauses[0].lits[0] = 100;
    assert.throws(
      () => outOfRange.checkInvariants(),
      /database invariant.*invalid clause literals/,
    );
    const unexplained = new Solver(compile(and('a', or('b', 'c'))));
    unexplained.reason[1] = unexplained.clauses[0];
    assert.throws(() => unexplained.checkInvariants(), /reason invariant.*does not explain/);
  });
});
