import assert from 'node:assert';
import { describe, it } from 'node:test';
import { getAllSolutions } from '../src/index.js';
import type { SolveOptions } from '../src/index.js';
import { compile, isNeg, litValue, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, not, or, Value, xor } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SearchVerdict, SolverStats } from '../src/solver.js';
import {
  assertModelListsEqual,
  assertModelShape,
  expectCompleteModels,
  expressionValue,
  modelKey,
  referenceModels,
  watchesClause,
} from './helpers.js';

const counters = (value = 0): SolverStats => ({
  decisions: value,
  propagations: value,
  conflicts: value,
  restarts: value,
  learnedClauses: value,
  learnedClausesCurrent: value,
  learnedLiterals: value,
  minimizedLiterals: value,
});
const key = (clause: Clause): string => [...clause.lits].sort((a, b) => a - b).join(',');
const pairs = (count: number): BooleanExpr =>
  and(...Array.from({ length: count }, (_, i) => or(`a${i + 1}`, `b${i + 1}`)));

interface Internals {
  readonly clauseByKey: Map<string, Clause>;
  readonly learnedSinceReduction: number;
  readonly enablePle: boolean;
  readonly learnedClauseReductionThreshold: number;
  readonly restartBaseConflicts: number;
  readonly restartPolicy: { readonly kind: 'ema' | 'luby' };
  readonly conflictBudget: number | undefined;
  // Named-variable membership per global variable index (post-add() named
  // indices need not be contiguous; enumeration never adds, so the flag here
  // marks exactly 0..numNamedVars-1).
  readonly named: Uint8Array;
}

// The number of named variables, derived from the named flags rather than the
// pre-add() contiguous-index invariant.
function namedCount(solver: Solver): number {
  let count = 0;
  for (const flag of internals(solver).named) {
    count += flag;
  }
  return count;
}
// Observation only: no tests install arbitrary learned clauses or manufacture
// LBD, activity, assignments, reasons, phases, or counter values in a solver.
const internals = (solver: Solver): Internals => solver as unknown as Internals;

function literal(base: CompiledCnf, name: string, value = Value.TRUE): number {
  const index = base.nameToIndex.get(name);
  assert.ok(index !== undefined);
  return index * 2 + (value === Value.FALSE ? 1 : 0);
}

// Independent implication-graph audit: a reason must have been unit in the
// TRAIL PREFIX preceding its enqueue, regardless of its current watch slots.
function assertReasons(solver: Solver): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (let index = 0; index < solver.trail.length; index += 1) {
    const lit = solver.trail[index];
    const variable = varOf(lit);
    const level = solver.trailLim.filter((boundary) => boundary <= index).length;
    assert.strictEqual(prefix[variable], Value.UNSET);
    assert.strictEqual(solver.level[variable], level);
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.strictEqual(internals(solver).clauseByKey.get(key(reason)), reason);
      assert.ok(reason.lits.includes(lit));
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(litValue(other, prefix), Value.FALSE, 'unit reason at enqueue');
        }
      }
    } else if (level > 0) {
      assert.strictEqual(index, solver.trailLim[level - 1], 'one actual decision per level');
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepStrictEqual(prefix, solver.assigns);
}

function assertFixpoint(solver: Solver): void {
  assert.strictEqual(solver.qhead, solver.trail.length);
  for (const clause of solver.clauses) {
    const values = clause.lits.map((lit) => litValue(lit, solver.assigns));
    assert.ok(
      values.includes(Value.TRUE) || values.filter((value) => value === Value.UNSET).length >= 2,
      'no overlooked unit or conflict after propagation',
    );
  }
  assertReasons(solver);
  solver.checkInvariants();
}

// Operation-local decisions, not an alternate enumeration/search loop. Work
// counters in these fixtures are not presented as production search totals.
function decide(solver: Solver, lit: number): void {
  assert.strictEqual(solver.propagate(), null);
  assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
  solver.newDecisionLevel();
  assert.strictEqual(solver.enqueue(lit, null), true);
}

describe('permanent clause admission for persistent enumeration', () => {
  it('normalizes, drops tautologies, and reuses canonical permanent objects without double counting', () => {
    const base = compile(and(or('a', not('a')), or('b', not('b'))));
    const solver = new Solver(base);
    const a = literal(base, 'a');
    const b = literal(base, 'b');
    const raw = [b, a, b];
    const clause = solver.addPermanentClause(raw);
    assert.ok(clause !== null);
    assert.deepStrictEqual(raw, [b, a, b], 'caller array is not mutated');
    assert.deepStrictEqual(clause.lits, [a, b]);
    assert.strictEqual(clause.learned, false);
    assert.strictEqual(solver.addPermanentClause([a, b, a]), clause);
    assert.strictEqual(solver.addPermanentClause([a, a ^ 1]), null);
    assert.strictEqual(solver.clauses.length, 1);
    assert.deepStrictEqual(solver.stats, counters());
    assertFixpoint(solver);
  });

  it('keeps a root-satisfied insertion safe even when its true literal is behind the watches', () => {
    const base = compile(and('c', or('a', not('a')), or('b', not('b'))));
    const solver = new Solver(base);
    assert.strictEqual(solver.propagate(), null);
    const before = { ...solver.stats };
    const clause = solver.addPermanentClause(['a', 'b', 'c'].map((name) => literal(base, name)));
    assert.ok(clause !== null);
    assert.deepStrictEqual(solver.stats, before, 'satisfied insertion is not a propagation');
    for (let run = 0; run < 2; run += 1) {
      decide(solver, literal(base, 'a', Value.FALSE));
      decide(solver, literal(base, 'b', Value.FALSE));
      assert.strictEqual(solver.propagate(), null);
      assertFixpoint(solver);
      solver.cancelUntil(0);
      assert.strictEqual(solver.assigns[varOf(literal(base, 'c'))], Value.TRUE);
    }
    assert.strictEqual(solver.addPermanentClause([literal(base, 'c')]), base.clauses[0]);
    assert.strictEqual(solver.stats.propagations, before.propagations);
  });

  it('immediately enqueues a nonstructural root unit and propagates its queued consequences', () => {
    const base = compile(and('a', 'b', implies('c', 'd')));
    const solver = new Solver(base);
    assert.strictEqual(solver.propagate(), null);
    const head = solver.qhead;
    assert.strictEqual(head, solver.trail.length, 'all antecedent events already processed');
    const c = literal(base, 'c');
    const clause = solver.addPermanentClause([
      literal(base, 'a', Value.FALSE),
      literal(base, 'b', Value.FALSE),
      c,
    ]);
    assert.ok(clause !== null);
    assert.strictEqual(solver.assigns[varOf(c)], Value.TRUE);
    assert.strictEqual(solver.reason[varOf(c)], clause);
    assert.strictEqual(solver.level[varOf(c)], 0);
    assert.strictEqual(solver.qhead, head, 'the new implication remains queued');
    assert.strictEqual(solver.trail.length, head + 1);
    assert.strictEqual(solver.stats.propagations, 3, 'two original units plus one new root unit');
    assert.strictEqual(clause.lits.length, 3, 'root-false antecedents are not discarded');
    assert.ok(clause.lits.slice(0, 2).includes(c));
    assertReasons(solver);
    solver.checkInvariants();
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.stats.propagations, 4, 'c implies d, without a fabricated event');
    assert.strictEqual(solver.addPermanentClause([...clause.lits].reverse()), clause);
    assert.strictEqual(solver.stats.propagations, 4, 'duplicate is not another enqueue');
    solver.cancelUntil(0);
    assert.deepStrictEqual(solver.model(), { a: 1, b: 1, c: 1, d: 1 });
    assertFixpoint(solver);
  });

  it('keeps a normalized structural unit unwatched, including duplicate admissions', () => {
    const base = compile(or('a', not('a')));
    const solver = new Solver(base);
    const a = literal(base, 'a');
    const unit = solver.addPermanentClause([a, a]);
    assert.ok(unit !== null);
    assert.deepStrictEqual(unit.lits, [a]);
    assert.strictEqual(solver.reason[varOf(a)], unit);
    assert.ok(solver.watches.every((list) => list.length === 0));
    assert.strictEqual(solver.addPermanentClause([a]), unit);
    assert.strictEqual(solver.stats.propagations, 1);
    assert.strictEqual(solver.propagate(), null);
    assertFixpoint(solver);
  });

  it('reports and caches a root conflict without waiting for an already-processed event', () => {
    const base = compile(and('a', 'b'));
    const solver = new Solver(base);
    assert.strictEqual(solver.propagate(), null);
    const clause = solver.addPermanentClause([
      literal(base, 'a', Value.FALSE),
      literal(base, 'b', Value.FALSE),
    ]);
    assert.ok(clause !== null);
    assert.strictEqual(solver.qhead, solver.trail.length);
    assert.strictEqual(solver.propagate(), clause);
    assert.strictEqual(solver.stats.conflicts, 1);
    for (let run = 0; run < 3; run += 1) {
      assert.strictEqual(solver.solve(), false);
    }
    assert.strictEqual(solver.stats.conflicts, 1, 'cached UNSAT is not a fresh conflict');
    solver.checkInvariants();
    assertReasons(solver);
  });

  it('cancels partial non-root assignments before choosing watches or declaring a root unit', () => {
    const base = compile(and('a', or('b', not('b')), or('c', not('c'))));
    const solver = new Solver(base);
    const b = literal(base, 'b');
    const c = literal(base, 'c');
    decide(solver, b);
    assert.strictEqual(solver.propagate(), null);
    // Under a=T@0, b=T@1 this LOOKS unit, but after cancelling b the clause
    // has two live watches (¬b,c). c must NOT be pinned at root.
    const clause = solver.addPermanentClause([literal(base, 'a', Value.FALSE), b ^ 1, c]);
    assert.ok(clause !== null);
    assert.strictEqual(solver.trailLim.length, 0);
    assert.strictEqual(solver.assigns[varOf(b)], Value.UNSET);
    assert.strictEqual(solver.assigns[varOf(c)], Value.UNSET);
    assert.deepStrictEqual(clause.lits.slice(0, 2), [b ^ 1, c]);
    assertFixpoint(solver);
    decide(solver, b);
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.reason[varOf(c)], clause);
    assertFixpoint(solver);
    solver.cancelUntil(0);
    decide(solver, c ^ 1);
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.assigns[varOf(b)], Value.FALSE);
    assert.strictEqual(solver.reason[varOf(b)], clause);
    assertFixpoint(solver);
  });

  it('does not interpret the blocked complete non-root model as permanent UNSAT', () => {
    const expr = and(or('a', not('a')), or('b', not('b')));
    const base = compile(expr);
    const solver = new Solver(base);
    assert.strictEqual(solver.solve(), true);
    const excluded = solver.model();
    assert.deepStrictEqual(excluded, { a: Value.FALSE, b: Value.FALSE });
    solver.addPermanentClause([literal(base, 'a'), literal(base, 'b')]);
    assert.strictEqual(solver.trailLim.length, 0);
    assert.strictEqual(solver.stats.conflicts, 0);
    assertModelListsEqual(
      expectCompleteModels(solver.enumerateModels()),
      referenceModels(expr).filter((model) => modelKey(model) !== modelKey(excluded)),
    );
  });

  it('refuses stale-PLE operation modes and invalid literals rather than guessing', () => {
    const solver = new Solver(compile(or('a', 'b')), { enablePle: true });
    assert.strictEqual(solver.solve(), true, 'the single-shot solve really runs PLE');
    assert.strictEqual(solver.trailLim.length, 0);
    assert.throws(() => solver.enumerateModels(), /model enumeration requires enablePle: false/);
    assert.throws(() => solver.addPermanentClause([0]), /insertion requires enablePle: false/);
    const noPle = new Solver(compile(or('a', 'b')));
    for (const lit of [-1, 4, 0.5, Number.NaN, Number.POSITIVE_INFINITY]) {
      assert.throws(() => noPle.addPermanentClause([lit]), /out-of-range literal/);
    }
    noPle.checkInvariants();
  });
});

// Each gadget derives (¬a ∨ ¬b ∨ ¬xi) by resolving t. The positive clause
// leaves a=b=T, xi=F as a known model and prevents accidental unsatisfiability.
const gadgets = (count: number): BooleanExpr =>
  and(
    ...Array.from({ length: count }, (_, i) =>
      and(
        or(not('a'), not(`x${i}`), 't'),
        or(not('b'), not(`x${i}`), not('t')),
        or('a', 'b', `x${i}`, 't'),
      ),
    ),
  );

function learnGadget(solver: Solver, base: CompiledCnf, expr: BooleanExpr, index: number): Clause {
  for (const name of ['a', 'b', `x${index}`]) {
    decide(solver, literal(base, name));
  }
  const conflict = solver.propagate();
  assert.ok(conflict !== null);
  assertReasons(solver);
  const { learned, backjumpLevel } = solver.analyze(conflict);
  assert.strictEqual(learned.lbd, 3);
  assert.strictEqual(backjumpLevel, 2);
  // Non-vacuous independent truth table: all base models, including those
  // violating the decisions that exposed this conflict, satisfy the result.
  const models = referenceModels(expr);
  assert.ok(models.length > 0);
  for (const model of models) {
    assert.ok(
      learned.lits.some(
        (lit) => model[base.indexToName[varOf(lit)]] === (isNeg(lit) ? Value.FALSE : Value.TRUE),
      ),
    );
  }
  const registered = solver.addLearnedClause(learned);
  solver.cancelUntil(backjumpLevel);
  assert.strictEqual(solver.enqueue(learned.lits[0], registered), true);
  assertReasons(solver);
  solver.cancelUntil(0);
  return registered;
}

describe('canonical permanent promotion and learned bookkeeping', () => {
  it('promotes a genuinely learned high-LBD object after watch movement and protects its permanent role', () => {
    const expr = gadgets(3);
    const base = compile(expr);
    const solver = new Solver(base);
    const learned = learnGadget(solver, base, expr, 0);
    const consequence = { ...learned, lits: [...learned.lits] };
    decide(solver, literal(base, 'x0'));
    assert.strictEqual(solver.propagate(), null);
    assert.ok(!learned.lits.slice(0, 2).includes(literal(base, 'x0', Value.FALSE)));
    solver.cancelUntil(0);
    const { activity, lbd } = learned;
    assert.strictEqual(solver.addPermanentClause([...learned.lits].reverse()), learned);
    assert.strictEqual(learned.learned, false);
    assert.strictEqual(learned.activity, activity);
    assert.strictEqual(learned.lbd, lbd);
    assert.strictEqual(lbd, 3, 'role, not an invented low LBD, supplies protection');
    assert.strictEqual(solver.stats.learnedClauses, 1);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 0);
    assert.strictEqual(internals(solver).learnedSinceReduction, 1, 'cadence does not rewind');
    assert.strictEqual(solver.addPermanentClause([...learned.lits, learned.lits[0]]), learned);
    assert.strictEqual(solver.addLearnedClause(consequence), learned, 'reverse rediscovery');
    assert.strictEqual(learned.learned, false, 'learning cannot demote a permanent object');
    assert.strictEqual(solver.stats.learnedClausesCurrent, 0);
    assert.strictEqual(internals(solver).learnedSinceReduction, 1);
    const second = learnGadget(solver, base, expr, 1);
    const third = learnGadget(solver, base, expr, 2);
    solver.reduceLearnedClauses();
    assert.ok(solver.clauses.includes(learned));
    assert.ok(!solver.clauses.includes(second), 'genuine eligible deletion alongside promotion');
    assert.ok(solver.clauses.includes(third));
    assert.strictEqual(solver.stats.learnedClauses, 3);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 1);
    assert.strictEqual(internals(solver).clauseByKey.get(key(learned)), learned);
    assert.ok(!internals(solver).clauseByKey.has(key(second)));
    assertFixpoint(solver);
  });

  it('promotes a live root reason in place without replaying or losing its implication', () => {
    const expr = gadgets(1);
    const base = compile(expr);
    const solver = new Solver(base);
    const learned = learnGadget(solver, base, expr, 0);
    solver.addPermanentClause([literal(base, 'a')]);
    solver.addPermanentClause([literal(base, 'b')]);
    assert.strictEqual(solver.propagate(), null);
    const variable = varOf(literal(base, 'x0'));
    assert.strictEqual(solver.reason[variable], learned);
    assert.strictEqual(solver.level[variable], 0);
    assert.strictEqual(learned.lbd, 3);
    const trail = [...solver.trail];
    const stats = { ...solver.stats };
    assert.strictEqual(solver.addPermanentClause([...learned.lits].reverse()), learned);
    assert.strictEqual(solver.reason[variable], learned);
    assert.deepStrictEqual(solver.trail, trail);
    assert.deepStrictEqual(solver.stats, { ...stats, learnedClausesCurrent: 0 });
    solver.reduceLearnedClauses();
    assert.ok(solver.clauses.includes(learned));
    assertFixpoint(solver);
  });

  it('promotes a learned structural unit without introducing watches or another admission', () => {
    const expr = and(or('x', 't'), or('x', not('t')));
    const base = compile(expr);
    const solver = new Solver(base);
    decide(solver, literal(base, 'x', Value.FALSE));
    const conflict = solver.propagate();
    assert.ok(conflict !== null);
    const { learned } = solver.analyze(conflict);
    assert.deepStrictEqual(learned.lits, [literal(base, 'x')]);
    assert.ok(referenceModels(expr).every((model) => model.x === Value.TRUE));
    solver.addLearnedClause(learned);
    solver.cancelUntil(0);
    assert.strictEqual(solver.enqueue(learned.lits[0], learned), true);
    assert.strictEqual(solver.addPermanentClause([...learned.lits, ...learned.lits]), learned);
    assert.strictEqual(solver.stats.learnedClauses, 1);
    assert.strictEqual(solver.stats.learnedClausesCurrent, 0);
    assert.ok(solver.watches.every((list) => !watchesClause(list, learned)));
    solver.checkInvariants();
    assertReasons(solver);
  });
});

// Observation-only instrumentation around the inherited production loop.
// Permanent identities survive EVERY reduction, and all automatic reduction
// boundaries get a complete database/watch/canonical audit, even in k=10.
class EnumerationAudit extends Solver {
  readonly blockers = new Set<Clause>();
  readonly liveLearned = new Set<Clause>();
  readonly snapshots: Array<{ models: number; total: number; live: number }> = [];
  modelsProduced = 0;
  solveCalls = 0;
  reductions = 0;
  deletingRounds = 0;
  deleted = 0;
  retainedReasons = 0;
  retainedHighLbdReasons = 0;
  peakLive = 0;
  firstDeletionAt = -1;
  totalAtFirstDeletion = 0;

  constructor(
    readonly base: CompiledCnf,
    options?: ConstructorParameters<typeof Solver>[1],
  ) {
    super(base, options);
  }

  // Intercepts the tri-state core driver: enumerateSlices dispatches through
  // search(), so this single override covers every per-model search. These
  // enumerations run without budgets, so 'unknown' never occurs here.
  override search(): SearchVerdict {
    assert.strictEqual(this.trailLim.length, 0, 'each enumeration search starts at root');
    const before = { ...this.stats };
    this.solveCalls += 1;
    const result = super.search();
    for (const counter of [
      'decisions',
      'propagations',
      'conflicts',
      'restarts',
      'learnedClauses',
    ] as const) {
      assert.ok(this.stats[counter] >= before[counter], `${counter} accumulates on one instance`);
    }
    assert.strictEqual(this.stats.learnedClausesCurrent, this.liveLearned.size);
    return result;
  }

  override model(): VariableAssignments {
    const model = super.model();
    this.modelsProduced += 1;
    return model;
  }

  override addLearnedClause(learned: Clause): Clause {
    const before = this.stats.learnedClauses;
    const result = super.addLearnedClause(learned);
    if (result.learned) {
      const isNew = !this.liveLearned.has(result);
      assert.strictEqual(this.stats.learnedClauses, before + (isNew ? 1 : 0));
      this.liveLearned.add(result);
    } else {
      assert.strictEqual(
        this.stats.learnedClauses,
        before,
        'permanent rediscovery is not learning',
      );
    }
    assert.strictEqual(this.stats.learnedClausesCurrent, this.liveLearned.size);
    this.peakLive = Math.max(this.peakLive, this.liveLearned.size);
    return result;
  }

  override addPermanentClause(raw: readonly number[]): Clause | null {
    // Named-flag-aware blocker audit: the blocker covers exactly the flagged
    // named variables (enumeration never calls add(), so the flags mark
    // precisely 0..numNamedVars-1) and never an auxiliary index.
    const flags = internals(this).named;
    assert.strictEqual(raw.length, namedCount(this));
    assert.strictEqual(new Set(raw.map(varOf)).size, namedCount(this));
    for (const lit of raw) {
      assert.strictEqual(flags[varOf(lit)], 1, 'blockers never mention auxiliaries');
      assert.strictEqual(
        litValue(lit, this.assigns),
        Value.FALSE,
        'excludes the just-returned model',
      );
    }
    const root = this.trail.filter((lit) => this.level[varOf(lit)] === 0);
    const reasons = root.map((lit) => this.reason[varOf(lit)]);
    const activity = this.activity.slice();
    const phases = this.polarity.slice();
    const stats = { ...this.stats };
    const size = this.clauses.length;
    const result = super.addPermanentClause(raw);
    assert.ok(result !== null);
    assert.strictEqual(result.learned, false);
    // A valid model cannot falsify any live clause, so its complete blocker
    // must be new. Promotion has separate non-vacuous operation-local tests.
    assert.strictEqual(this.clauses.length, size + 1);
    assert.strictEqual(internals(this).clauseByKey.get(key(result)), result);
    this.blockers.add(result);
    assert.strictEqual(this.trailLim.length, 0);
    assert.deepStrictEqual(
      this.trail.slice(0, root.length),
      root,
      'root facts never replay or drop',
    );
    for (let i = 0; i < root.length; i += 1) {
      assert.strictEqual(this.reason[varOf(root[i])], reasons[i]);
    }
    assert.deepStrictEqual(this.activity, activity, 'VSIDS scores survive model boundaries');
    for (let variable = 0; variable < phases.length; variable += 1) {
      if (this.assigns[variable] === Value.UNSET) {
        assert.strictEqual(this.polarity[variable], phases[variable], 'cancelled phases survive');
      } else {
        assert.strictEqual(this.polarity[variable], this.assigns[variable]);
      }
    }
    assert.deepStrictEqual(this.stats, {
      ...stats,
      propagations: stats.propagations + this.trail.length - root.length,
    });
    assert.strictEqual(this.stats.learnedClausesCurrent, this.liveLearned.size);
    assertReasons(this);
    if (this.modelsProduced % 19_683 === 0) {
      this.snapshots.push({
        models: this.modelsProduced,
        total: this.stats.learnedClauses,
        live: this.stats.learnedClausesCurrent,
      });
    }
    return result;
  }

  override reduceLearnedClauses(): void {
    const before = [...this.clauses];
    const reasons = [...this.reason];
    const learned = before.filter((clause) => clause.learned);
    const total = this.stats.learnedClauses;
    assert.strictEqual(this.stats.learnedClausesCurrent, learned.length);
    super.reduceLearnedClauses();
    const retained = new Set(this.clauses);
    const removed = new Set(learned.filter((clause) => !retained.has(clause)));
    let next = 0;
    for (const clause of before) {
      if (removed.has(clause)) {
        assert.ok(clause.lbd > 2);
        assert.ok(!reasons.includes(clause), 'all active reasons are protected');
        assert.ok(!internals(this).clauseByKey.has(key(clause)), 'deleted key detached');
        this.liveLearned.delete(clause);
      } else {
        assert.strictEqual(this.clauses[next++], clause, 'every survivor keeps identity and order');
        if (reasons.includes(clause)) {
          this.retainedReasons += 1;
          if (clause.learned && clause.lbd > 2) {
            this.retainedHighLbdReasons += 1;
          }
        }
      }
    }
    assert.strictEqual(next, this.clauses.length, 'no newly invented clauses during reduction');
    assert.strictEqual(this.stats.learnedClauses, total, 'total never decreases');
    assert.strictEqual(this.stats.learnedClausesCurrent, learned.length - removed.size);
    assert.strictEqual(this.stats.learnedClausesCurrent, this.liveLearned.size);
    for (let i = 0; i < reasons.length; i += 1) {
      assert.strictEqual(this.reason[i], reasons[i]);
    }
    this.reductions += 1;
    if (removed.size > 0) {
      this.deletingRounds += 1;
      this.deleted += removed.size;
      if (this.firstDeletionAt < 0) {
        this.firstDeletionAt = this.modelsProduced;
        this.totalAtFirstDeletion = total;
      }
    }
    this.checkInvariants();
    assertReasons(this);
  }
}

describe('persistent enumeration production path', () => {
  it('compiles once and uses one solver and the shared loop; its exact small trace explains the counters', (t) => {
    let reads = 0;
    const expr = {
      get or() {
        reads += 1;
        return ['a', 'b'];
      },
    };
    compile(expr);
    const oneCompilationReads = reads;
    reads = 0;
    const instances = new Set<Solver>();
    const searches: Array<{ sat: boolean; stats: SolverStats; root: number[] }> = [];
    const search = Solver.prototype.search;
    const enumerate = Solver.prototype.enumerateModels;
    let loopCalls = 0;
    t.mock.method(Solver.prototype, 'enumerateModels', function (this: Solver) {
      loopCalls += 1;
      instances.add(this);
      return enumerate.call(this);
    });
    // The shared loop dispatches each per-model search through search().
    t.mock.method(Solver.prototype, 'search', function (this: Solver) {
      instances.add(this);
      const verdict = search.call(this);
      this.checkInvariants();
      assertReasons(this);
      searches.push({
        sat: verdict === 'sat',
        stats: { ...this.stats },
        root: this.trail.filter((lit) => this.level[varOf(lit)] === 0),
      });
      return verdict;
    });
    const stats = counters(999);
    const models = expectCompleteModels(getAllSolutions(expr, { stats }));
    assert.strictEqual(
      reads,
      oneCompilationReads,
      'one variable collection/compilation, not per model',
    );
    assert.strictEqual(loopCalls, 1);
    assert.strictEqual(instances.size, 1, 'all searches share the SAME instance');
    assertModelListsEqual(models, referenceModels(or('a', 'b')));
    assert.deepStrictEqual(searches, [
      { sat: true, stats: { ...counters(), decisions: 1, propagations: 1 }, root: [] },
      {
        sat: true,
        stats: {
          ...counters(),
          decisions: 3,
          propagations: 3,
          conflicts: 1,
          learnedClauses: 1,
          learnedClausesCurrent: 1,
          learnedLiterals: 1,
        },
        root: [0],
      },
      {
        sat: true,
        stats: {
          ...counters(),
          decisions: 3,
          propagations: 4,
          conflicts: 1,
          learnedClauses: 1,
          learnedClausesCurrent: 1,
          learnedLiterals: 1,
        },
        root: [0, 2],
      },
      {
        sat: false,
        stats: {
          ...counters(),
          decisions: 3,
          propagations: 4,
          conflicts: 2,
          learnedClauses: 1,
          learnedClausesCurrent: 1,
          learnedLiterals: 1,
        },
        root: [0, 2],
      },
    ]);
    assert.deepStrictEqual(stats, searches[3].stats);
    const solver = [...instances][0];
    assert.strictEqual(solver.stats, stats);
    assert.strictEqual(solver.clauses.filter((clause) => clause.learned).length, 1);
    assert.strictEqual(solver.clauses.filter((clause) => !clause.learned).length, 4);
  });

  it('reads constant assumptions once, keeps them at root, and zeroes every supplied counter exactly once', (t) => {
    const values = counters(999);
    const zeros = counters();
    const stats = Object.defineProperties(
      {},
      Object.fromEntries(
        (Object.keys(values) as Array<keyof SolverStats>).map((name) => [
          name,
          {
            enumerable: true,
            get: () => values[name],
            set: (value: number) => {
              if (value === 0) zeros[name] += 1;
              values[name] = value;
            },
          },
        ]),
      ),
    ) as SolverStats;
    let reads = 0;
    const assumptions = {
      get a1() {
        reads += 1;
        return Value.TRUE;
      },
      b2: Value.UNSET,
    };
    const original = Solver.prototype.search;
    const instances = new Set<Solver>();
    t.mock.method(Solver.prototype, 'search', function (this: Solver) {
      instances.add(this);
      assert.strictEqual(this.assigns[0], Value.TRUE);
      assert.strictEqual(this.level[0], 0);
      assert.strictEqual(this.reason[0], null, 'constructor assumption, not a fake implication');
      assert.strictEqual(this.trail.filter((lit) => varOf(lit) === 0).length, 1);
      return original.call(this);
    });
    const expr = pairs(3);
    const models = expectCompleteModels(getAllSolutions(expr, { assumptions, stats }));
    assert.strictEqual(reads, 1);
    assert.strictEqual(instances.size, 1);
    assert.deepStrictEqual(zeros, counters(1));
    assert.strictEqual(models.length, 2 * 3 ** 2);
    assertModelListsEqual(
      models,
      referenceModels(expr).filter((model) => model.a1 === Value.TRUE),
    );
    for (const model of models) {
      assertModelShape(model, expr);
      assert.strictEqual(expressionValue(expr, model), Value.TRUE);
      assert.strictEqual(model.a1, Value.TRUE);
    }
  });

  it('does not forward internal constructor knobs through public options', (t) => {
    const original = Solver.prototype.enumerateModels;
    t.mock.method(Solver.prototype, 'enumerateModels', function (this: Solver) {
      assert.strictEqual(internals(this).enablePle, false);
      assert.strictEqual(internals(this).learnedClauseReductionThreshold, 10_000);
      assert.strictEqual(internals(this).restartBaseConflicts, 100);
      assert.strictEqual(internals(this).restartPolicy.kind, 'ema');
      assert.strictEqual(internals(this).conflictBudget, undefined);
      return original.call(this);
    });
    const extra = {
      enablePle: true,
      learnedClauseReductionThreshold: 1,
      restartBaseConflicts: 1,
      restartPolicy: 'luby',
      // The retired throwing cap stays a non-forwarded unknown knob; the
      // public conflictBudget is a real SolveOptions member and belongs to
      // the budget contract tests, not this bag.
      maxConflicts: 0,
    } as SolveOptions;
    assert.strictEqual(expectCompleteModels(getAllSolutions(or('a', 'b'), extra)).length, 3);
  });

  it('validates all assumptions even on empty/known-UNSAT formulas and rejects Boolean values', () => {
    for (const expr of [and(), or(), and(or(), 'a'), and('a', not('a'))]) {
      for (const value of [Value.UNSET, Value.FALSE, Value.TRUE]) {
        assert.throws(
          () => getAllSolutions(expr, { assumptions: { missing: value } }),
          /unknown assumption variable: "missing"/,
        );
      }
    }
    for (const value of [true, false, 2, null, undefined, Number.NaN, '1']) {
      for (const expr of [and('a'), and(or(), 'a')]) {
        const assumptions = { a: value } as unknown as VariableAssignments;
        const stats = counters(999);
        assert.throws(
          () => getAllSolutions(expr, { assumptions, stats }),
          /invalid assumption value/,
        );
        assert.strictEqual(stats.decisions, 0, 'zeroing precedes validation');
      }
    }
  });

  it('terminates zero-named enumeration with exactly one permanent empty blocker', () => {
    const solver = new EnumerationAudit(compile(and()), { learnedClauseReductionThreshold: 1 });
    assert.deepStrictEqual(solver.enumerateModels(), { status: 'complete', models: [{}] });
    assert.strictEqual(solver.modelsProduced, 1);
    assert.strictEqual(solver.solveCalls, 2);
    assert.strictEqual(solver.blockers.size, 1);
    assert.deepStrictEqual([...solver.blockers][0].lits, []);
    assert.deepStrictEqual(solver.stats, { ...counters(), conflicts: 1 });
    assert.deepStrictEqual(solver.enumerateModels(), { status: 'complete', models: [] });
    assert.deepStrictEqual(solver.stats, { ...counters(), conflicts: 1 });
    solver.checkInvariants();
    const stats = counters(999);
    assert.deepStrictEqual(getAllSolutions(or(), { stats }), { status: 'complete', models: [] });
    assert.deepStrictEqual(stats, counters(), 'compiler-known empty-clause UNSAT needs no search');
  });

  it('keeps the two PLE counterexamples complete, including constant assumptions and auxiliaries', () => {
    const subsets: VariableAssignments[] = [
      {},
      { a: Value.FALSE },
      { a: Value.TRUE },
      { a: Value.UNSET },
    ];
    for (const expr of [or('v', 'a'), and(or('a', 'b'), or(not('a'), 'c')), xor('a', 'b')]) {
      const reference = referenceModels(expr);
      for (const assumptions of subsets) {
        const expected = reference.filter((model) =>
          Object.entries(assumptions).every(
            ([name, value]) => value === Value.UNSET || model[name] === value,
          ),
        );
        const solver = new EnumerationAudit(compile(expr), {
          enablePle: false,
          assumptions,
          learnedClauseReductionThreshold: 1,
        });
        const models = expectCompleteModels(solver.enumerateModels());
        assertModelListsEqual(models, expected);
        for (const model of models) {
          assertModelShape(model, expr);
          assert.strictEqual(expressionValue(expr, model), Value.TRUE);
        }
        solver.checkInvariants();
      }
    }
  });

  it('preserves constant assumptions across genuine restarts and deletion on the shared loop', () => {
    // pairs(5): deep enough trails that the reducible tier (LBD > 2) is
    // genuinely populated, so the two-tier policy really deletes — pairs(4)
    // learned almost exclusively glue-tier clauses, which the pinned policy
    // correctly never deletes. The reference is combinatorial (the naive
    // enumerator caps at 8 variables), double-checked by the evaluator.
    const expr = pairs(5);
    const assumptions = { a1: Value.TRUE, b2: Value.FALSE };
    // Pair 1 admits (T,F),(T,T) under a1=TRUE; b2=FALSE forces pair 2 to
    // (T,F); the other three pairs each admit (F,T),(T,F),(T,T).
    const pairChoices = [
      [Value.FALSE, Value.TRUE],
      [Value.TRUE, Value.FALSE],
      [Value.TRUE, Value.TRUE],
    ] as const;
    const expected: VariableAssignments[] = [];
    for (const b1 of [Value.FALSE, Value.TRUE] as const) {
      for (const [a3, b3] of pairChoices) {
        for (const [a4, b4] of pairChoices) {
          for (const [a5, b5] of pairChoices) {
            expected.push({
              a1: Value.TRUE,
              b1,
              a2: Value.TRUE,
              b2: Value.FALSE,
              a3,
              b3,
              a4,
              b4,
              a5,
              b5,
            });
          }
        }
      }
    }
    assert.strictEqual(expected.length, 2 * 3 ** 3);
    for (const model of expected) {
      assert.strictEqual(expressionValue(expr, model), Value.TRUE, 'reference is sound');
    }
    let previous: { models: VariableAssignments[]; stats: SolverStats } | undefined;
    for (let run = 0; run < 2; run += 1) {
      const base = compile(expr);
      class AssumptionAudit extends EnumerationAudit {
        override search(): SearchVerdict {
          for (const [name, value] of Object.entries(assumptions)) {
            const variable = varOf(literal(base, name));
            assert.strictEqual(this.assigns[variable], value);
            assert.strictEqual(this.level[variable], 0);
            assert.strictEqual(this.reason[variable], null);
          }
          return super.search();
        }
      }
      const solver = new AssumptionAudit(base, {
        assumptions,
        enablePle: false,
        restartPolicy: 'luby',
        restartBaseConflicts: 1,
        learnedClauseReductionThreshold: 1,
      });
      const models = expectCompleteModels(solver.enumerateModels());
      assertModelListsEqual(models, expected);
      for (const model of models) {
        assertModelShape(model, expr);
        assert.strictEqual(expressionValue(expr, model), Value.TRUE);
        assert.strictEqual(model.a1, Value.TRUE);
        assert.strictEqual(model.b2, Value.FALSE);
      }
      assert.ok(solver.stats.restarts > 0, 'not just enumeration root cancellations');
      assert.ok(solver.deleted > 0, 'real automatic deletions during restarted enumeration');
      assert.strictEqual(solver.stats.learnedClauses, solver.deleted + solver.liveLearned.size);
      const current = { models, stats: { ...solver.stats } };
      previous ??= current;
      assert.deepStrictEqual(current, previous, 'fixed internal knobs remain deterministic');
      solver.checkInvariants();
    }
  });

  it('matches the independent reference and mathematical product at small k, including learned entailment', () => {
    for (let k = 0; k <= 4; k += 1) {
      const expr = pairs(k);
      const reference = referenceModels(expr);
      // Each disjoint pair admits precisely FT, TF, TT: independent choices
      // multiply. The k=0 empty product is one, not zero.
      assert.strictEqual(reference.length, 3 ** k);
      const base = compile(expr);
      class TruthTableAudit extends EnumerationAudit {
        remaining = [...reference];
        nonvacuousAnalyses = 0;
        override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
          assertReasons(this);
          const result = super.analyze(conflict);
          for (const model of this.remaining) {
            assert.ok(
              result.learned.lits.some(
                (lit) =>
                  model[base.indexToName[varOf(lit)]] === (isNeg(lit) ? Value.FALSE : Value.TRUE),
              ),
              'learned consequence of the strengthened formula, not just the original AST',
            );
          }
          if (this.remaining.length > 0) this.nonvacuousAnalyses += 1;
          return result;
        }
        override addPermanentClause(raw: readonly number[]): Clause | null {
          const remaining = this.remaining.filter((model) =>
            raw.some(
              (lit) =>
                model[base.indexToName[varOf(lit)]] === (isNeg(lit) ? Value.FALSE : Value.TRUE),
            ),
          );
          assert.strictEqual(
            remaining.length,
            this.remaining.length - 1,
            'one reference model excluded',
          );
          this.remaining = remaining;
          return super.addPermanentClause(raw);
        }
      }
      const solver = new TruthTableAudit(base, { learnedClauseReductionThreshold: 1 });
      const actual = expectCompleteModels(solver.enumerateModels());
      assert.strictEqual(actual.length, 3 ** k);
      assertModelListsEqual(actual, reference);
      assertModelListsEqual(expectCompleteModels(getAllSolutions(expr)), reference);
      assert.strictEqual(solver.remaining.length, 0);
      if (k > 0) assert.ok(solver.nonvacuousAnalyses > 0);
      solver.checkInvariants();
    }
  });

  it('enumerates exactly 3^10 distinct total models with genuine mid-enumeration reduction and bounded live learning', (t) => {
    // Calibrated only AFTER mathematical count, strict per-model validity,
    // uniqueness and small-k reference checks: threshold32 observed peak103,
    // total29524/live87 with29437 actual deletions. Fix the bound at256 (2x
    // peak rounded up to a power of two), not a sum across disposable solvers.
    // Protected/permanent clauses are not suppressed to meet this bound;
    // blockers intentionally grow to59049. No blanket memory or speedup claim.
    // Re-observed under the task-5cad two-tier/decayed-activity/dynamic-LBD
    // policy: the IDENTICAL 29525-conflict trajectory now peaks at live120
    // (final live111, 29413 deletions in 922 deleting rounds) — comfortably
    // within the unchanged bound.
    const LIVE_LEARNED_BOUND = 256;
    const expr = pairs(10);
    const solver = new EnumerationAudit(compile(expr), {
      enablePle: false,
      learnedClauseReductionThreshold: 32,
      conflictBudget: 295_250, // 10x the independently validated 29525-conflict calibration
    });
    // One enumeration-wide budget spans every model search plus the terminal
    // search; the calibrated 29525 conflicts never approach it, so the run
    // completes rather than returning 'unknown'.
    const models = expectCompleteModels(solver.enumerateModels());
    assert.strictEqual(models.length, 59_049);
    assert.strictEqual(models.length, 3 ** 10);
    const keys = new Set<string>();
    for (const model of models) {
      assertModelShape(model, expr);
      assert.strictEqual(expressionValue(expr, model), Value.TRUE);
      // Independent of the solver/compiler: each pair must be FT, TF or TT.
      for (let i = 1; i <= 10; i += 1) {
        assert.ok(model[`a${i}`] === Value.TRUE || model[`b${i}`] === Value.TRUE);
      }
      keys.add(modelKey(model));
    }
    assert.strictEqual(
      keys.size,
      59_049,
      'valid + unique + exact product count proves completeness',
    );
    assert.strictEqual(solver.solveCalls, models.length + 1);
    assert.strictEqual(solver.blockers.size, models.length);
    assert.ok(solver.deletingRounds > 1);
    assert.ok(solver.firstDeletionAt > 0 && solver.firstDeletionAt < models.length / 2);
    assert.ok(solver.stats.learnedClauses > solver.totalAtFirstDeletion);
    assert.ok(solver.retainedReasons > 0);
    assert.ok(
      solver.retainedHighLbdReasons > 0,
      'genuine high-LBD reason retention during deletion',
    );
    assert.ok(
      solver.peakLive < LIVE_LEARNED_BOUND,
      `peak live ${solver.peakLive} < ${LIVE_LEARNED_BOUND}`,
    );
    assert.strictEqual(solver.stats.learnedClausesCurrent, solver.liveLearned.size);
    assert.strictEqual(solver.stats.learnedClauses, solver.deleted + solver.liveLearned.size);
    assert.strictEqual(solver.clauses.length, 10 + models.length + solver.liveLearned.size);
    assert.strictEqual(solver.snapshots.length, 3);
    for (let i = 1; i < solver.snapshots.length; i += 1) {
      assert.ok(
        solver.snapshots[i].total > solver.snapshots[i - 1].total,
        'learning continues throughout enumeration',
      );
    }
    const live = new Set(solver.clauses);
    for (const blocker of solver.blockers) {
      assert.ok(live.has(blocker));
      assert.strictEqual(blocker.learned, false);
    }
    solver.checkInvariants();
    assertReasons(solver);
    const final = { ...solver.stats };
    assert.strictEqual(solver.solve(), false);
    assert.deepStrictEqual(solver.stats, final, 'terminal UNSAT is cached');
    t.diagnostic(
      `k10/threshold32: ${JSON.stringify(final)}; ${solver.reductions} reductions, ${
        solver.deletingRounds
      } deleting, ${solver.deleted} deleted; first deletion after model${
        solver.firstDeletionAt
      }; peak live${solver.peakLive}<${LIVE_LEARNED_BOUND}; high-LBD reason retentions${
        solver.retainedHighLbdReasons
      }; snapshots${JSON.stringify(solver.snapshots)}`,
    );
  });
});
