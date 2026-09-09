// Observation-only tooling for the incremental production path. No fixture
// installs learned clauses, assignments, scores, LBDs, or internal counters.
import assert from 'node:assert';
import { isNeg, litValue, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { RestartPolicy, SolverStats } from '../src/solver.js';
import {
  assertModelShape,
  assertWatchListsSurvive,
  expressionValue,
  snapshotWatches,
} from './helpers.js';

export const counters = (value = 0): SolverStats => ({
  decisions: value,
  propagations: value,
  conflicts: value,
  restarts: value,
  learnedClauses: value,
  learnedClausesCurrent: value,
  learnedLiterals: value,
  minimizedLiterals: value,
});

export interface Internals {
  readonly decisionHeap: readonly number[];
  readonly heapPosition: Int32Array;
  readonly unassignedNamed: number;
  readonly varInc: number;
  readonly learnedSinceReduction: number;
  readonly conflictsSoFar: number;
  readonly permanentUnsat: boolean;
  readonly incrementalCallActive: boolean;
  readonly enablePle: boolean;
  readonly restartBaseConflicts: number;
  readonly restartPolicy: RestartPolicy;
  readonly learnedClauseReductionThreshold: number;
  readonly maxConflicts: number | undefined;
  readonly propagationCursor: {
    event: number;
    falseLit: number;
    phase: 'binary' | 'long';
    nextWatch: number;
  } | null;
  readonly scheduling: { quantum: number; remaining: number } | null;
  readonly searchState: { phase: 'startup' | 'search' | 'prefix' } | null;
}

export const internals = (solver: Solver): Internals => solver as unknown as Internals;

export function literal(base: CompiledCnf, name: string, value = Value.TRUE): number {
  const variable = base.nameToIndex.get(name);
  assert.ok(variable !== undefined);
  return variable * 2 + (value === Value.FALSE ? 1 : 0);
}

export function extendsAssumptions(
  model: VariableAssignments,
  assumptions: VariableAssignments,
): boolean {
  return Object.entries(assumptions).every(
    ([name, value]) =>
      Object.hasOwn(model, name) && (value === Value.UNSET || model[name] === value),
  );
}

// Expected models come from the AST truth table, NEVER an earlier solver call.
// Check actual models' assumptions directly as well as reference filtering.
export function assertResult(
  expr: BooleanExpr,
  assumptions: VariableAssignments,
  reference: readonly VariableAssignments[],
  actual: VariableAssignments | null,
): void {
  const expectedSat = reference.some((model) => extendsAssumptions(model, assumptions));
  assert.strictEqual(actual !== null, expectedSat, 'incremental reference verdict');
  if (actual === null) return;
  assertModelShape(actual, expr);
  assert.strictEqual(
    expressionValue(expr, actual),
    Value.TRUE,
    'reference-valid incremental model',
  );
  for (const [name, value] of Object.entries(assumptions)) {
    assert.ok(Object.hasOwn(actual, name), 'own assumption key');
    if (value !== Value.UNSET) {
      assert.strictEqual(actual[name], value, `model must extend ${JSON.stringify(name)}`);
    }
  }
}

export function assertHeap(solver: Solver): void {
  const { decisionHeap: heap, heapPosition: positions, unassignedNamed } = internals(solver);
  assert.strictEqual(new Set(heap).size, heap.length, 'unique heap entries');
  for (let index = 0; index < heap.length; index += 1) {
    const variable = heap[index];
    assert.ok(variable >= 0 && variable < positions.length, 'named heap entries only');
    assert.strictEqual(positions[variable], index);
    if (index > 0) {
      const parent = heap[Math.floor((index - 1) / 2)];
      assert.ok(
        solver.activity[parent] > solver.activity[variable] ||
          (solver.activity[parent] === solver.activity[variable] && parent < variable),
        'heap orders actual VSIDS scores with index ties',
      );
    }
  }
  let unset = 0;
  for (let variable = 0; variable < positions.length; variable += 1) {
    if (positions[variable] >= 0) assert.strictEqual(heap[positions[variable]], variable);
    if (solver.assigns[variable] === Value.UNSET) {
      unset += 1;
      assert.ok(positions[variable] >= 0, 'no unassigned candidate lost between calls');
    }
  }
  assert.strictEqual(unassignedNamed, unset);
}

export function assertReasons(solver: Solver): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (const [index, lit] of solver.trail.entries()) {
    const variable = varOf(lit);
    const level = solver.trailLim.filter((boundary) => boundary <= index).length;
    assert.strictEqual(prefix[variable], Value.UNSET, 'unique trail variable');
    assert.strictEqual(
      solver.level[variable],
      level,
      'dummy boundaries preserve assignment levels',
    );
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.ok(solver.clauses.includes(reason), 'canonical live reason');
      assert.ok(reason.lits.includes(lit));
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(litValue(other, prefix), Value.FALSE, 'reason was unit at enqueue');
        }
      }
    } else if (level > 0) {
      assert.strictEqual(index, solver.trailLim[level - 1], 'decision/assumption starts its level');
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepStrictEqual(prefix, solver.assigns);
}

export function assertRoot(solver: Solver): void {
  assert.deepStrictEqual(solver.trailLim, [], 'every completed incremental call returns to root');
  assert.ok(solver.qhead >= 0 && solver.qhead <= solver.trail.length);
  for (let variable = 0; variable < solver.assigns.length; variable += 1) {
    assert.strictEqual(solver.level[variable], 0);
    if (solver.assigns[variable] === Value.UNSET) assert.strictEqual(solver.reason[variable], null);
  }
  assertHeap(solver);
  assertReasons(solver);
  solver.checkInvariants();
  assert.strictEqual(
    solver.stats.learnedClausesCurrent,
    solver.clauses.filter((clause) => clause.learned).length,
    'the lifetime ledger counts the ACTUAL live database',
  );
}

function assertFixpoint(solver: Solver): void {
  assert.strictEqual(solver.qhead, solver.trail.length);
  assert.strictEqual(internals(solver).propagationCursor, null, 'no partially scanned event');
  for (const clause of solver.clauses) {
    const values = clause.lits.map((lit) => litValue(lit, solver.assigns));
    assert.ok(
      values.includes(Value.TRUE) || values.filter((value) => value === Value.UNSET).length >= 2,
      'propagate before advancing assumptions, deciding, or returning a model',
    );
  }
}

// Independent exhaustive CNF evaluator, including ALL auxiliaries. The
// original clauses are copied before search; no assumptions/learned premises.
export function cnfTruthTable(base: CompiledCnf): Int8Array[] {
  assert.ok(base.numVars <= 12, 'bounded independent truth table');
  const clauses = base.clauses.map((clause) => [...clause.lits]);
  const models: Int8Array[] = [];
  for (let mask = 0; mask < 2 ** base.numVars; mask += 1) {
    const values = Int8Array.from({ length: base.numVars }, (_, index) => (mask >> index) & 1);
    if (
      clauses.every((lits) =>
        lits.some((lit) => values[Math.floor(lit / 2)] === (lit % 2 === 0 ? 1 : 0)),
      )
    ) {
      models.push(values);
    }
  }
  return models;
}

export function assertEntailed(models: readonly Int8Array[], learned: Clause): void {
  assert.ok(models.length > 0, 'non-vacuous base-formula entailment');
  for (const model of models) {
    assert.ok(
      learned.lits.some((lit) => model[Math.floor(lit / 2)] === (lit % 2 === 0 ? 1 : 0)),
      "learned clause holds even in base models violating this call's assumptions",
    );
  }
}

// Every override delegates unchanged to the inherited production operation.
export class IncrementalAudit extends Solver {
  readonly enqueues: Array<{
    lit: number;
    reason: Clause | null;
    level: number;
    assumption: boolean;
    call: number;
  }> = [];
  readonly levels: Array<{
    level: number;
    boundary: number;
    pending: number | undefined;
    value: Value | undefined;
    call: number;
  }> = [];
  readonly analyses: Array<{
    from: number;
    backjumpLevel: number;
    lits: number[];
    levels: number[];
    lbd: number;
    // Literals recursive minimization removed from this clause before lbd.
    minimized: number;
    call: number;
  }> = [];
  readonly cancellations: Array<{
    kind: 'backjump' | 'restart' | 'cleanup';
    from: number;
    to: number;
    call: number;
  }> = [];
  readonly admissions: Clause[] = [];
  readonly reductions: Array<{ total: number; removed: Clause[]; live: number; call: number }> = [];
  readonly initialStats = { ...this.stats };
  conflictsObserved = 0;
  calls = 0;
  verifyLearned: ((clause: Clause) => void) | undefined;
  private active: readonly number[] = [];
  private searching = false;
  private backjumpPending = false;

  override solve(assumptions: readonly number[] = []): boolean {
    assertRoot(this);
    this.calls += 1;
    this.active = assumptions;
    this.searching = true;
    try {
      const sat = super.solve(assumptions);
      if (sat) {
        assertFixpoint(this);
        for (const lit of assumptions) assert.strictEqual(litValue(lit, this.assigns), Value.TRUE);
      }
      return sat;
    } finally {
      this.searching = false;
      this.active = [];
    }
  }

  override newDecisionLevel(): void {
    assertFixpoint(this);
    const pending = this.active[this.trailLim.length];
    this.levels.push({
      level: this.trailLim.length + 1,
      boundary: this.trail.length,
      pending,
      value: pending === undefined ? undefined : litValue(pending, this.assigns),
      call: this.calls,
    });
    super.newDecisionLevel();
  }

  override enqueue(lit: number, reason: Clause | null): boolean {
    const unset = this.assigns[varOf(lit)] === Value.UNSET;
    const level = this.trailLim.length;
    if (unset && reason !== null) {
      assert.ok(this.clauses.includes(reason));
      for (const other of reason.lits) {
        if (other !== lit) assert.strictEqual(litValue(other, this.assigns), Value.FALSE);
      }
    }
    const assumption = reason === null && level > 0 && level <= (this.active?.length ?? 0);
    if (assumption) assert.strictEqual(lit, this.active[level - 1]);
    const result = super.enqueue(lit, reason);
    if (result && unset) {
      // Root construction precedes subclass fields and is measured separately.
      this.enqueues?.push({ lit, reason, level, assumption, call: this.calls });
    }
    return result;
  }

  override propagate(): Clause | null {
    const conflict = super.propagate();
    if (conflict !== null) {
      this.conflictsObserved += 1;
      assert.ok(conflict.lits.every((lit) => litValue(lit, this.assigns) === Value.FALSE));
    } else {
      assertFixpoint(this);
    }
    assertReasons(this);
    return conflict;
  }

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    const producedBefore = this.stats.learnedLiterals;
    const minimizedBefore = this.stats.minimizedLiterals;
    const result = super.analyze(conflict);
    const levels = result.learned.lits.map((lit) => this.level[varOf(lit)]);
    assert.strictEqual(
      result.learned.lbd,
      new Set(levels.filter((level) => level !== 0)).size,
      'learning-time distinct nonzero levels of the minimized clause',
    );
    const produced = this.stats.learnedLiterals - producedBefore;
    const minimized = this.stats.minimizedLiterals - minimizedBefore;
    assert.strictEqual(
      produced,
      result.learned.lits.length,
      'learnedLiterals counts post-minimization literals per analysis',
    );
    assert.ok(
      minimized >= 0 && produced >= 1,
      'minimization only removes; the asserting literal always survives',
    );
    this.verifyLearned?.(result.learned);
    this.analyses.push({
      from: this.trailLim.length,
      backjumpLevel: result.backjumpLevel,
      lits: [...result.learned.lits],
      levels,
      lbd: result.learned.lbd,
      minimized,
      call: this.calls,
    });
    this.backjumpPending = true;
    return result;
  }

  override addLearnedClause(clause: Clause): Clause {
    const before = new Set(this.clauses);
    const total = this.stats.learnedClauses;
    const registered = super.addLearnedClause(clause);
    const admitted = !before.has(registered);
    if (admitted) this.admissions.push(registered);
    assert.strictEqual(this.stats.learnedClauses, total + Number(admitted));
    this.checkInvariants();
    return registered;
  }

  override cancelUntil(target: number): void {
    const kind = this.searching ? (this.backjumpPending ? 'backjump' : 'restart') : 'cleanup';
    this.backjumpPending = false;
    const from = this.trailLim.length;
    const before = [...this.clauses];
    const metadata = before.map((clause) => ({ ...clause, lits: [...clause.lits] }));
    // Entry-era snapshot: entry identity + blocker per position (a raw
    // deep-equal over shared entry references would degenerate).
    const watches = snapshotWatches(this.watches, this.binaryWatches);
    const activity = this.activity.slice();
    const phases = this.polarity.slice();
    const increment = internals(this).varInc;
    const root = this.trail.filter((lit) => this.level[varOf(lit)] === 0);
    const reasons = root.map((lit) => this.reason[varOf(lit)]);
    const qhead = this.qhead;
    const pendingEvent = internals(this).propagationCursor?.event ?? qhead;
    super.cancelUntil(target);
    assert.strictEqual(this.clauses.length, before.length);
    for (const [index, clause] of before.entries()) {
      assert.strictEqual(this.clauses[index], clause, 'retain canonical identity');
      assert.deepStrictEqual(clause, metadata[index]);
    }
    assertWatchListsSurvive(
      this.watches,
      this.binaryWatches,
      watches,
      'cancellation does not rebuild watches',
    );
    assert.deepStrictEqual(this.activity, activity);
    assert.deepStrictEqual(this.polarity, phases);
    assert.strictEqual(internals(this).varInc, increment);
    assert.deepStrictEqual(this.trail.slice(0, root.length), root);
    for (const [index, lit] of root.entries())
      assert.strictEqual(this.reason[varOf(lit)], reasons[index]);
    assert.strictEqual(this.qhead, Math.min(qhead, pendingEvent, this.trail.length));
    assert.strictEqual(internals(this).propagationCursor, null, 'partial scans requeued or undone');
    assertHeap(this);
    assertReasons(this);
    this.checkInvariants();
    this.cancellations.push({ kind, from, to: this.trailLim.length, call: this.calls });
  }

  override reduceLearnedClauses(): void {
    const before = [...this.clauses];
    const metadata = before.map((clause) => ({ ...clause, lits: [...clause.lits] }));
    const reasons = [...this.reason];
    const total = this.stats.learnedClauses;
    const live = before.filter((clause) => clause.learned).length;
    super.reduceLearnedClauses();
    const retained = new Set(this.clauses);
    const removed = before.filter((clause) => !retained.has(clause));
    assert.ok(removed.length <= Math.floor(live / 2));
    for (const [index, clause] of before.entries()) {
      assert.deepStrictEqual(clause, metadata[index], 'no rewriting during deletion');
      if (!clause.learned || clause.lbd <= 2 || reasons.includes(clause)) {
        assert.ok(retained.has(clause), 'permanent/glue/reason protection across calls');
      }
    }
    for (const [index, reason] of reasons.entries()) assert.strictEqual(this.reason[index], reason);
    assert.strictEqual(this.stats.learnedClauses, total);
    assert.strictEqual(this.stats.learnedClausesCurrent, live - removed.length);
    assert.strictEqual(internals(this).learnedSinceReduction, 0);
    assertReasons(this);
    assertHeap(this);
    this.checkInvariants();
    this.reductions.push({ total, removed, live: live - removed.length, call: this.calls });
  }

  assertCounters(): void {
    assert.deepStrictEqual(this.stats, {
      decisions:
        this.initialStats.decisions +
        this.enqueues.filter((e) => e.reason === null && !e.assumption).length,
      propagations:
        this.initialStats.propagations + this.enqueues.filter((e) => e.reason !== null).length,
      conflicts: this.initialStats.conflicts + this.conflictsObserved,
      restarts:
        this.initialStats.restarts +
        this.cancellations.filter((e) => e.kind === 'restart' && e.from > 0).length,
      learnedClauses: this.initialStats.learnedClauses + this.admissions.length,
      learnedClausesCurrent: this.clauses.filter((clause) => clause.learned).length,
      learnedLiterals:
        this.initialStats.learnedLiterals +
        this.analyses.reduce((sum, analysis) => sum + analysis.lits.length, 0),
      minimizedLiterals:
        this.initialStats.minimizedLiterals +
        this.analyses.reduce((sum, analysis) => sum + analysis.minimized, 0),
    });
    assert.strictEqual(
      this.stats.learnedClausesCurrent,
      this.admissions.length -
        this.reductions.reduce((sum, round) => sum + round.removed.length, 0),
    );
  }
}
