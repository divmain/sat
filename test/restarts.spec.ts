import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, isNeg, litValue, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, implies, not, or, Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats, VariablePriority } from '../src/solver.js';
import {
  assertModelShape,
  cnfToExpr,
  expressionValue,
  mulberry32,
  phpCnf,
  random3Cnf,
  randomFormula,
  referenceModels,
} from './helpers';
import { PHP_REGRESSIONS } from './php-regressions';

interface HeapState {
  readonly decisionHeap: readonly number[];
  readonly heapPosition: Int32Array;
  readonly unassignedNamed: number;
  readonly varInc: number;
}

// Observation only: no assignments, counters, phases, scores or heap entries
// are injected. The independent heap oracle sorts actual unassigned variables.
const heapState = (solver: Solver): HeapState => solver as unknown as HeapState;

function assertHeap(solver: Solver): void {
  const { decisionHeap: heap, heapPosition: positions, unassignedNamed } = heapState(solver);
  assert.strictEqual(new Set(heap).size, heap.length);
  for (let index = 0; index < heap.length; index += 1) {
    const variable = heap[index];
    assert.ok(variable >= 0 && variable < positions.length, 'only named heap entries');
    assert.strictEqual(positions[variable], index);
    if (index > 0) {
      const parent = heap[Math.floor((index - 1) / 2)];
      assert.ok(
        solver.activity[parent] > solver.activity[variable] ||
          (solver.activity[parent] === solver.activity[variable] && parent < variable),
        'activity ordering with lower-index ties survives cancellation',
      );
    }
  }
  let unset = 0;
  for (let variable = 0; variable < positions.length; variable += 1) {
    if (positions[variable] !== -1) {
      assert.strictEqual(heap[positions[variable]], variable);
    }
    if (solver.assigns[variable] === Value.UNSET) {
      unset += 1;
      assert.ok(positions[variable] >= 0, 'no unassigned candidate lost from the heap');
    }
  }
  assert.strictEqual(unassignedNamed, unset);
}

function assertReasons(solver: Solver): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (let index = 0; index < solver.trail.length; index += 1) {
    const lit = solver.trail[index];
    const variable = varOf(lit);
    const level = solver.trailLim.filter((boundary) => boundary <= index).length;
    assert.strictEqual(prefix[variable], Value.UNSET, 'one trail entry per assigned variable');
    assert.strictEqual(solver.level[variable], level);
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.ok(solver.clauses.includes(reason), 'canonical reason identity');
      assert.ok(reason.lits.includes(lit));
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(litValue(other, prefix), Value.FALSE, 'unit reason at enqueue time');
        }
      }
    } else if (level > 0) {
      assert.strictEqual(index, solver.trailLim[level - 1], 'one decision per level');
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepStrictEqual(prefix, solver.assigns);
}

function assertWatches(solver: Solver): void {
  const memberships = new Map(solver.clauses.map((clause) => [clause, [] as number[]]));
  const keys = solver.clauses.map((clause) => [...clause.lits].sort((a, b) => a - b).join(','));
  assert.strictEqual(new Set(keys).size, keys.length, 'no duplicate canonical clauses');
  for (let lit = 0; lit < solver.watches.length; lit += 1) {
    const list = solver.watches[lit];
    assert.strictEqual(new Set(list).size, list.length, 'no duplicate watch references');
    for (const clause of list) {
      const actual = memberships.get(clause);
      assert.ok(actual !== undefined, 'every watch refers to a registered clause');
      actual.push(lit);
    }
  }
  for (const [clause, actual] of memberships) {
    const expected = clause.lits.length < 2 ? [] : clause.lits.slice(0, 2).sort((a, b) => a - b);
    assert.deepStrictEqual(actual, expected, 'exact watch membership, including unwatched units');
  }
}

function assertFixpoint(solver: Solver): void {
  assert.strictEqual(solver.qhead, solver.trail.length);
  for (const clause of solver.clauses) {
    const values = clause.lits.map((lit) => litValue(lit, solver.assigns));
    assert.ok(
      values.includes(Value.TRUE) || values.filter((value) => value === Value.UNSET).length >= 2,
      'no overlooked unit/conflict before a decision or SAT result',
    );
  }
}

interface Cancellation {
  kind: 'backjump' | 'restart';
  conflict: number;
  from: number;
  to: number;
  before: number[];
  retained: number[];
  qheadBefore: number;
  qheadAfter: number;
}

// Lightweight enough for default PHP(8,7). Distinguish the normal analysis
// backjump from the EXTRA restart cancellation without consulting restarts or
// the Luby implementation. Every override calls the real operation unchanged.
class RestartTraceSolver extends Solver {
  readonly cancellations: Cancellation[] = [];
  private backjumpPending = false;

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    const result = super.analyze(conflict);
    this.backjumpPending = true;
    return result;
  }

  override cancelUntil(level: number): void {
    const kind = this.backjumpPending ? 'backjump' : 'restart';
    this.backjumpPending = false;
    const from = this.trailLim.length;
    const before = [...this.trail];
    const qheadBefore = this.qhead;
    super.cancelUntil(level);
    if (kind === 'restart') {
      assert.strictEqual(level, 0);
    }
    this.cancellations.push({
      kind,
      conflict: this.stats.conflicts,
      from,
      to: this.trailLim.length,
      before,
      retained: [...this.trail],
      qheadBefore,
      qheadAfter: this.qhead,
    });
  }

  get boundaries(): Cancellation[] {
    return this.cancellations.filter((event) => event.kind === 'restart');
  }
}

type Event =
  | { kind: 'enqueue'; lit: number; reason: Clause | null; level: number }
  | { kind: 'propagate'; level: number; conflict: Clause | null }
  | { kind: 'register'; clause: Clause }
  | { kind: 'analyze' }
  | Cancellation;

// Small-fixture traces check the actual implication graph, watches and heap
// across every cancellation; none of these checks infer validity from stats.
class CheckedSolver extends RestartTraceSolver {
  readonly events: Event[] = [];
  readonly startupPropagations = this.trail.filter(
    (lit) => this.reason[varOf(lit)] !== null,
  ).length;

  override enqueue(lit: number, reason: Clause | null): boolean {
    const wasUnset = this.assigns[varOf(lit)] === Value.UNSET;
    if (wasUnset && reason === null && this.trailLim.length > 0) {
      const named = heapState(this).heapPosition.length;
      assert.ok(varOf(lit) < named, 'auxiliaries are never decisions');
      if (this.variablePriority === undefined) {
        const candidates = Array.from({ length: named }, (_, variable) => variable)
          .filter((variable) => this.assigns[variable] === Value.UNSET)
          .sort((a, b) => this.activity[b] - this.activity[a] || a - b);
        assert.strictEqual(varOf(lit), candidates[0], 'independent VSIDS ranking');
        assert.strictEqual(isNeg(lit) ? Value.FALSE : Value.TRUE, this.polarity[varOf(lit)]);
      }
    }
    const result = super.enqueue(lit, reason);
    assertHeap(this);
    if (wasUnset && result) {
      assert.strictEqual(this.polarity[varOf(lit)], this.assigns[varOf(lit)]);
      // Constructor enqueues precede field initialization; root assumptions
      // must not be mistaken for search propagations or decisions.
      this.events?.push({ kind: 'enqueue', lit, reason, level: this.trailLim.length });
    }
    return result;
  }

  override propagate(): Clause | null {
    const event: Event = { kind: 'propagate', level: this.trailLim.length, conflict: null };
    this.events.push(event);
    const result = super.propagate();
    event.conflict = result;
    assertReasons(this);
    if (result === null) {
      assertFixpoint(this);
    }
    return result;
  }

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    assert.ok(conflict.lits.every((lit) => litValue(lit, this.assigns) === Value.FALSE));
    const result = super.analyze(conflict);
    this.events.push({ kind: 'analyze' });
    assertHeap(this);
    return result;
  }

  override addLearnedClause(clause: Clause): Clause {
    const registered = super.addLearnedClause(clause);
    this.events.push({ kind: 'register', clause: registered });
    assertWatches(this);
    return registered;
  }

  override cancelUntil(level: number): void {
    const clauses = [...this.clauses];
    const contents = clauses.map((clause) => ({
      lits: [...clause.lits],
      activity: clause.activity,
    }));
    const watches = this.watches.map((list) => [...list]);
    const activity = this.activity.slice();
    const phases = this.polarity.slice();
    const increment = heapState(this).varInc;
    const root = this.trail.filter((lit) => this.level[varOf(lit)] === 0);
    const rootReasons = root.map((lit) => this.reason[varOf(lit)]);
    super.cancelUntil(level);
    assert.strictEqual(this.clauses.length, clauses.length);
    for (let index = 0; index < clauses.length; index += 1) {
      assert.strictEqual(this.clauses[index], clauses[index], 'canonical identity survives');
      assert.deepStrictEqual(this.clauses[index].lits, contents[index].lits);
      assert.strictEqual(this.clauses[index].activity, contents[index].activity);
    }
    assert.deepStrictEqual(this.watches, watches, 'cancellation does not rebuild watch lists');
    assert.deepStrictEqual(this.activity, activity, 'retain VSIDS scores');
    assert.deepStrictEqual(this.polarity, phases, 'retain EVERY saved assignment phase');
    assert.strictEqual(heapState(this).varInc, increment, 'no restart bump/decay/reset');
    assert.deepStrictEqual(
      this.trail.slice(0, root.length),
      root,
      'retain the dynamic root prefix',
    );
    for (let index = 0; index < root.length; index += 1) {
      const variable = varOf(root[index]);
      assert.strictEqual(this.reason[variable], rootReasons[index]);
      assert.strictEqual(this.level[variable], 0);
    }
    assertHeap(this);
    assertReasons(this);
    assertWatches(this);
    const event = this.cancellations[this.cancellations.length - 1];
    assert.strictEqual(event.qheadAfter, Math.min(event.qheadBefore, this.trail.length));
    if (event.kind === 'restart') {
      assert.deepStrictEqual(this.trail, root);
    }
    this.events.push(event);
  }

  override newDecisionLevel(): void {
    assertFixpoint(this);
    super.newDecisionLevel();
  }

  assertCounters(): void {
    const enqueues = this.events.filter(
      (event): event is Extract<Event, { kind: 'enqueue' }> => event.kind === 'enqueue',
    );
    assert.strictEqual(
      this.stats.decisions,
      enqueues.filter((event) => event.reason === null && event.level > 0).length,
    );
    assert.strictEqual(
      this.stats.propagations,
      this.startupPropagations +
        enqueues.filter((event) => event.reason !== null || event.level === 0).length,
      'count actual non-decision/assumption enqueues, even assertions immediately undone',
    );
    assert.strictEqual(
      this.stats.conflicts,
      this.events.filter((event) => event.kind === 'propagate' && event.conflict !== null).length,
    );
    assert.strictEqual(
      this.stats.restarts,
      this.boundaries.filter((event) => event.from > 0).length,
    );
    const live = this.clauses.filter((clause) => clause.learned).length;
    assert.strictEqual(this.stats.learnedClausesCurrent, live);
    assert.strictEqual(this.stats.learnedClauses, live, 'no reduction in this ticket');
  }
}

// G entails (¬x∨¬v): resolve t in its first two clauses. Deciding v=TRUE
// then x=TRUE exposes exactly that conflict, backjumping 2→1. The third clause
// prevents startup purity, but is satisfied by v=TRUE. Thus all x=FALSE and
// v=TRUE is an independently known model for any number of these gadgets.
function gadget(v = 'v', x = 'x', t = 't'): BooleanExpr {
  return and(or(not(x), t), or(not(x), not(t), not(v)), or(v, x, t));
}

function gadgets(count: number): BooleanExpr {
  return and(...Array.from({ length: count }, (_, index) => gadget('v', `x${index}`, `t${index}`)));
}

const gadgetPriority: VariablePriority = (unassigned) => {
  if (unassigned.includes('v')) {
    return ['v', true];
  }
  const x = unassigned.find((name) => name.startsWith('x'));
  return x === undefined ? null : [x, true];
};

function literal(base: CompiledCnf, name: string, value = Value.TRUE): number {
  const index = base.nameToIndex.get(name);
  assert.ok(index !== undefined);
  return index * 2 + (value === Value.FALSE ? 1 : 0);
}

function assertModel(
  solver: Solver,
  expr: BooleanExpr,
  assumptions: VariableAssignments = {},
): void {
  const model = solver.model();
  assertModelShape(model, expr);
  assert.strictEqual(expressionValue(expr, model), Value.TRUE);
  for (const [name, value] of Object.entries(assumptions)) {
    assert.ok(Object.hasOwn(model, name));
    if (value !== Value.UNSET) {
      assert.strictEqual(model[name], value, 'a restart must never lose a fixed assumption');
    }
  }
}

// Independent truth table over ALL base variables. Only plain-clause small
// fixtures use this; no premise comes from the solver's model or analysis.
function assertEntailed(base: CompiledCnf, learned: Clause): void {
  assert.ok(base.numVars <= 8);
  for (let mask = 0; mask < 2 ** base.numVars; mask += 1) {
    const satisfied = (clause: Clause) =>
      clause.lits.some((lit) => ((mask >> varOf(lit)) & 1) === (isNeg(lit) ? 0 : 1));
    if (base.clauses.every(satisfied)) {
      assert.ok(satisfied(learned), 'learning remains a consequence without root assumptions');
    }
  }
}

describe('Solver exact Luby restart budgets', () => {
  for (const base of [1, 2, 3]) {
    it(`uses exact Luby conflict intervals scaled by ${base}, not ordinary backjumps`, () => {
      const expr = gadgets(12 * base);
      const solver = new CheckedSolver(compile(expr), {
        restartBaseConflicts: base,
        enablePle: true,
        variablePriority: gadgetPriority,
        maxConflicts: 12 * base + 1,
      });
      assert.strictEqual(solver.solve(), true);
      // Literal, independently summed prefix: 1,1,2,1,1,2,4. Not luby().
      assert.deepStrictEqual(
        solver.boundaries.map((event) => event.conflict),
        [1, 2, 4, 5, 6, 8, 12].map((count) => count * base),
      );
      assert.ok(solver.boundaries.every((event) => event.from === 1 && event.to === 0));
      const jumps = solver.cancellations.filter((event) => event.kind === 'backjump');
      assert.strictEqual(jumps.length, 12 * base);
      assert.ok(jumps.every((event) => event.from === 2 && event.to === 1));
      assert.strictEqual(solver.stats.conflicts, 12 * base);
      assert.strictEqual(solver.stats.restarts, 7);
      assert.strictEqual(solver.stats.learnedClauses, 12 * base);
      assertModel(solver, expr);
      assert.strictEqual(solver.model().v, Value.TRUE);
      solver.assertCounters();
    });
  }

  it('does not restart early, or count an ordinary backjump as a restart', () => {
    const expr = gadget();
    const solver = new CheckedSolver(compile(expr), {
      restartBaseConflicts: 2,
      variablePriority: gadgetPriority,
    });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.conflicts, 1);
    assert.strictEqual(solver.stats.restarts, 0);
    assert.deepStrictEqual(solver.boundaries, []);
    assertModel(solver, expr);
    solver.assertCounters();
  });

  for (const maxConflicts of [1, 7]) {
    it(`keeps the hard cap ${maxConflicts} independent of restart epochs and throws before learning`, () => {
      const solver = new RestartTraceSolver(compile(gadgets(12)), {
        restartBaseConflicts: 1,
        variablePriority: gadgetPriority,
        maxConflicts,
      });
      assert.throws(
        () => solver.solve(),
        new RegExp(`maximum conflict budget exhausted \\(${maxConflicts}\\)`),
      );
      assert.strictEqual(solver.stats.conflicts, maxConflicts);
      assert.strictEqual(solver.stats.learnedClauses, maxConflicts - 1);
      assert.deepStrictEqual(
        solver.boundaries.map((event) => event.conflict),
        [1, 2, 4, 5, 6].filter((count) => count < maxConflicts),
      );
      assert.strictEqual(solver.stats.restarts, maxConflicts === 1 ? 0 : 5);
    });
  }

  it('keeps each fresh schedule independent of pre-populated/shared output counters', () => {
    const stats: SolverStats = {
      decisions: 999,
      propagations: 999,
      conflicts: 999,
      restarts: 999,
      learnedClauses: 999,
      learnedClausesCurrent: 999,
    };
    for (let run = 0; run < 2; run += 1) {
      const before = { ...stats };
      const solver = new RestartTraceSolver(compile(gadgets(12)), {
        stats,
        maxConflicts: 13,
        restartBaseConflicts: 1,
        variablePriority: gadgetPriority,
      });
      assert.strictEqual(solver.solve(), true);
      assert.deepStrictEqual(
        solver.boundaries.map((event) => event.conflict - before.conflicts),
        [1, 2, 4, 5, 6, 8, 12],
      );
      assert.strictEqual(stats.conflicts - before.conflicts, 12);
      assert.strictEqual(stats.restarts - before.restarts, 7);
      assert.strictEqual(stats.learnedClauses - before.learnedClauses, 12);
      assert.strictEqual(stats.learnedClausesCurrent - before.learnedClausesCurrent, 12);
    }
  });

  it('does not restart for decisions, conflict-free results, or terminal startup conflicts', () => {
    const free = and(
      ...Array.from({ length: 128 }, (_, index) => or(`v${index}`, not(`v${index}`))),
    );
    const solver = new CheckedSolver(compile(free), { restartBaseConflicts: 1, maxConflicts: 0 });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.decisions, 128);
    assert.strictEqual(solver.stats.restarts, 0);
    assertModel(solver, free);
    solver.assertCounters();
    const cases: Array<[BooleanExpr, boolean, VariableAssignments]> = [
      [and(), true, {}],
      [or(), false, {}],
      [and('a'), true, {}],
      [and('a', not('a')), false, {}],
      [and(or('a', 'b'), not('a'), not('b')), false, {}],
      [and('a'), false, { a: Value.FALSE }],
    ];
    for (const [expr, sat, assumptions] of cases) {
      const solver = new RestartTraceSolver(compile(expr), {
        restartBaseConflicts: 1,
        assumptions,
      });
      assert.strictEqual(solver.solve(), sat);
      assert.deepStrictEqual(solver.cancellations, []);
      assert.strictEqual(solver.stats.restarts, 0);
    }
  });
});

describe('Solver restart ordering and retained state', () => {
  it('restarts after the learned assertion but BEFORE its propagation can expose another conflict', () => {
    // Equivalent to a: a=FALSE leaves all four b/t clauses, which are UNSAT.
    // Default a=F,b=F first learns (a∨b), asserting b at level 1. Propagating
    // b BEFORE restart would already produce conflict #2, violating base=1.
    const expr = and(
      or('a', 'b', 't'),
      or('a', 'b', not('t')),
      or('a', not('b'), 't'),
      or('a', not('b'), not('t')),
    );
    const base = compile(expr);
    const solver = new CheckedSolver(base, { restartBaseConflicts: 1 });
    assert.strictEqual(solver.solve(), true);
    const first = solver.boundaries[0];
    assert.strictEqual(first.conflict, 1);
    assert.strictEqual(first.from, 1);
    assert.deepStrictEqual(first.before, [literal(base, 'a', Value.FALSE), literal(base, 'b')]);
    assert.deepStrictEqual(first.retained, []);
    assert.strictEqual(first.qheadBefore, 1, 'the new assertion was still pending');
    assert.strictEqual(first.qheadAfter, 0);
    const index = solver.events.findIndex((event) => event.kind === 'restart');
    assert.deepStrictEqual(
      solver.events.slice(index - 3, index + 2).map((event) => event.kind),
      ['register', 'backjump', 'enqueue', 'restart', 'propagate'],
    );
    const assertion = solver.events[index - 1];
    assert.strictEqual(assertion.kind, 'enqueue');
    if (assertion.kind !== 'enqueue') {
      throw new Error('expected a real asserting enqueue');
    }
    assert.strictEqual(assertion.lit, literal(base, 'b'));
    assert.strictEqual(assertion.level, 1);
    assert.ok(assertion.reason !== null);
    assertEntailed(base, assertion.reason);
    assert.ok(
      solver.events.filter((event) => event.kind === 'enqueue' && event.reason === assertion.reason)
        .length >= 2,
      'the retained learned clause actually propagates again after restart',
    );
    assert.ok(
      assertion.reason.activity > 0,
      'later analysis actually consumes the retained clause',
    );
    assert.strictEqual(solver.stats.conflicts, 2);
    assert.strictEqual(solver.stats.restarts, 1, 'the second epoch is an already-root no-op');
    assert.strictEqual(solver.model().b, Value.TRUE, 'saved TRUE assertion phase is reused');
    assertModel(solver, expr);
    assert.ok(referenceModels(expr).every((model) => model.a === Value.TRUE));
    solver.assertCounters();
  });

  it('consumes a root no-op epoch, propagates its unwatched learned unit, and retains it on a later restart', () => {
    const expr = and(or('y', 'z'), or('y', not('z')), or(not('y'), not('z')), gadgets(2));
    const base = compile(expr);
    const solver = new CheckedSolver(base, {
      restartBaseConflicts: 1,
      variablePriority: (unassigned, assignments) =>
        unassigned.includes('y') ? ['y', false] : gadgetPriority(unassigned, assignments),
    });
    assert.strictEqual(solver.solve(), true);
    assert.deepStrictEqual(
      solver.boundaries.map((event) => event.conflict),
      [1, 2],
    );
    assert.deepStrictEqual(
      solver.boundaries.map((event) => event.from),
      [0, 1],
    );
    assert.strictEqual(solver.stats.conflicts, 3, 'third epoch needs TWO conflicts, not one');
    assert.strictEqual(solver.stats.restarts, 1, 'ordinary root backjump is not an extra restart');
    const root = [literal(base, 'y'), literal(base, 'z', Value.FALSE)];
    const unitBoundary = solver.boundaries[0];
    assert.deepStrictEqual(unitBoundary.retained, [root[0]]);
    assert.strictEqual(unitBoundary.qheadAfter, 0, 'unwatched learned unit remains queued');
    assert.deepStrictEqual(solver.boundaries[1].retained, root);
    const learned = solver.reason[varOf(root[0])];
    assert.ok(learned?.learned);
    assert.deepStrictEqual(learned.lits, [root[0]]);
    assert.ok(solver.watches.every((list) => !list.includes(learned)));
    assert.strictEqual(solver.level[varOf(root[1])], 0, 'root implication also survives');
    for (const clause of solver.clauses.filter((clause) => clause.learned)) {
      assertEntailed(base, clause);
    }
    assertModel(solver, expr);
    solver.assertCounters();
  });

  it('preserves a pending NON-unit root assertion and its fixed assumption antecedent', () => {
    const expr = and(
      or(not('a'), not('x'), 't'),
      or(not('a'), not('x'), not('t')),
      or('x', not('z')),
      gadget('v', 'w', 'u'),
    );
    const base = compile(expr);
    const assumptions = { a: Value.TRUE };
    const solver = new CheckedSolver(base, {
      assumptions,
      restartBaseConflicts: 1,
      variablePriority: (unassigned) => {
        const name = ['x', 'v', 'w'].find((name) => unassigned.includes(name));
        return name === undefined ? null : [name, true];
      },
    });
    assert.strictEqual(solver.solve(), true);
    assert.deepStrictEqual(
      solver.boundaries.map((event) => event.conflict),
      [1, 2],
    );
    assert.deepStrictEqual(
      solver.boundaries.map((event) => event.from),
      [0, 1],
    );
    const x = varOf(literal(base, 'x'));
    const learned = solver.reason[x];
    assert.ok(learned?.learned);
    assert.deepStrictEqual(
      [...learned.lits].sort((a, b) => a - b),
      [literal(base, 'a', Value.FALSE), literal(base, 'x', Value.FALSE)],
    );
    assert.strictEqual(solver.level[x], 0);
    assert.strictEqual(solver.level[varOf(literal(base, 'z'))], 0);
    assert.strictEqual(solver.model().z, Value.FALSE, 'root assertion propagation was not skipped');
    assert.strictEqual(solver.boundaries[0].qheadAfter, 1);
    assert.strictEqual(solver.boundaries[0].retained.length, 2, 'root x was still pending');
    assertEntailed(base, learned);
    assertModel(solver, expr, assumptions);
    solver.assertCounters();
  });

  it('retains constructor units, assumptions, their implications, and scoped startup PLE pins', () => {
    const expr = and('r', implies('a', 'b'), or('p', 'q'), gadget());
    const base = compile(expr);
    const assumptions = { a: Value.TRUE, t: Value.UNSET };
    const solver = new CheckedSolver(base, {
      assumptions,
      enablePle: true,
      restartBaseConflicts: 1,
      variablePriority: gadgetPriority,
    });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.restarts, 1);
    assert.deepStrictEqual(
      solver.boundaries[0].retained,
      ['r', 'a', 'b', 'p', 'q'].map((name) => literal(base, name)),
    );
    for (const name of ['r', 'a', 'b', 'p', 'q']) {
      const variable = varOf(literal(base, name));
      assert.strictEqual(solver.level[variable], 0);
      assert.strictEqual(solver.assigns[variable], Value.TRUE);
    }
    const plePins = solver.events.filter(
      (event) => event.kind === 'enqueue' && event.reason === null && event.level === 0,
    );
    assert.strictEqual(
      plePins.length,
      2,
      'only p/q are PLE assignments, not assumptions/decisions',
    );
    assert.strictEqual(solver.model().a, Value.TRUE);
    assertModel(solver, expr, assumptions);
    assert.ok(referenceModels(expr).some((model) => model.a === Value.TRUE));
    solver.assertCounters();
  });

  it('retains real gate learning and bumped auxiliaries without ever deciding them', () => {
    // (¬v∨(x∧t)∨(x∧¬t)) is (¬v∨x), but Tseitin gates hide its implication
    // until v=TRUE,x=FALSE exposes a conflict. No fake auxiliary variables.
    const expr = and(or(not('v'), and('x', 't'), and('x', not('t'))), or('v', 'x', 't'));
    const base = compile(expr);
    assert.ok(base.numVars > base.numNamedVars);
    const solver = new CheckedSolver(base, {
      restartBaseConflicts: 1,
      variablePriority: (unassigned) => {
        if (unassigned.includes('v')) {
          return ['v', true];
        }
        return unassigned.includes('x') ? ['x', false] : null;
      },
    });
    assert.strictEqual(solver.solve(), true);
    assert.ok(solver.stats.restarts > 0);
    assert.ok(solver.activity.slice(base.numNamedVars).some((score) => score > 0));
    assertModel(solver, expr);
    assert.ok(referenceModels(expr).length > 0);
    solver.assertCounters();
  });
});

describe('Solver restart regression and reference gates', () => {
  it('proves default-budget PHP(8,7) UNSAT with genuine additional root cancellations', (t) => {
    const gate = PHP_REGRESSIONS.find(({ pigeons, holes }) => pigeons === 8 && holes === 7);
    assert.ok(gate !== undefined);
    assert.strictEqual(gate.maxConflicts, 36_270, 'do not recalibrate the historical hard cap');
    const solver = new RestartTraceSolver(compile(cnfToExpr(phpCnf(8, 7))), {
      enablePle: true,
      maxConflicts: gate.maxConflicts,
    });
    // Independent UNSAT witness: eight pigeons cannot occupy seven distinct holes.
    assert.strictEqual(solver.solve(), false);
    assert.ok(solver.stats.conflicts < gate.maxConflicts);
    assert.ok(solver.stats.learnedClauses > 0);
    assert.deepStrictEqual(
      solver.boundaries.slice(0, 7).map((event) => event.conflict),
      [100, 200, 400, 500, 600, 800, 1200],
    );
    const real = solver.boundaries.filter((event) => event.from > 0);
    assert.ok(real.length > 0, 'positivity must witness actual extra non-root cancellation');
    assert.ok(real.every((event) => event.before.length > event.retained.length && event.to === 0));
    assert.strictEqual(solver.stats.restarts, real.length);
    assert.strictEqual(
      solver.stats.learnedClausesCurrent,
      solver.clauses.filter((c) => c.learned).length,
    );
    assertReasons(solver);
    assertWatches(solver);
    assertHeap(solver);
    t.diagnostic(`Phase 3 task-10b8 PHP(8,7), base100: ${JSON.stringify(solver.stats)}`);
  });

  it('matches independent truth tables under base1, with both PLE modes and fixed assumptions', (t) => {
    let restarts = 0;
    let satCases = 0;
    let unsatCases = 0;
    let searches = 0;
    const names = ['__proto__', 'constructor', '', 'a=0,b', '0', 'toString', 'quote"\\\nλ'];
    for (let seed = 0; seed < 128; seed += 1) {
      const formulas = [
        cnfToExpr(random3Cnf(mulberry32(seed), 7, 30)),
        randomFormula(mulberry32(seed), { maxDepth: 3, maxWidth: 3, variables: names }).expr,
      ];
      for (const expr of formulas) {
        const reference = referenceModels(expr);
        const named = compile(expr).indexToName;
        const rng = mulberry32(10_000 + seed);
        const sample = Object.fromEntries(
          named
            .filter(() => rng.boolean())
            .map((name) => [name, rng.pick([Value.FALSE, Value.TRUE, Value.UNSET])]),
        );
        for (const assumptions of [{}, sample]) {
          const expected = reference.filter((model) =>
            Object.entries(assumptions).every(
              ([key, value]) => value === Value.UNSET || model[key] === value,
            ),
          );
          for (const enablePle of [false, true]) {
            let first: string | undefined;
            for (let run = 0; run < 2; run += 1) {
              const solver = new CheckedSolver(compile(expr), {
                assumptions,
                enablePle,
                restartBaseConflicts: 1,
                maxConflicts: 1000,
              });
              const sat = solver.solve();
              assert.strictEqual(
                sat,
                expected.length > 0,
                `seed ${seed}, PLE ${enablePle}, run ${run}`,
              );
              if (sat) {
                assertModel(solver, expr, assumptions);
                satCases += 1;
              } else {
                unsatCases += 1;
              }
              if (!enablePle) {
                assert.ok(
                  !solver.events.some(
                    (event) =>
                      event.kind === 'enqueue' && event.reason === null && event.level === 0,
                  ),
                  'no PLE pins introduced in disabled mode, including after restart',
                );
              }
              solver.assertCounters();
              assertWatches(solver);
              const actual = JSON.stringify({
                model: sat ? solver.model() : null,
                stats: solver.stats,
              });
              first ??= actual;
              assert.strictEqual(actual, first, 'fresh forced-restart searches are deterministic');
              restarts += solver.stats.restarts;
              searches += 1;
            }
          }
        }
      }
    }
    assert.strictEqual(searches, 2048);
    assert.ok(satCases > 0 && unsatCases > 0);
    assert.ok(restarts > 0, 'truth-table cross-validation must actually exercise restarts');
    t.diagnostic(
      `base1 reference gate: ${searches} searches, ${satCases} SAT, ${unsatCases} UNSAT, ${restarts} real restarts`,
    );
  });
});
