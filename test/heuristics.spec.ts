import assert from 'node:assert';
import { describe, it } from 'node:test';
import { compile, isNeg, litValue, negLit, posLit, varOf } from '../src/compile.js';
import type { Clause, CompiledCnf } from '../src/compile.js';
import { and, getAllSolutions, getSolution, implies, not, or, Value, xor } from '../src/index.js';
import { Solver } from '../src/solver.js';
import type { SolverStats, VariablePriority } from '../src/solver.js';
import {
  assertModelShape,
  cnfToExpr,
  expressionValue,
  mulberry32,
  random3Cnf,
  randomFormula,
  referenceModels,
} from './helpers';

function cnf(names: string[], clauses: number[][], numVars = names.length): CompiledCnf {
  assert.deepEqual(names, [...names].sort());
  return {
    numVars,
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

// White-box observations, not a new public API or a state injection seam.
// Tests NEVER set assignments, phases, scores, the increment, or heap entries.
// Two tests wrap a private method only to observe each real operation.
interface VsidsInternals {
  readonly decisionHeap: readonly number[];
  readonly heapPosition: Int32Array;
  readonly unassignedNamed: number;
  // Named-variable membership per global variable index: the heap is indexed
  // globally, so the flag — not an index bound — decides heap eligibility.
  readonly named: Uint8Array;
  readonly varInc: number;
  bumpVariableActivity(variable: number): void;
  decisionPrecedes(left: number, right: number): boolean;
}

const internals = (solver: Solver): VsidsInternals => solver as unknown as VsidsInternals;

function assertHeap(solver: Solver): void {
  const { decisionHeap: heap, heapPosition: positions, unassignedNamed, named } = internals(solver);
  assert.strictEqual(new Set(heap).size, heap.length, 'no duplicate heap entries');
  for (let index = 0; index < heap.length; index += 1) {
    const variable = heap[index];
    assert.ok(variable >= 0 && variable < positions.length, 'heap entries within the array');
    assert.strictEqual(named[variable], 1, 'only named variables enter the heap');
    assert.strictEqual(positions[variable], index, 'position is the inverse of heap membership');
    if (index > 0) {
      const parent = heap[(index - 1) >> 1];
      assert.ok(
        solver.activity[parent] > solver.activity[variable] ||
          (solver.activity[parent] === solver.activity[variable] && parent < variable),
        'heap ordering includes deterministic lower-index ties',
      );
    }
  }
  let unset = 0;
  for (let variable = 0; variable < positions.length; variable += 1) {
    if (named[variable] !== 1) {
      assert.strictEqual(positions[variable], -1, 'auxiliaries never enter the heap');
      continue;
    }
    if (positions[variable] >= 0) {
      assert.strictEqual(heap[positions[variable]], variable);
    }
    if (solver.assigns[variable] === Value.UNSET) {
      unset += 1;
      assert.ok(positions[variable] >= 0, 'every unassigned named variable is eligible');
    }
  }
  assert.strictEqual(unassignedNamed, unset, 'constant-time termination count stays exact');
}

function assertReasons(solver: Solver, conflict: Clause): void {
  const prefix = new Int8Array(solver.assigns.length).fill(Value.UNSET);
  for (const lit of solver.trail) {
    const variable = varOf(lit);
    assert.strictEqual(prefix[variable], Value.UNSET);
    const reason = solver.reason[variable];
    if (reason !== null) {
      assert.ok(solver.clauses.includes(reason));
      assert.ok(reason.lits.includes(lit));
      for (const other of reason.lits) {
        if (other !== lit) {
          assert.strictEqual(litValue(other, prefix), Value.FALSE, 'reason was genuinely unit');
        }
      }
    }
    prefix[variable] = isNeg(lit) ? Value.FALSE : Value.TRUE;
  }
  assert.deepEqual(prefix, solver.assigns);
  assert.ok(solver.clauses.includes(conflict));
  assert.ok(conflict.lits.every((lit) => litValue(lit, prefix) === Value.FALSE));
}

class ObservedSolver extends Solver {
  readonly decisions: number[] = [];

  override enqueue(lit: number, reason: Clause | null): boolean {
    const wasUnset = this.assigns[varOf(lit)] === Value.UNSET;
    const result = super.enqueue(lit, reason);
    assertHeap(this);
    if (result && wasUnset) {
      assert.strictEqual(this.polarity[varOf(lit)], this.assigns[varOf(lit)]);
      // Constructor units/assumptions precede subclass field initialization,
      // but are level zero, and must not be logged as search decisions.
      if (reason === null && this.trailLim.length > 0) {
        assert.strictEqual(internals(this).named[varOf(lit)], 1, 'decisions are named');
        this.decisions.push(lit);
      }
    }
    return result;
  }

  override analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    assertReasons(this, conflict);
    const result = super.analyze(conflict);
    assertHeap(this);
    return result;
  }

  override cancelUntil(level: number): void {
    super.cancelUntil(level);
    assertHeap(this);
  }
}

// Independent O(n log n) oracle in tests only. Unlike the implementation, it
// sorts the actual unassigned names afresh at every real decision enqueue.
class HeapOracleSolver extends ObservedSolver {
  override enqueue(lit: number, reason: Clause | null): boolean {
    if (reason === null && this.trailLim.length > 0) {
      const state = internals(this);
      const candidates = Array.from({ length: state.heapPosition.length }, (_, v) => v)
        .filter((v) => state.named[v] === 1 && this.assigns[v] === Value.UNSET)
        .sort((a, b) => this.activity[b] - this.activity[a] || a - b);
      assert.strictEqual(varOf(lit), candidates[0], 'real decision follows VSIDS, not index scan');
      assert.strictEqual(isNeg(lit) ? Value.FALSE : Value.TRUE, this.polarity[varOf(lit)]);
    }
    return super.enqueue(lit, reason);
  }
}

function decide(solver: Solver, lit: number): void {
  assert.strictEqual(solver.propagate(), null);
  assert.strictEqual(solver.qhead, solver.trail.length);
  assert.strictEqual(litValue(lit, solver.assigns), Value.UNSET);
  solver.newDecisionLevel();
  assert.strictEqual(solver.enqueue(lit, null), true);
}

// Complete bidirectional gates for (a∧b)∨(a∧¬b), NOT unconstrained variables
// relabelled as auxiliaries. This hand-built fixture intentionally fixes its
// gate layout; no exact compiler aux-count assumption is needed.
function gateClauses(a: number, b: number, u: number, v: number, w: number): number[][] {
  return [
    [negLit(u), posLit(a)],
    [negLit(u), posLit(b)],
    [posLit(u), negLit(a), negLit(b)],
    [negLit(v), posLit(a)],
    [negLit(v), negLit(b)],
    [posLit(v), negLit(a), posLit(b)],
    [posLit(w), negLit(u)],
    [posLit(w), negLit(v)],
    [negLit(w), posLit(u), posLit(v)],
    [posLit(w)],
  ];
}

const decisionWitness = () =>
  compile(and(or('a', not('a')), or('b', not('b')), or('x', 'y'), or('x', not('y'))));

describe('Solver VSIDS activity and rescaling', () => {
  it('starts all named and auxiliary activities at zero and phases at FALSE', () => {
    const base = compile(xor('a', 'b'));
    const solver = new Solver(base);
    assert.ok(solver.activity instanceof Float64Array);
    assert.ok(solver.polarity instanceof Int8Array);
    assert.strictEqual(solver.activity.length, base.numVars);
    assert.strictEqual(solver.polarity.length, base.numVars);
    assert.ok(solver.activity.every((score) => score === 0));
    // Constructor units have already saved their assigned phase; all other
    // named/aux variables still have the initial FALSE preference.
    for (let v = 0; v < base.numVars; v += 1) {
      const expected = solver.assigns[v] === Value.UNSET ? Value.FALSE : solver.assigns[v];
      assert.strictEqual(solver.polarity[v], expected);
    }
    assert.strictEqual(internals(solver).varInc, 1);
    assertHeap(solver);
  });

  it('uses the increased increment on the next real search conflict, not on the first', () => {
    const solver = new HeapOracleSolver(
      cnf(
        ['a', 'b', 'x', 'y'],
        [
          [posLit(0), posLit(1)],
          [posLit(0), negLit(1)],
          [posLit(2), posLit(3)],
          [posLit(2), negLit(3)],
        ],
      ),
    );
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(solver.stats.conflicts, 2);
    assert.deepEqual(Array.from(solver.activity), [1, 1, 1 / 0.95, 1 / 0.95]);
    assert.strictEqual(internals(solver).varInc, (1 / 0.95) * (1 / 0.95));
  });

  it('rescales inside each bump, including repeated rescaling and underflow ties', () => {
    const solver = new ObservedSolver(
      cnf(
        ['idleA', 'idleB', 'seedA', 'seedB', 'x', 'y'],
        [[posLit(2), posLit(3)], [posLit(2), negLit(3)], ...gateClauses(4, 5, 6, 7, 8)],
        9,
      ),
    );
    const state = internals(solver);
    const bump = state.bumpVariableActivity.bind(solver);
    let rescales = 0;
    let rescaledThisAnalysis = false;
    let laterBumpsInSameAnalysis = 0;
    let afterBumpIncrement = 1;
    let underflowTieNeedsRepair = false;
    state.bumpVariableActivity = (variable) => {
      const before = Array.from(solver.activity);
      const increment = state.varInc;
      const shouldRescale = before[variable] + increment > 1e100;
      const oldHeap = shouldRescale ? [...state.decisionHeap] : [];
      if (rescaledThisAnalysis) {
        laterBumpsInSameAnalysis += 1;
      }
      bump(variable); // observation only: same receiver, argument and real method
      const scale = shouldRescale ? 1e-100 : 1;
      for (let v = 0; v < before.length; v += 1) {
        // Exact operations, no absolute epsilon that could accept zero for a
        // tiny nonzero score. Check untouched variables and auxiliaries too.
        assert.strictEqual(
          solver.activity[v],
          (before[v] + (v === variable ? increment : 0)) * scale,
        );
        assert.ok(Number.isFinite(solver.activity[v]));
      }
      assert.strictEqual(state.varInc, increment * scale);
      afterBumpIncrement = state.varInc;
      if (shouldRescale) {
        rescales += 1;
        rescaledThisAnalysis = true;
        for (let index = 1; index < oldHeap.length; index += 1) {
          const parent = oldHeap[(index - 1) >> 1];
          const child = oldHeap[index];
          if (
            before[parent] > before[child] &&
            solver.activity[parent] === 0 &&
            solver.activity[child] === 0 &&
            parent > child
          ) {
            underflowTieNeedsRepair = true;
          }
        }
      }
      assertHeap(solver);
    };

    const exposeConflict = (variable: number): void => {
      decide(solver, negLit(variable));
      const conflict = solver.propagate();
      assert.ok(conflict !== null);
      rescaledThisAnalysis = false;
      solver.analyze(conflict);
      assert.strictEqual(state.varInc, afterBumpIncrement * (1 / 0.95), 'decay follows all bumps');
      solver.cancelUntil(0);
    };
    exposeConflict(2); // seed seedA/seedB at 1, then leave them untouched
    // Operation-level analysis stress, not a solve trace: repeatedly expose a
    // REAL conflict, analyze it, and undo the decision without installing the
    // learned result. Four natural rescales ultimately underflow those old
    // scores into ties with LOWER-index idle names. No fabricated activities,
    // increment, reasons, assignments or conflicts, and no timing assertion.
    for (let round = 1; round <= 20_000; round += 1) {
      exposeConflict(4);
      if (round === 5_000) {
        assert.strictEqual(rescales, 1);
        assert.strictEqual(solver.activity[2], 1e-100);
        assert.strictEqual(solver.activity[3], 1e-100);
      }
    }
    assert.strictEqual(solver.stats.conflicts, 20_001);
    assert.strictEqual(rescales, 4);
    assert.ok(laterBumpsInSameAnalysis > 0, 'remaining bumps use the scaled increment immediately');
    assert.strictEqual(solver.activity[2], 0, 'old score underflows after four rescales');
    assert.strictEqual(solver.activity[3], 0);
    assert.strictEqual(solver.activity[5], 0, 'unseen input y stays untouched');
    assert.strictEqual(solver.activity[4], solver.activity[6]);
    assert.strictEqual(solver.activity[4], solver.activity[7]);
    assert.strictEqual(solver.activity[4], solver.activity[8]);
    assert.ok(underflowTieNeedsRepair, 'new lower-index ties require real heap repair');
    assertHeap(solver);
  });

  it('decays a terminal root conflict once without inventing a bump or analysis', () => {
    const solver = new Solver(cnf(['a'], [[posLit(0)], [negLit(0)]]));
    assert.strictEqual(solver.solve(), false);
    assert.strictEqual(solver.stats.conflicts, 1);
    assert.strictEqual(internals(solver).varInc, 1 / 0.95);
    assert.strictEqual(solver.activity[0], 0);
    assert.strictEqual(solver.solve(), false);
    assert.strictEqual(internals(solver).varInc, 1 / 0.95);
  });
});

describe('Solver named-only decision heap', () => {
  it('reinserts actual heap decisions on a backjump, then chooses activity over index', () => {
    const solver = new HeapOracleSolver(decisionWitness());
    assert.strictEqual(solver.solve(), true);
    // a=F,b=F,x=F; y=F conflicts, learn x and backjump 3→0. VSIDS
    // selects y before the lower-index a,b, which must both be reinserted.
    assert.deepEqual(solver.decisions, [
      negLit(0),
      negLit(1),
      negLit(2),
      negLit(3),
      negLit(0),
      negLit(1),
    ]);
    assert.deepEqual(Array.from(solver.activity), [0, 0, 1, 1]);
    assert.deepEqual(solver.model(), {
      a: Value.FALSE,
      b: Value.FALSE,
      x: Value.TRUE,
      y: Value.FALSE,
    });
    assert.deepEqual(solver.stats, {
      decisions: 6,
      propagations: 2,
      conflicts: 1,
      restarts: 0,
      learnedClauses: 1,
      learnedClausesCurrent: 1,
      learnedLiterals: 1,
      minimizedLiterals: 0,
    });
    assertHeap(solver);
  });

  it('bumps real gate auxiliaries but never inserts or decides them, even after cancellation', () => {
    const solver = new HeapOracleSolver(cnf(['a', 'b'], gateClauses(0, 1, 2, 3, 4), 5));
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.decisions, [negLit(0), negLit(1)]);
    assert.strictEqual(solver.stats.conflicts, 1);
    assert.deepEqual(Array.from(solver.activity), [1, 0, 1, 1, 1]);
    // After asserting a=TRUE at root, u/v are unassigned with activity 1,
    // but b (activity 0) is the only eligible decision. Its gates then settle.
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.FALSE });
    assert.ok(
      solver.clauses.every((clause) =>
        clause.lits.some((lit) => litValue(lit, solver.assigns) === Value.TRUE),
      ),
    );
    solver.cancelUntil(0);
    assert.strictEqual(solver.assigns[2], Value.UNSET);
    assert.strictEqual(solver.assigns[3], Value.UNSET);
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.decisions, [negLit(0), negLit(1), negLit(1)]);
    assertHeap(solver);
  });

  it('pops a binary heap within a comparison budget and reuses it after complete cancellation', () => {
    const count = 256;
    const names = Array.from({ length: count }, (_, v) => `v${String(v).padStart(3, '0')}`);
    const solver = new HeapOracleSolver(cnf(names, []));
    const state = internals(solver);
    const precedes = state.decisionPrecedes.bind(solver);
    let comparisons = 0;
    state.decisionPrecedes = (left, right) => {
      comparisons += 1;
      return precedes(left, right);
    };
    for (let run = 0; run < 2; run += 1) {
      comparisons = 0;
      solver.decisions.length = 0;
      assert.strictEqual(solver.solve(), true);
      assert.deepEqual(
        solver.decisions,
        names.map((_, v) => negLit(v)),
      );
      assert.ok(comparisons > 0 && comparisons <= 2 * count * Math.ceil(Math.log2(count)));
      solver.cancelUntil(0);
      solver.cancelUntil(0); // no-op cancellation must not duplicate entries or counts
      assert.strictEqual(state.decisionHeap.length, count);
      assertHeap(solver);
    }
  });

  it('matches an independent ranking oracle across seeded conflict/backtrack searches', () => {
    let conflicts = 0;
    for (let seed = 0; seed < 64; seed += 1) {
      const formula = cnfToExpr(random3Cnf(mulberry32(seed), 7, 30));
      const solver = new HeapOracleSolver(compile(formula));
      const models = referenceModels(formula);
      assert.strictEqual(solver.solve(), models.length > 0, `seed ${seed}`);
      if (models.length > 0) {
        assertModelShape(solver.model(), formula);
        assert.strictEqual(expressionValue(formula, solver.model()), Value.TRUE);
      }
      conflicts += solver.stats.conflicts;
      assertHeap(solver);
    }
    assert.ok(conflicts > 0, 'the heap oracle must cover learned-activity changes and backjumps');
  });
});

describe('Solver phase saving and priority hook', () => {
  it('saves root units, assumptions and PLE immediately, without corrupting phases on rejection', () => {
    const solver = new ObservedSolver(cnf(['a', 'b', 'c'], [[posLit(0)]]), {
      assumptions: { b: Value.TRUE },
    });
    assert.deepEqual(Array.from(solver.polarity), [Value.TRUE, Value.TRUE, Value.FALSE]);
    const trail = [...solver.trail];
    assert.strictEqual(solver.enqueue(posLit(0), solver.reason[0]), true);
    assert.strictEqual(solver.enqueue(negLit(0), null), false);
    assert.deepEqual(solver.trail, trail);
    assert.strictEqual(solver.polarity[0], Value.TRUE);
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.decisions, [negLit(2)]);

    const ple = new ObservedSolver(compile(or('a', 'b')), { enablePle: true });
    assert.strictEqual(ple.solve(), true);
    assert.deepEqual(Array.from(ple.polarity), [Value.TRUE, Value.TRUE]);
    assert.strictEqual(ple.stats.decisions, 0);
  });

  it('saves an implied TRUE at enqueue time and uses it on a later decision', () => {
    const solver = new ObservedSolver(compile(implies('b', 'a')));
    decide(solver, posLit(1));
    assert.strictEqual(solver.polarity[1], Value.TRUE);
    assert.strictEqual(solver.polarity[0], Value.FALSE);
    assert.strictEqual(solver.propagate(), null);
    assert.strictEqual(solver.polarity[0], Value.TRUE, 'before any cancellation');
    assert.strictEqual(solver.reason[0], solver.clauses[0]);
    solver.cancelUntil(0);
    assert.deepEqual(Array.from(solver.assigns), [Value.UNSET, Value.UNSET]);
    assert.deepEqual(Array.from(solver.polarity), [Value.TRUE, Value.TRUE]);
    solver.decisions.length = 0;
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(solver.decisions, [posLit(0), posLit(1)]);
    assert.deepEqual(solver.model(), { a: Value.TRUE, b: Value.TRUE });
  });

  for (const preferTrue of [false, true]) {
    it(`overrides the saved phase with ${preferTrue} for one decision, not a permanent preference`, () => {
      let calls = 0;
      const solver = new ObservedSolver(compile(or('a', not('a'))), {
        variablePriority: () => (++calls === 1 ? ['a', preferTrue] : null),
      });
      const opposite = preferTrue ? negLit(0) : posLit(0);
      decide(solver, opposite);
      solver.cancelUntil(0);
      assert.strictEqual(calls, 0, 'manual operations/propagation do not call the hook');
      assert.strictEqual(solver.solve(), true);
      assert.strictEqual(solver.polarity[0], preferTrue ? Value.TRUE : Value.FALSE);
      solver.cancelUntil(0);
      // A subsequent, valid assignment changes the saved phase again. The
      // original hook choice must not remain as a sticky polarity override.
      decide(solver, opposite);
      assert.strictEqual(solver.polarity[0], preferTrue ? Value.FALSE : Value.TRUE);
      solver.cancelUntil(0);
      assert.strictEqual(solver.solve(), true);
      assert.strictEqual(solver.model().a, preferTrue ? Value.FALSE : Value.TRUE);
      assert.strictEqual(calls, 2);
    });
  }

  const invalidReplies: Array<[string, unknown]> = [
    ['null', null],
    ['unknown name', ['missing', true]],
    ['already assigned name', ['x', false]],
    ['invalid polarity', ['y', 1]],
    ['malformed tuple', {}],
    ['undefined', undefined],
  ];
  for (const [label, reply] of invalidReplies) {
    it(`defers to real VSIDS for ${label}, not a first-unassigned fallback`, () => {
      let calls = 0;
      const solver: ObservedSolver = new ObservedSolver(decisionWitness(), {
        // Deliberately exercise defensive JS-hook validation outside the TS
        // return type too; this changes no solver state or valid-hook contract.
        variablePriority: (() => {
          calls += 1;
          return solver.stats.conflicts === 0 ? null : reply;
        }) as VariablePriority,
      });
      assert.strictEqual(solver.solve(), true);
      assert.deepEqual(solver.decisions, [
        negLit(0),
        negLit(1),
        negLit(2),
        negLit(3),
        negLit(0),
        negLit(1),
      ]);
      assert.strictEqual(calls, solver.stats.decisions);
      assert.strictEqual(solver.stats.conflicts, 1);
    });
  }

  it('honors a valid hook ahead of VSIDS without losing the displaced heap candidate', () => {
    let overridden = false;
    const solver: ObservedSolver = new ObservedSolver(decisionWitness(), {
      variablePriority: () => {
        if (solver.stats.conflicts > 0 && !overridden) {
          overridden = true;
          return ['a', true];
        }
        return null;
      },
    });
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(overridden, true);
    assert.deepEqual(solver.decisions, [
      negLit(0),
      negLit(1),
      negLit(2),
      posLit(0),
      negLit(3),
      negLit(1),
    ]);
    assert.strictEqual(solver.model().a, Value.TRUE);
    assert.strictEqual(solver.stats.decisions, 6);
  });

  it('calls the hook only at genuine decision fixpoints on a PLE-inert xor family', () => {
    const formula = and(xor('a', 'b'), xor('c', 'd'), xor('e', 'f'));
    const candidates: string[][] = [];
    const solver: ObservedSolver = new ObservedSolver(compile(formula), {
      enablePle: true,
      variablePriority: (unassigned, assignments) => {
        assert.strictEqual(solver.qhead, solver.trail.length);
        assert.strictEqual(candidates.length, solver.stats.decisions);
        for (const clause of solver.clauses) {
          assert.ok(
            clause.lits.some((lit) => litValue(lit, solver.assigns) === Value.TRUE) ||
              clause.lits.filter((lit) => litValue(lit, solver.assigns) === Value.UNSET).length >=
                2,
            'no pending unit or conflict at a hook call',
          );
        }
        const expectedAssigned = ['a', 'b', 'c', 'd', 'e', 'f'].filter(
          (v) => !unassigned.includes(v),
        );
        assert.deepEqual(Object.keys(assignments), expectedAssigned, 'no aux or UNSET assignments');
        candidates.push([...unassigned]);
        return [unassigned[0], true];
      },
    });
    assert.strictEqual(solver.solve(), true);
    assert.deepEqual(candidates, [
      ['a', 'b', 'c', 'd', 'e', 'f'],
      ['c', 'd', 'e', 'f'],
      ['e', 'f'],
    ]);
    assert.strictEqual(solver.stats.decisions, 3);
    assert.strictEqual(expressionValue(formula, solver.model()), Value.TRUE);
    assert.deepEqual(getSolution(xor('a', 'b')), {
      status: 'sat',
      model: { a: Value.FALSE, b: Value.TRUE },
    });
  });

  it('passes a complete named partial record to the hook even for Object.prototype keys', () => {
    let calls = 0;
    const solver = new ObservedSolver(
      cnf(['__proto__', 'a', 'constructor'], [[posLit(0)], [negLit(2)]]),
      {
        variablePriority: (unassigned, assignments) => {
          calls += 1;
          assert.deepEqual(unassigned, ['a']);
          assert.deepStrictEqual(
            assignments,
            Object.fromEntries([
              ['__proto__', Value.TRUE],
              ['constructor', Value.FALSE],
            ]),
          );
          return ['a', true];
        },
      },
    );
    assert.strictEqual(solver.solve(), true);
    assert.strictEqual(calls, 1);
    assert.strictEqual(solver.model().__proto__, Value.TRUE);
  });
});

describe('Solver fixed-seed reproducibility', () => {
  it('returns byte-identical stats for repeated fresh solves and enumerations, including learning', () => {
    let learned = 0;
    for (let seed = 0; seed < 32; seed += 1) {
      const formulas = [
        cnfToExpr(random3Cnf(mulberry32(seed), 6, 24)),
        randomFormula(mulberry32(seed), { maxVariables: 6, maxDepth: 3, maxWidth: 3 }).expr,
      ];
      for (const formula of formulas) {
        let expected: string | undefined;
        for (let run = 0; run < 3; run += 1) {
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
          const result = getSolution(formula, { stats });
          const singleStats = { ...stats };
          learned += stats.learnedClauses;
          const enumeration = getAllSolutions(formula, { stats });
          assert.strictEqual(enumeration.status, 'complete');
          const models = enumeration.models;
          assert.strictEqual(models.length, referenceModels(formula).length);
          if (result.status === 'sat') {
            assertModelShape(result.model, formula);
            assert.strictEqual(expressionValue(formula, result.model), Value.TRUE);
          }
          const actual = JSON.stringify({ result, models, singleStats, enumerationStats: stats });
          expected ??= actual;
          assert.strictEqual(actual, expected, `seed ${seed}, run ${run}`);
        }
      }
    }
    assert.ok(learned > 0, 'stats determinism must include actual learned activity, not only PLE');
  });
});
