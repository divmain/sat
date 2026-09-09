// SatSolver.add() (Design § Incremental Clause Addition): failure-atomic
// staged compilation against the shared symbol table, named-flag growth with
// history-dependent batch indices, permanent-path clause admission with
// cached root conflicts, quiescence guards, and the mutation/abort
// regressions. The randomized add+solve equivalence battery lives in
// incremental-property.spec.ts.

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
  and,
  atLeast,
  atMost,
  createSolver,
  exactly,
  getSolution,
  implies,
  not,
  or,
  Value,
  xor,
} from '../src/index.js';
import type { BooleanExpr, SolveResult, VariableAssignments } from '../src/index.js';
import { compile, compileCount, varOf } from '../src/compile.js';
import { setYieldScheduler, Solver } from '../src/solver.js';
import { expressionValue, expectSatModel, referenceModels } from './helpers.js';
import { assertRoot, counters, IncrementalAudit, internals } from './incremental-helpers.js';

// A root unit plus 3×width long watch clauses to scan: startup propagation
// does real inspection-only work, so a small yieldQuantum pauses mid-scan.
const wideScan = (width: number): BooleanExpr =>
  and(
    'root',
    ...Array.from({ length: width }, (_, i) => `sat${i}`),
    ...Array.from({ length: width }, (_, i) =>
      and(
        or(not('root'), `sat${i}`),
        or(not('root'), `free${i}`, `t${i}`),
        or(not('root'), `free${i}`, not(`t${i}`)),
      ),
    ),
  );

const isNegated = (lit: number): boolean => lit % 2 === 1;

// Model-set validity oracle: the model must be one of the independently
// computed reference models of the (grown) conjunction.
function assertInReference(result: SolveResult, expr: BooleanExpr): void {
  const model = expectSatModel(result);
  const reference = referenceModels(expr);
  assert.ok(
    reference.some((candidate) =>
      Object.entries(model).every(([name, value]) => candidate[name] === value),
    ),
    'model is in the independently computed reference set',
  );
}

describe('incremental compilation and the shared symbol table', () => {
  it('assigns batch-sorted indices after all existing variables (auxes included) and ticks compileCount once per add', () => {
    // or(and('z','b'),'q') allocates aux gates: named 0..2 (b,q,z sorted),
    // auxiliaries from index 3.
    const base = compile(or(and('z', 'b'), 'q'));
    assert.ok(base.numVars > base.numNamedVars, 'fixture carries auxiliaries');
    const solver = new Solver(base);
    const compileBefore = compileCount.value;

    // New names a, m, y land sorted-within-batch AFTER the auxiliaries; the
    // plain-clause or('m','a') and the unit 'y' allocate no auxes.
    solver.add(and(or('m', 'a'), 'y'));
    assert.strictEqual(compileCount.value, compileBefore + 1, 'one real compilation per add');
    const state = internals(solver);
    for (const [name, expected] of [
      ['b', 0],
      ['q', 1],
      ['z', 2],
      ['a', base.numVars],
      ['m', base.numVars + 1],
      ['y', base.numVars + 2],
    ] as const) {
      assert.strictEqual(state.nameToIndex.get(name), expected, `history-dependent index: ${name}`);
      assert.strictEqual(state.named[expected], 1, `named flag: ${name}`);
      assert.strictEqual(state.indexToName[expected], name);
    }
    for (let aux = base.numNamedVars; aux < base.numVars; aux += 1) {
      assert.strictEqual(state.named[aux], 0, 'existing auxiliaries stay unnamed');
      assert.strictEqual(state.indexToName[aux], undefined, 'auxiliary slot stays a hole');
    }
    assert.strictEqual(solver.assigns.length, base.numVars + 3, 'no aux needed for this batch');
    // The batch's unit conjunct 'y' is root-admitted immediately (the
    // permanent path enqueues it at level 0); the other five named variables
    // stay unassigned, and y lingers lazily in the heap until popped.
    assert.strictEqual(
      solver.assigns[base.numVars + 2],
      Value.TRUE,
      'unit conjunct admitted at root',
    );
    assert.strictEqual(state.unassignedNamed, 5);
    assert.strictEqual(state.decisionHeap.length, 6, 'every named variable enters the heap');
    assert.deepStrictEqual(
      [...state.decisionHeap].sort((left, right) => left - right),
      [0, 1, 2, base.numVars, base.numVars + 1, base.numVars + 2],
      'the batch joins the heap behind the construction variables (activity 0, index ties)',
    );

    // A second batch with a gate continues aux allocation past the batch:
    // two new named variables, one and-gate aux, one root-or aux.
    solver.add(or(and('m2', 'a'), 'zz'));
    assert.strictEqual(state.nameToIndex.get('m2'), base.numVars + 3);
    assert.strictEqual(state.nameToIndex.get('zz'), base.numVars + 4);
    assert.strictEqual(solver.assigns.length, base.numVars + 3 + 2 + 2);
    assert.strictEqual(state.named[base.numVars + 5], 0, 'the new gate auxiliary is unnamed');
    assertRoot(solver);
  });

  it('reports the globally sorted named set from variables() regardless of insertion order', () => {
    const solver = createSolver(or('z'));
    solver.add(and('a'));
    solver.add(or('m', not('a')));
    assert.deepStrictEqual(solver.variables(), ['a', 'm', 'z']);
    // Hook inputs arrive in internal index order, which is history-dependent:
    // construction names (free=0, z=1) precede the appended batch (a=2, b=3).
    const seen: string[][] = [];
    const hooked = createSolver(or('z', 'free'), {
      variablePriority: (unassigned) => {
        seen.push([...unassigned]);
        return null;
      },
    });
    // A non-forcing batch: a and b stay unassigned until decision time.
    hooked.add(or('a', 'b'));
    expectSatModel(hooked.solve());
    assert.ok(seen.length > 0, 'the hook ran');
    const first = seen[0];
    assert.deepStrictEqual(first, ['free', 'z', 'a', 'b']);
  });
});

describe('cardinality additions', () => {
  it('appends batch-sorted named indices after existing auxiliaries, with counter auxes continuing past them', () => {
    // The base carries gate auxiliaries: named 0..2 (b,q,z sorted), auxes
    // from index 3.
    const base = compile(or(and('z', 'b'), 'q'));
    assert.ok(base.numVars > base.numNamedVars, 'fixture carries auxiliaries');
    const solver = new Solver(base);
    // atLeast(2, four new names) rewrites to a Sinz atMost(2, ¬…) counter:
    // the batch's sorted named indices follow ALL existing variables (auxes
    // included)...
    solver.add(atLeast(2, 'y2', 'w0', 'x1', 'z3'));
    const state = internals(solver);
    for (const [name, expected] of [
      ['w0', base.numVars],
      ['x1', base.numVars + 1],
      ['y2', base.numVars + 2],
      ['z3', base.numVars + 3],
    ] as const) {
      assert.strictEqual(state.nameToIndex.get(name), expected, `history-dependent index: ${name}`);
      assert.strictEqual(state.named[expected], 1, `named flag: ${name}`);
      assert.strictEqual(state.indexToName[expected], name);
    }
    // ...and the counter auxiliaries continue past the batch, unnamed.
    assert.ok(solver.assigns.length > base.numVars + 4, 'counter auxiliaries allocated');
    for (let aux = base.numVars + 4; aux < solver.assigns.length; aux += 1) {
      assert.strictEqual(state.named[aux], 0, 'counter auxiliary stays unnamed');
      assert.strictEqual(state.indexToName[aux], undefined, 'counter auxiliary slot is a hole');
    }
    assertRoot(solver);
  });

  it('adds cardinality constraints with new variables, equivalent to the single-shot conjunction', () => {
    const solver = createSolver(and('base'));
    solver.add(atMost(1, 'x', 'y', 'z'));
    solver.add(atLeast(2, 'x', 'y', 'z', 'w'));
    solver.add(exactly(1, 'p', 'q'));
    assert.deepStrictEqual(solver.variables(), ['base', 'p', 'q', 'w', 'x', 'y', 'z']);
    const whole = and(
      and('base'),
      atMost(1, 'x', 'y', 'z'),
      atLeast(2, 'x', 'y', 'z', 'w'),
      exactly(1, 'p', 'q'),
    );
    // The equivalence contract: verdicts and model-set validity agree with
    // single-shot solving of the conjunction (not identical first models).
    const probes: VariableAssignments[] = [
      {},
      { x: Value.TRUE, y: Value.TRUE }, // violates atMost(1, x, y, z)
      { w: Value.FALSE, x: Value.FALSE, y: Value.FALSE, z: Value.FALSE }, // atLeast(2, …)
      { p: Value.TRUE, q: Value.TRUE }, // violates exactly(1, p, q)
      { p: Value.FALSE, q: Value.FALSE }, // violates exactly(1, p, q)
    ];
    for (const partial of probes) {
      const incremental = solver.solve(partial);
      const singleShot = getSolution(whole, { assumptions: partial });
      assert.strictEqual(
        incremental.status,
        singleShot.status,
        `verdict under ${JSON.stringify(partial)}`,
      );
      if (incremental.status === 'sat') {
        assertInReference(incremental, whole);
        for (const [name, value] of Object.entries(partial)) {
          assert.strictEqual(incremental.model[name], value, `model extends ${name}`);
        }
      }
    }
    // A failed cardinality add stays failure-atomic; the handle is reusable.
    assert.throws(
      () => solver.add({ atMost: { k: -1, exprs: ['v'] } } as BooleanExpr),
      /invalid BooleanExpr/,
    );
    assertInReference(solver.solve(), whole);
    assert.deepStrictEqual(solver.variables(), ['base', 'p', 'q', 'w', 'x', 'y', 'z']);
  });

  it('strengthens to UNSAT through a cardinality batch and caches it', () => {
    const solver = createSolver(and('a', 'b'));
    // Both units are already true at root: the pairwise clause (¬a ∨ ¬b) is
    // a root falsification, recorded as the cached startup conflict.
    solver.add(atMost(1, 'a', 'b'));
    assert.deepStrictEqual(solver.solve(), { status: 'unsat', core: {} });
    assert.deepStrictEqual(solver.solve({ a: Value.TRUE }), { status: 'unsat', core: {} });
    // Adding to an UNSAT base keeps it UNSAT, and the new name still joins
    // the universe.
    solver.add(atLeast(1, 'c'));
    assert.deepStrictEqual(solver.solve(), { status: 'unsat', core: {} });
    assert.ok(solver.variables().includes('c'));
  });
});

describe('failure-atomic staged compilation', () => {
  const invalidExprs: Array<[string, unknown]> = [
    ['multiple operator keys', { and: ['a'], or: ['b'] }],
    ['no operator key', { foo: ['a'] }],
    ['empty node', {}],
    ['non-array and operands', { and: 'a' }],
    ['non-array or operands', { or: { or: ['a'] } }],
    ['array as a node', ['a', 'b']],
    ['null child', { and: ['a', null] }],
    ['numeric child', { and: ['a', 7] }],
    ['boolean node', true],
    ['undefined child', { or: [undefined] }],
    ['array under not', { not: ['a'] }],
    ['null node', null],
    ['atMost with a negative k', { atMost: { k: -1, exprs: ['a'] } }],
    ['atLeast with a fractional k', { atLeast: { k: 1.5, exprs: ['a'] } }],
    ['atMost with a non-numeric k', { atMost: { k: '1', exprs: ['a'] } }],
    ['atLeast with a scalar payload', { atLeast: 1 }],
    ['atMost with a null payload', { atMost: null }],
    ['atMost with non-array exprs', { atMost: { k: 1, exprs: 'a' } }],
    ['atLeast with k missing', { atLeast: { exprs: ['a'] } }],
  ];

  it('rejects every malformed hand-built AST before touching the handle', () => {
    for (const [label, bad] of invalidExprs) {
      const solver = createSolver(and(or('a', 'b'), xor('c', 'd')));
      const resultBefore = solver.solve();
      const varsBefore = solver.variables();
      assert.throws(
        () => solver.add(bad as BooleanExpr),
        /invalid BooleanExpr/,
        `rejects ${label}`,
      );
      assert.deepStrictEqual(solver.variables(), varsBefore, `${label}: universe unchanged`);
      assert.deepStrictEqual(solver.solve(), resultBefore, `${label}: behavior unchanged`);
      solver.add(and('after'));
      assert.ok(solver.variables().includes('after'), `${label}: a later valid add works`);
    }
  });

  it('rejects cyclic hand-built graphs instead of overflowing the compiler recursion', () => {
    const cyclic: { and: unknown[] } = { and: [] };
    cyclic.and.push(cyclic, 'a');
    const solver = createSolver(and('base'));
    assert.throws(() => solver.add(cyclic as BooleanExpr), /cyclic expression graph/);
    expectSatModel(solver.solve());
    // The same guard covers the fresh-compile entry point.
    assert.throws(() => compile(cyclic as BooleanExpr), /cyclic expression graph/);
  });

  it('runs the quiescence guard before expression validation, like solveAssuming guards before its validation', () => {
    const solver = createSolver(and('a', or('b', not('b'))), {
      variablePriority: () => {
        // A malformed expression during an in-flight call still reports the
        // in-flight state (guard first), never a compile error.
        assert.throws(() => solver.add({} as BooleanExpr), /quiescent/);
        return null;
      },
    });
    expectSatModel(solver.solve({ a: Value.TRUE }));
  });
});

describe('snapshot ownership and caller-AST mutation', () => {
  it('retains the compiled snapshot of the constructor expression when it is edited before a later add', () => {
    const expr = { and: [or('a', 'b')] } as { and: Array<BooleanExpr | string> };
    const solver = createSolver(expr);
    const before = expectSatModel(solver.solve({ a: Value.FALSE }));
    assert.strictEqual(before.b, Value.TRUE);
    before.a = Value.TRUE; // returned models are detached snapshots
    // Editing the caller object then re-adding reads the NEW contents: the
    // staged delta's caches are per-add, never cross-add identity caches.
    expr.and.push(and('c'));
    solver.add(expr);
    assert.strictEqual(solver.solve({ c: Value.FALSE }).status, 'unsat');
    assert.strictEqual(solver.solve({ a: Value.FALSE, b: Value.FALSE }).status, 'unsat');
    assertInReference(solver.solve(), and(or('a', 'b'), and('c')));
  });

  it('reads an edited re-added object anew without weakening its previous admission', () => {
    const solver = createSolver(and(or('p', 'q')));
    const edited = and(or('r1', 'r2'));
    solver.add(edited);
    assert.strictEqual(solver.solve({ r1: Value.FALSE, r2: Value.FALSE }).status, 'unsat');
    // Edit the SAME object: it now additionally forces s. The earlier
    // admission (r1∨r2) must survive, and the new read must observe s.
    (edited as { and: Array<BooleanExpr | string> }).and.push(and('s'));
    solver.add(edited);
    assert.strictEqual(solver.solve({ s: Value.FALSE }).status, 'unsat');
    assert.strictEqual(solver.solve({ r1: Value.FALSE, r2: Value.FALSE }).status, 'unsat');
    assert.strictEqual(solver.solve({ p: Value.FALSE, q: Value.FALSE }).status, 'unsat');
    assertInReference(solver.solve(), and(or('p', 'q'), or('r1', 'r2'), and('s')));
  });

  it('never lets a re-added edited subtree alias its previous canonical form', () => {
    // xor duplicates its operands; a cross-add identity cache would alias the
    // edited shared subtree to its old canonical form and lose the edit.
    const shared = or('x', 'y');
    const solver = createSolver(and(shared));
    solver.add(and(shared, 'u'));
    (shared as { or: Array<BooleanExpr | string> }).or.length = 0;
    (shared as { or: Array<BooleanExpr | string> }).or.push('v', 'w');
    solver.add(and(shared));
    assert.strictEqual(solver.solve({ v: Value.FALSE, w: Value.FALSE }).status, 'unsat');
    assert.strictEqual(solver.solve({ x: Value.FALSE, y: Value.FALSE }).status, 'unsat');
    assert.strictEqual(solver.solve({ u: Value.FALSE }).status, 'unsat');
  });
});

describe('permanent-path admission and root handling', () => {
  it('excludes add-time root-unit work from per-call stats while the lifetime ledger counts it', () => {
    const solver = new IncrementalAudit(compile(and('a')));
    assert.strictEqual(solver.stats.propagations, 1, 'constructor unit');
    solver.add(and('b'));
    assert.strictEqual(solver.stats.propagations, 2, 'add-time unit joins the lifetime ledger');
    solver.add(and(or('c', not('c')))); // tautology: no unit, no clause, but c joins the universe
    assert.strictEqual(solver.stats.propagations, 2);
    const stats = counters(999);
    assert.deepStrictEqual(solver.solveAssuming(undefined, stats), {
      status: 'sat',
      model: { a: Value.TRUE, b: Value.TRUE, c: Value.FALSE },
    });
    assert.deepStrictEqual(
      stats,
      { ...counters(), decisions: 1 },
      // The add-time units are outside the per-call measurement; c is a
      // don't-care and takes one ordinary decision at the default FALSE phase.
      "add work is excluded from per-call measurement; only the don't-care decision counts",
    );
    solver.assertCounters();
    assertRoot(solver);
  });

  it('enqueues add-time root facts with their clause as reason and base-derived mask zero', () => {
    const solver = new Solver(compile(or('a', 'b')));
    solver.add(and('a', implies('a', 'c')));
    const a = internals(solver).nameToIndex.get('a');
    const c = internals(solver).nameToIndex.get('c');
    assert.ok(a !== undefined && c !== undefined);
    assert.strictEqual(solver.assigns[a], Value.TRUE, 'unit admitted at root');
    assert.ok(solver.reason[a] !== null, 'root unit carries its clause as reason');
    assert.strictEqual(solver.rootBasis[a], 0, 'base-derived mask zero');
    // The binary (¬a∨c) is root-unit at admission: c is enqueued at add time
    // with the clause as reason, so the next call reports no propagations.
    assert.strictEqual(solver.assigns[c], Value.TRUE, 'root-unit clause implication at admission');
    assert.strictEqual(solver.rootBasis[c], 0);
    const stats = counters(999);
    assert.strictEqual(solver.solveAssuming(undefined, stats).status, 'sat');
    assert.strictEqual(stats.propagations, 0, 'root facts were enqueued at add time');
  });

  it('records a root falsification as the cached startup conflict and keeps permanentUnsat across later adds', () => {
    const solver = new IncrementalAudit(compile(and('a')));
    solver.add(and(not('a')));
    // No solve has reported the cached conflict yet; the first search
    // observes it exactly once and sets permanentUnsat.
    assert.deepStrictEqual(solver.solveAssuming(), { status: 'unsat', core: {} });
    assert.strictEqual(internals(solver).permanentUnsat, true);
    // Adding more constraints (and new names) to a UNSAT base keeps it UNSAT.
    solver.add(and(or('fresh', 'other'), and('fresh')));
    const lifetime = { ...solver.stats };
    assert.deepStrictEqual(solver.solveAssuming(), { status: 'unsat', core: {} });
    // Even assumptions over the newly valid names core on {}: the proof is
    // assumption-independent.
    assert.deepStrictEqual(solver.solveAssuming({ fresh: Value.TRUE }), {
      status: 'unsat',
      core: {},
    });
    assert.deepStrictEqual(solver.stats, lifetime, 'cached UNSAT does no new work');
    solver.assertCounters();
    assertRoot(solver);
  });

  it('keeps a constructor-level UNSAT through adds', () => {
    const solver = createSolver(or());
    solver.add(and('a'));
    solver.add(or());
    assert.deepStrictEqual(solver.solve(), { status: 'unsat', core: {} });
    assert.deepStrictEqual(solver.variables(), ['a']);
  });

  it('treats and() as a no-op batch and or() as an immediate root conflict', () => {
    const solver = createSolver(or('a', 'b'));
    solver.add(and());
    assert.deepStrictEqual(solver.variables(), ['a', 'b']);
    assert.strictEqual(solver.solve().status, 'sat');
    solver.add(or());
    assert.deepStrictEqual(solver.solve(), { status: 'unsat', core: {} });
  });

  it('keeps admitting batches after an unreported root conflict; the first solve reports it once', () => {
    const solver = new IncrementalAudit(compile(and('a')));
    solver.add(or());
    // The cached empty-clause conflict has not been reported yet; further
    // batches still stage, grow the universe, and admit their root units.
    solver.add(and(or('fresh', 'other'), and('fresh')));
    assert.deepStrictEqual(solver.variables(), ['a', 'fresh', 'other']);
    const stats = counters(999);
    assert.deepStrictEqual(solver.solveAssuming(undefined, stats), {
      status: 'unsat',
      core: {},
    });
    assert.deepStrictEqual(
      stats,
      { ...counters(), conflicts: 1, learnedClausesCurrent: 0 },
      'the cached conflict is reported exactly once',
    );
    assert.deepStrictEqual(solver.solveAssuming(), { status: 'unsat', core: {} });
    assert.deepStrictEqual(stats, { ...counters(), conflicts: 1, learnedClausesCurrent: 0 });
    solver.assertCounters();
    assertRoot(solver);
  });

  it('promotes a matching learned clause to permanent instead of duplicating it', () => {
    // Solving (a∨b)∧(a∨¬b)∧(¬a∨b) learns the root unit (a): the FALSE-first
    // decision conflicts, and analysis learns the asserting unit.
    const solver = new IncrementalAudit(
      compile(and(or('a', 'b'), or('a', not('b')), or(not('a'), 'b'))),
    );
    assert.strictEqual(solver.solveAssuming().status, 'sat');
    const learnedUnit = solver.admissions.find((clause) => clause.lits.length === 1);
    assert.ok(learnedUnit !== undefined, 'a learned unit exists to promote');
    const liveBefore = solver.stats.learnedClausesCurrent;
    const name = internals(solver).indexToName[varOf(learnedUnit.lits[0])];
    assert.ok(name !== undefined);
    solver.add(isNegated(learnedUnit.lits[0]) ? not(name) : and(name));
    assert.strictEqual(learnedUnit.learned, false, 'promoted to permanent');
    assert.strictEqual(
      solver.stats.learnedClausesCurrent,
      liveBefore - 1,
      'the learned duplicate leaves the live learned gauge',
    );
    solver.assertCounters();
    assertRoot(solver);
  });
});

describe('validation contract and models across adds', () => {
  it('rejects unknown names before the add and accepts them after', () => {
    const solver = createSolver(and('a'));
    assert.throws(() => solver.solve({ later: Value.TRUE }), /unknown assumption variable/);
    assert.throws(() => solver.solve({ later: Value.UNSET }), /unknown assumption variable/);
    solver.add(and(implies('a', 'later')));
    // The base forces a=TRUE, so the admitted implication forces later=TRUE:
    // the newly valid name behaves exactly like a construction-time name.
    assert.deepStrictEqual(solver.solve({ later: Value.TRUE }), {
      status: 'sat',
      model: { a: Value.TRUE, later: Value.TRUE },
    });
    assert.deepStrictEqual(solver.solve({ later: Value.FALSE }), {
      status: 'unsat',
      core: { later: Value.FALSE },
    });
    assert.throws(() => solver.solve({ later: 2 as never }), /invalid assumption value/);
    assert.throws(() => solver.solve({ still: Value.UNSET }), /unknown assumption variable/);
  });

  it('covers every known named variable in post-add models, including folded-away names', () => {
    const solver = createSolver(and('a', or('b', and())));
    solver.add(or('c', and('d', 'e')));
    const conjunction = and('a', or('b', and()), or('c', and('d', 'e')));
    const model = expectSatModel(solver.solve());
    assert.deepStrictEqual(Object.keys(model).sort(), ['a', 'b', 'c', 'd', 'e']);
    assert.strictEqual(expressionValue(conjunction, model), Value.TRUE);
  });

  it('lets hooks address appended variables and honors their picks', () => {
    let sawAppended = false;
    const solver = createSolver(and(or('a', 'b'), or('a', 'c')), {
      variablePriority: (unassigned) => {
        if (unassigned.includes('appended')) {
          sawAppended = true;
          return ['appended', true];
        }
        return null;
      },
    });
    solver.add(and(or('appended', 'a'), or(not('appended'), 'b')));
    const conjunction = and(
      or('a', 'b'),
      or('a', 'c'),
      or('appended', 'a'),
      or(not('appended'), 'b'),
    );
    const model = expectSatModel(solver.solve());
    assert.ok(sawAppended, 'the hook saw the appended variable');
    assert.strictEqual(model.appended, Value.TRUE, 'the hook polarity was honored');
    assert.strictEqual(expressionValue(conjunction, model), Value.TRUE);
  });
});

describe('quiescence guards', () => {
  it('throws for a sync add during a parked async solve, then admits once the call settles', async () => {
    let release: (() => void) | undefined;
    let parked = false;
    setYieldScheduler(() => {
      if (!parked) {
        parked = true;
        return new Promise<void>((resolve) => {
          release = resolve;
        });
      }
      return Promise.resolve();
    });
    try {
      const handle = createSolver(wideScan(96));
      const pending = handle.solveAsync(undefined, { yieldQuantum: 64 });
      assert.ok(parked, 'the async call parked mid-scan');
      assert.throws(() => handle.add(and('nope')), /quiescent/);
      assert.ok(release !== undefined);
      release();
      assert.strictEqual((await pending).status, 'sat');
      handle.add(and('late'));
      assert.ok(handle.variables().includes('late'));
      assert.strictEqual(handle.solve().status, 'sat');
    } finally {
      setYieldScheduler(undefined);
    }
  });

  it('throws from a reentrant hook call without disturbing the in-flight solve', () => {
    const handle = createSolver(and(implies('a', 'b'), or('c', not('c'))), {
      variablePriority: () => {
        assert.throws(() => handle.add(and('nope')), /quiescent/);
        return null;
      },
    });
    assert.strictEqual(handle.solve({ a: Value.TRUE }).status, 'sat');
    handle.add(and('d'));
    assert.strictEqual(handle.solve().status, 'sat');
  });

  it('throws during an in-flight enumeration on an internal solver', async () => {
    const solver = new Solver(
      compile(and(...Array.from({ length: 6 }, (_, i) => or(`p${i}`, `q${i}`)))),
    );
    let release: (() => void) | undefined;
    let parked = false;
    setYieldScheduler(() => {
      if (!parked) {
        parked = true;
        return new Promise<void>((resolve) => {
          release = resolve;
        });
      }
      return Promise.resolve();
    });
    try {
      const pending = solver.enumerateModelsAsync(undefined, 64);
      assert.ok(parked, 'enumeration parked between slices');
      assert.throws(() => solver.add(and('nope')), /quiescent/);
      assert.ok(release !== undefined);
      release();
      const result = await pending;
      assert.strictEqual(result.status, 'complete');
      assert.strictEqual(result.models.length, 3 ** 6, 'the undisturbed enumeration completes');
    } finally {
      setYieldScheduler(undefined);
    }
  });

  it('refuses add() on a PLE-enabled internal solver', () => {
    const solver = new Solver(compile(or('a', 'b')), { enablePle: true });
    assert.throws(() => solver.add(and('c')), /enablePle/);
  });
});

describe('abort during a root scan, then add, then solve', () => {
  it('preserves the pending retained-root scan across the abandoned call and the addition', async () => {
    const controller = new AbortController();
    let yields = 0;
    setYieldScheduler(() => {
      yields += 1;
      if (yields >= 1) controller.abort();
      return Promise.resolve();
    });
    let aborted: SolveResult | undefined;
    const handle = createSolver(wideScan(96));
    try {
      aborted = await handle.solveAsync(undefined, { yieldQuantum: 64, signal: controller.signal });
    } finally {
      setYieldScheduler(undefined);
    }
    assert.deepStrictEqual(aborted, { status: 'unknown', reason: 'aborted' });
    // The abandoned call left root propagation pending; the addition must not
    // discard it, and the final solve drains to the same fixpoint as a
    // control handle that never saw the abort.
    const control = createSolver(wideScan(96));
    handle.add(and('post', or('sat0', 'sat1')));
    control.add(and('post', or('sat0', 'sat1')));
    const first = handle.solve();
    assert.deepStrictEqual(first, control.solve(), 'the aborted history reaches the same model');
    const model = expectSatModel(first);
    assert.strictEqual(model.root, Value.TRUE);
    assert.strictEqual(model.post, Value.TRUE);
    assert.strictEqual(
      expressionValue(and(wideScan(96), and('post', or('sat0', 'sat1'))), model),
      Value.TRUE,
    );
  });
});
