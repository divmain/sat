// Copied into the fresh consumer by release-smoke.mjs, never run via tsx.
// The only library import is the installed package root; all oracles are local.
import assert from 'node:assert/strict';
import { realpathSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import * as sat from '@divmain/sat';

const {
  and,
  or,
  not,
  implies,
  xor,
  atMostOne,
  atMost,
  atLeast,
  exactly,
  Value,
  getSolution,
  getSolutionAsync,
  getAllSolutions,
  getAllSolutionsAsync,
  createSolver,
  createSolverStats,
} = sat;
const root = realpathSync(dirname(fileURLToPath(import.meta.url)));
assert.deepEqual(process.execArgv, [], 'Runtime probes must use plain Node with no flags/loaders');
assert.equal(process.env.NODE_OPTIONS, undefined);
assert.equal(process.env.NODE_PATH, undefined);
const resolved = import.meta.resolve('@divmain/sat');
const resolution = { url: resolved, realpath: realpathSync(fileURLToPath(resolved)) };
assert.equal(
  resolution.realpath,
  join(root, 'node_modules', '@divmain', 'sat', 'dist', 'index.js'),
);
const free = (name) => or(name, not(name));
const statNames = [
  'decisions',
  'propagations',
  'conflicts',
  'restarts',
  'learnedClauses',
  'learnedClausesCurrent',
  'learnedLiterals',
  'minimizedLiterals',
];
const counters = (value = 0) => Object.fromEntries(statNames.map((name) => [name, value]));

function variables(expr, result = new Set()) {
  if (typeof expr === 'string') result.add(expr);
  else if (Object.hasOwn(expr, 'not')) variables(expr.not, result);
  else if (Object.hasOwn(expr, 'atMost')) {
    for (const child of expr.atMost.exprs) variables(child, result);
  } else if (Object.hasOwn(expr, 'atLeast')) {
    for (const child of expr.atLeast.exprs) variables(child, result);
  } else for (const child of expr.and ?? expr.or) variables(child, result);
  return [...result].sort();
}

function evaluate(expr, model) {
  if (typeof expr === 'string') return model[expr] === 1;
  if (Object.hasOwn(expr, 'and')) return expr.and.every((child) => evaluate(child, model));
  if (Object.hasOwn(expr, 'or')) return expr.or.some((child) => evaluate(child, model));
  if (Object.hasOwn(expr, 'not')) return !evaluate(expr.not, model);
  // Cardinality operands are a multiset: repeated operands count repeatedly.
  if (Object.hasOwn(expr, 'atMost')) {
    const count = expr.atMost.exprs.filter((child) => evaluate(child, model)).length;
    return count <= expr.atMost.k;
  }
  if (Object.hasOwn(expr, 'atLeast')) {
    const count = expr.atLeast.exprs.filter((child) => evaluate(child, model)).length;
    return count >= expr.atLeast.k;
  }
  throw new Error('Unexpected Boolean AST');
}

function shape(model, names) {
  assert.ok(model !== null && typeof model === 'object', 'Expected a model');
  assert.equal(Object.getPrototypeOf(model), Object.prototype, 'Model must be an ordinary object');
  const keys = Reflect.ownKeys(model);
  assert.ok(
    keys.every((key) => typeof key === 'string'),
    'No symbol/auxiliary properties',
  );
  assert.deepEqual(keys.sort(), [...names].sort(), 'Model must contain every named variable only');
  for (const name of names) {
    const descriptor = Object.getOwnPropertyDescriptor(model, name);
    assert.ok(
      descriptor && Object.hasOwn(descriptor, 'value'),
      `Not an own data property: ${name}`,
    );
    assert.equal(descriptor.enumerable, true);
    assert.ok(descriptor.value === 0 || descriptor.value === 1, `Not a numeric Boolean: ${name}`);
  }
}

function modelFor(expr, model, assumptions = {}) {
  shape(model, variables(expr));
  assert.equal(evaluate(expr, model), true, 'Independent AST evaluation failed');
  for (const [name, value] of Object.entries(assumptions)) {
    if (value !== -1) {
      assert.ok(Object.hasOwn(model, name));
      assert.equal(model[name], value, `Model lost assumption ${name}`);
    }
  }
  return model;
}

function modelSet(expr, models, expected, assumptions = {}) {
  assert.ok(Array.isArray(models));
  assert.equal(new Set(models).size, models.length, 'Enumeration must return detached objects');
  const names = variables(expr);
  const key = (model) => JSON.stringify(names.map((name) => model[name]));
  for (const model of models) modelFor(expr, model, assumptions);
  assert.deepEqual(models.map(key).sort(), expected.map(key).sort());
}

async function runtime() {
  const exports = Object.keys(sat).sort();
  assert.deepEqual(exports, [
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
  assert.deepEqual(createSolverStats(), counters());
  const forbidden = [
    'default',
    'compileCount',
    'compile',
    'Solver',
    'CompiledCnf',
    'Clause',
    'SolverOptions',
    'getVariables',
    'isVariable',
    'parseDimacs',
    'DIMACS',
    'selectNextVar',
    'SelectNextVariable',
    'NextVariable',
    'bruteForceAllSolutions',
    'getInitialAssignments',
    'defaultSelect',
    'allPossibleAssignments',
    'dpllSolution',
    'sequence',
    'expressionValue',
  ];
  for (const name of forbidden) assert.equal(Object.hasOwn(sat, name), false, name);
  assert.deepEqual([Value.UNSET, Value.FALSE, Value.TRUE], [-1, 0, 1]);
  assert.deepEqual(and('a', 'b'), { and: ['a', 'b'] });
  assert.deepEqual(or('a', 'b'), { or: ['a', 'b'] });
  assert.deepEqual(not('a'), { not: 'a' });
  assert.deepEqual(implies('a', 'b'), { or: [{ not: 'a' }, 'b'] });
  assert.deepEqual(xor('a', 'b'), {
    or: [{ and: ['a', { not: 'b' }] }, { and: [{ not: 'a' }, 'b'] }],
  });
  // Cardinality constructors: atMostOne is pure atMost(1, …) sugar, and
  // exactly(k, …) is atMost ∧ atLeast over the same operand multiset.
  assert.deepEqual(atMostOne('a', 'b'), { atMost: { k: 1, exprs: ['a', 'b'] } });
  assert.deepEqual(atMost(2, 'a', 'b'), { atMost: { k: 2, exprs: ['a', 'b'] } });
  assert.deepEqual(atLeast(2, 'a', 'b'), { atLeast: { k: 2, exprs: ['a', 'b'] } });
  assert.deepEqual(exactly(1, 'a', 'b'), {
    and: [{ atMost: { k: 1, exprs: ['a', 'b'] } }, { atLeast: { k: 1, exprs: ['a', 'b'] } }],
  });
  assert.throws(() => atMost(-1, 'a'), /non-negative safe integer/);
  assert.throws(() => atLeast(1.5, 'a'), /non-negative safe integer/);
  assert.throws(() => exactly(Number.MAX_SAFE_INTEGER + 1, 'a'), /non-negative safe integer/);
  const checks = [];
  const check = (name, probe) => checks.push({ name, status: 'passed', ...probe() });
  const asyncCheck = async (name, probe) =>
    checks.push({ name, status: 'passed', ...(await probe()) });

  check('constructors, SAT/UNSAT/empty semantics across all three APIs', () => {
    const cases = [
      ['and', and('a', 'b'), [{ a: 1, b: 1 }]],
      [
        'or',
        or('a', 'b'),
        [
          { a: 0, b: 1 },
          { a: 1, b: 0 },
          { a: 1, b: 1 },
        ],
      ],
      ['not', not('a'), [{ a: 0 }]],
      [
        'implies',
        implies('a', 'b'),
        [
          { a: 0, b: 0 },
          { a: 0, b: 1 },
          { a: 1, b: 1 },
        ],
      ],
      [
        'xor',
        xor('a', 'b'),
        [
          { a: 0, b: 1 },
          { a: 1, b: 0 },
        ],
      ],
      [
        'atMostOne',
        atMostOne('a', 'b', 'c'),
        [
          { a: 0, b: 0, c: 0 },
          { a: 1, b: 0, c: 0 },
          { a: 0, b: 1, c: 0 },
          { a: 0, b: 0, c: 1 },
        ],
      ],
      [
        'atLeast',
        atLeast(2, 'a', 'b', 'c'),
        [
          { a: 1, b: 1, c: 0 },
          { a: 1, b: 0, c: 1 },
          { a: 0, b: 1, c: 1 },
          { a: 1, b: 1, c: 1 },
        ],
      ],
      [
        'exactly',
        exactly(2, 'a', 'b', 'c'),
        [
          { a: 1, b: 1, c: 0 },
          { a: 1, b: 0, c: 1 },
          { a: 0, b: 1, c: 1 },
        ],
      ],
      [
        'atMost-fold',
        atMost(5, 'a', 'b'),
        [
          { a: 0, b: 0 },
          { a: 0, b: 1 },
          { a: 1, b: 0 },
          { a: 1, b: 1 },
        ],
      ],
      // Multiplicity: two occurrences of a true 'a' exceed exactly(1, …).
      ['exactly-multiplicity', exactly(1, 'a', 'a'), []],
      // A nested (totalized) threshold under not/or.
      [
        'nested-cardinality',
        or(not(atMost(1, 'a', 'b')), 'c'),
        [
          { a: 1, b: 1, c: 0 },
          { a: 1, b: 1, c: 1 },
          { a: 0, b: 0, c: 1 },
          { a: 0, b: 1, c: 1 },
          { a: 1, b: 0, c: 1 },
        ],
      ],
      [
        'worked',
        and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e'))),
        [{ a: 1, b: 0, c: 1, d: 1, e: 1 }],
      ],
      [
        'dont-care',
        and('a', free('b')),
        [
          { a: 1, b: 0 },
          { a: 1, b: 1 },
        ],
      ],
      ['contradiction', and('a', not('a')), []],
      ['empty-and', and(), [{}]],
      ['empty-or', or(), []],
    ];
    for (const [, expr, expected] of cases) {
      const solver = createSolver(expr);
      assert.deepEqual(Object.keys(solver), ['solve', 'solveAsync', 'add', 'variables']);
      for (const actual of [getSolution(expr), solver.solve(), solver.solve()]) {
        if (expected.length === 0) {
          assert.equal(actual.status, 'unsat');
          // No assumptions supplied: the only sound core is the empty one.
          shape(actual.core, []);
        } else {
          assert.equal(actual.status, 'sat');
          modelFor(expr, actual.model);
          assert.ok(
            expected.some((model) =>
              variables(expr).every((name) => model[name] === actual.model[name]),
            ),
          );
        }
      }
      const enumeration = getAllSolutions(expr);
      assert.equal(enumeration.status, 'complete');
      modelSet(expr, enumeration.models, expected);
    }
    return { cases: cases.map(([name, , expected]) => ({ name, models: expected.length })) };
  });

  check('valid inconsistent assumptions, including total root models and empty formulas', () => {
    const expr = and('a', 'b');
    const solver = createSolver(expr);
    for (const assumptions of [{ a: 0 }, { a: 1, b: 0 }]) {
      // The failed-assumption core names exactly the contradictory facts.
      const expectedCore = assumptions.a === 0 ? { a: 0 } : { b: 0 };
      assert.deepEqual(getSolution(expr, { assumptions }), { status: 'unsat', core: expectedCore });
      assert.deepEqual(getAllSolutions(expr, { assumptions }), { status: 'complete', models: [] });
      assert.deepEqual(solver.solve(assumptions), { status: 'unsat', core: expectedCore });
      assert.deepEqual(modelFor(expr, solver.solve().model), { a: 1, b: 1 });
    }
    for (const empty of [and(), or()]) {
      const reusable = createSolver(empty);
      reusable.solve();
      const assumptions = { missing: -1 };
      for (const call of [
        () => getSolution(empty, { assumptions }),
        () => getAllSolutions(empty, { assumptions }),
        () => reusable.solve(assumptions),
      ])
        assert.throws(call, /unknown assumption variable.*missing/);
    }
    return { totalRootContradictions: 2, emptyFormulaUnknownUnsetRejections: 6 };
  });

  check('own numeric properties, special names, complete and detached models', () => {
    const special = [
      '__proto__',
      'constructor',
      'toString',
      'hasOwnProperty',
      '',
      '2',
      '10',
      'quote"\\\n\u03bb',
    ];
    const expr = and(...[...special, 'ordinary'].map(free));
    const assumptions = Object.fromEntries(special.map((name, index) => [name, index % 2]));
    const first = modelFor(expr, getSolution(expr, { assumptions }).model, assumptions);
    const enumerated = getAllSolutions(expr, { assumptions });
    assert.equal(enumerated.status, 'complete');
    modelSet(
      expr,
      enumerated.models,
      [
        { ...assumptions, ordinary: 0 },
        { ...assumptions, ordinary: 1 },
      ],
      assumptions,
    );
    const solver = createSolver(expr);
    const before = modelFor(expr, solver.solve(assumptions).model, assumptions);
    const saved = { ...before };
    const opposite = Object.fromEntries(special.map((name) => [name, 1 - assumptions[name]]));
    const after = modelFor(expr, solver.solve(opposite).model, opposite);
    assert.notEqual(before, after);
    assert.deepEqual(before, saved);
    before.__proto__ = 1 - before.__proto__;
    modelFor(expr, solver.solve(assumptions).model, assumptions);
    return { names: variables(expr), first, opposite: after };
  });

  check('validation before UNSAT/cache, UNSET, inherited and symbol entries', () => {
    const searchedUnsat = and(
      or('a', 'b'),
      or('a', not('b')),
      or(not('a'), 'b'),
      or(not('a'), not('b')),
    );
    const invalid = [
      true,
      false,
      '1',
      undefined,
      null,
      2,
      -2,
      Number.NaN,
      Number.POSITIVE_INFINITY,
      1n,
      Symbol('bad'),
      {},
      [],
    ];
    let rejected = 0;
    for (const expr of [and('a'), and('a', or()), and('a', not('a')), searchedUnsat]) {
      const solver = createSolver(expr);
      const initial = counters(999);
      const base = solver.solve(undefined, { stats: initial });
      if (base.status === 'unsat') {
        const cached = counters(999);
        // Cached base UNSAT: an assumption-independent proof cores on {}.
        assert.deepEqual(solver.solve({}, { stats: cached }), { status: 'unsat', core: {} });
        assert.deepEqual(cached, {
          ...counters(),
          learnedClausesCurrent: initial.learnedClausesCurrent,
        });
      }
      const calls = [
        (assumptions, stats) => getSolution(expr, { assumptions, stats }),
        (assumptions, stats) => getAllSolutions(expr, { assumptions, stats }),
        (assumptions, stats) => solver.solve(assumptions, { stats }),
      ];
      for (const call of calls) {
        for (const missing of [-1, 0, 1]) {
          const stats = counters(999);
          assert.throws(
            () => call({ a: 0, missing }, stats),
            /unknown assumption variable.*missing/,
          );
          assert.equal(stats.decisions, 0);
          rejected += 1;
        }
        for (const value of invalid) {
          const stats = counters(999);
          assert.throws(() => call({ a: value }, stats), /invalid assumption value.*a/);
          assert.equal(stats.decisions, 0);
          for (const counter of Object.values(stats))
            assert.ok(Number.isSafeInteger(counter) && counter >= 0 && counter < 999);
          rejected += 1;
        }
        const actual = call({ a: -1 });
        if (actual.status === 'complete') {
          assert.equal(actual.models.length === 0, base.status === 'unsat');
          for (const model of actual.models) modelFor(expr, model);
        } else if (base.status === 'unsat') assert.equal(actual.status, 'unsat');
        else modelFor(expr, actual.model);
      }
    }
    const expr = or('a', 'b');
    const solver = createSolver(expr);
    for (const call of [
      (assumptions) => [getSolution(expr, { assumptions }).model],
      (assumptions) => getAllSolutions(expr, { assumptions }).models,
      (assumptions) => [solver.solve(assumptions).model],
    ]) {
      let reads = 0;
      const assumptions = Object.create({ inheritedUnknown: true });
      Object.defineProperty(assumptions, 'hiddenUnknown', { value: true });
      assumptions[Symbol('ignored')] = true;
      Object.defineProperty(assumptions, 'a', {
        enumerable: true,
        get: () => {
          reads += 1;
          return 1;
        },
      });
      for (const model of call(assumptions)) modelFor(expr, model, { a: 1 });
      assert.equal(reads, 1);
    }
    return { rejected, getterReadsPerCall: 1, ignoredInheritedNonenumerableAndSymbols: true };
  });

  check(
    'lost assumptions, local UNSAT recovery, per-call admissions and retained live count',
    () => {
      const expr = and(implies('a', 'x'), implies('a', not('x')));
      const solver = createSolver(expr);
      const stats = counters(999);
      assert.deepEqual(solver.solve({ a: 1 }, { stats }), { status: 'unsat', core: { a: 1 } });
      assert.ok(stats.conflicts > 0 && stats.learnedClauses > 0 && stats.learnedClausesCurrent > 0);
      const first = { ...stats };
      modelFor(expr, solver.solve({ a: 0, x: 1 }, { stats }).model, { a: 0, x: 1 });
      assert.deepEqual(stats, {
        ...counters(),
        learnedClausesCurrent: first.learnedClausesCurrent,
      });
      const retained = { ...stats };
      assert.deepEqual(solver.solve({ a: 1 }, { stats }), { status: 'unsat', core: { a: 1 } });
      assert.deepEqual(stats, retained);
      for (const assumptions of [{ missing: -1 }, { a: true }]) {
        Object.assign(stats, counters(999));
        assert.throws(() => solver.solve(assumptions, { stats }), /assumption/);
        assert.deepEqual(stats, retained);
      }
      modelFor(expr, solver.solve().model);
      assert.deepEqual(
        stats,
        retained,
        'Omitted outputs must not keep mutating the previous stats object',
      );
      return { first, nextCall: retained };
    },
  );

  check('no stale PLE pins; assumptions replayed from a one-read snapshot after learning', () => {
    const stale = and(or('a', 'b'), or(not('a'), 'c'));
    const reusable = createSolver(stale);
    modelFor(stale, reusable.solve().model);
    assert.deepEqual(modelFor(stale, reusable.solve({ c: 0 }).model, { c: 0 }), {
      a: 0,
      b: 1,
      c: 0,
    });
    modelFor(stale, reusable.solve({ a: 1 }).model, { a: 1 });
    const expr = and(free('a'), free('b'), or('x', 't'), or('x', not('t')));
    let reads = 0;
    let suppliedA = 1;
    const assumptions = {
      b: 1,
      get a() {
        reads += 1;
        return suppliedA;
      },
    };
    const solver = createSolver(expr, {
      variablePriority: (unassigned) => {
        suppliedA = 0;
        assumptions.b = 0;
        return unassigned.includes('x') ? ['x', false] : null;
      },
    });
    const stats = counters(999);
    const first = modelFor(expr, solver.solve(assumptions, { stats }).model, { a: 1, b: 1 });
    assert.equal(reads, 1);
    assert.ok(
      stats.conflicts > 0 && stats.learnedClauses > 0,
      'Replay witness must actually learn',
    );
    const next = modelFor(expr, solver.solve(assumptions).model, { a: 0, b: 0 });
    assert.equal(reads, 2);
    return { first, next, getterReads: reads, firstCallStats: stats };
  });

  check('callback/getter exceptions and reentry do not poison later calls', () => {
    const expr = and(implies('a', 'b'), free('free'));
    const failure = new Error('consumer priority failure');
    let fail = true;
    let reenter = true;
    const solver = createSolver(expr, {
      variablePriority: () => {
        if (fail) {
          fail = false;
          throw failure;
        }
        if (reenter) {
          reenter = false;
          assert.throws(() => solver.solve(), /reentered/);
        }
        return null;
      },
    });
    const stats = counters(999);
    assert.throws(
      () => solver.solve({ a: 1 }, { stats }),
      (error) => error === failure,
    );
    assert.equal(stats.propagations, 1, 'Report work before callback failure');
    assert.equal(stats.decisions, 0);
    modelFor(expr, solver.solve({ a: 1 }).model, { a: 1 });
    assert.throws(
      () =>
        solver.solve({
          a: 1,
          get b() {
            throw failure;
          },
        }),
      (error) => error === failure,
    );
    const recovered = modelFor(expr, solver.solve({ a: 0, b: 0 }).model, { a: 0, b: 0 });
    return { throwingCallStats: stats, recovered };
  });

  check('hook named-unassigned/partial-own snapshots and null fallback across APIs', () => {
    const expr = and(
      '__proto__',
      not('constructor'),
      xor('left', 'right'),
      free('ordinary'),
      free('toString'),
    );
    const names = variables(expr);
    const counts = [];
    for (const api of ['single', 'all', 'incremental']) {
      let calls = 0;
      const variablePriority = (unassigned, partial) => {
        calls += 1;
        assert.ok(unassigned.length > 0);
        assert.equal(new Set(unassigned).size, unassigned.length);
        shape(
          partial,
          names.filter((name) => !unassigned.includes(name)),
        );
        assert.deepEqual([...Object.keys(partial), ...unassigned].sort(), names);
        assert.equal(partial.__proto__, 1);
        assert.equal(partial.constructor, 0);
        for (const name of unassigned) assert.equal(Object.hasOwn(partial, name), false);
        if (unassigned.includes('ordinary')) assert.equal(partial.ordinary, undefined);
        // These are snapshots, not a way to change solver state or its fallback heap.
        partial.__proto__ = 0;
        partial.constructor = 1;
        unassigned.length = 0;
        return null;
      };
      const models =
        api === 'single'
          ? [getSolution(expr, { variablePriority }).model]
          : api === 'all'
            ? getAllSolutions(expr, { variablePriority }).models
            : [createSolver(expr, { variablePriority }).solve().model];
      for (const model of models) modelFor(expr, model);
      assert.ok(calls > 0);
      if (api === 'all') assert.equal(models.length, 8);
      counts.push({ api, calls });
    }
    return { counts };
  });

  check('boolean polarity overrides saved phase; defensive choices defer to VSIDS', () => {
    const expr = and('root', xor('a', 'b'));
    let preferTrue = true;
    const solver = createSolver(expr, { variablePriority: () => ['a', preferTrue] });
    assert.deepEqual(modelFor(expr, solver.solve().model), { a: 1, b: 0, root: 1 });
    preferTrue = false;
    assert.deepEqual(modelFor(expr, solver.solve().model), { a: 0, b: 1, root: 1 });
    const choices = [
      null,
      ['unknown', true],
      ['root', false],
      ['a', 1],
      ['a'],
      ['a', true, 'extra'],
      'a',
    ];
    for (const choice of choices) {
      let calls = 0;
      const variablePriority = () => {
        calls += 1;
        return choice;
      };
      assert.deepEqual(modelFor(expr, getSolution(expr, { variablePriority }).model), {
        a: 0,
        b: 1,
        root: 1,
      });
      assert.deepEqual(modelFor(expr, createSolver(expr, { variablePriority }).solve().model), {
        a: 0,
        b: 1,
        root: 1,
      });
      const enumerated = getAllSolutions(expr, { variablePriority });
      assert.equal(enumerated.status, 'complete');
      modelSet(expr, enumerated.models, [
        { a: 0, b: 1, root: 1 },
        { a: 1, b: 0, root: 1 },
      ]);
      assert.ok(calls >= 3);
    }
    return { defensiveChoices: choices, savedPhaseOverridden: true };
  });

  // Async entry points under the REAL platform scheduler: yieldQuantum 64
  // over a wide formula forces genuine event-loop yields (MessageChannel
  // posts on this Node — no scheduler global exists here), and natural exit
  // of this process proves a settled solve retains no ports or listeners.
  await asyncCheck('async solves settle with real yields, budgets, aborts, and reuse', async () => {
    const wide = and(...Array.from({ length: 96 }, (_, i) => or(`w${i}`, not(`w${i}`))));
    const wideSingle = await getSolutionAsync(wide, { yieldQuantum: 64 });
    assert.equal(wideSingle.status, 'sat');
    modelFor(wide, wideSingle.model);
    const wideAll = await getAllSolutionsAsync(and('a', or('a', 'b')), { yieldQuantum: 64 });
    assert.equal(wideAll.status, 'complete');
    modelSet(and('a', or('a', 'b')), wideAll.models, [
      { a: 1, b: 0 },
      { a: 1, b: 1 },
    ]);
    const boundary = and(
      or('a', 'b'),
      or('a', not('b')),
      or(not('a'), 'b'),
      or(not('a'), not('b')),
    );
    const budgeted = await getSolutionAsync(boundary, { conflictBudget: 1, yieldQuantum: 64 });
    assert.deepEqual(budgeted, { status: 'unknown', reason: 'conflictBudget' });
    const handle = createSolver(xor('left', 'right'));
    assert.deepEqual(await handle.solveAsync({ left: 1 }, { yieldQuantum: 64 }), {
      status: 'sat',
      model: { left: 1, right: 0 },
    });
    const controller = new AbortController();
    controller.abort();
    assert.deepEqual(await handle.solveAsync(undefined, { signal: controller.signal }), {
      status: 'unknown',
      reason: 'aborted',
    });
    const reused = handle.solve();
    assert.equal(reused.status, 'sat');
    modelFor(xor('left', 'right'), reused.model);
    return { yieldsForced: true, budgetUnknown: true, aborted: true, reused: true };
  });

  check('add() conjoins constraints failure-atomically; variables() stays sorted', () => {
    const base = xor('left', 'right');
    const solver = createSolver(base);
    assert.deepEqual(solver.variables(), ['left', 'right']);
    assert.equal(solver.solve({ left: 1 }).status, 'sat');
    // New names become valid assumption/model names immediately.
    const extension = and(implies('left', 'extra'), or('extra', 'right'));
    solver.add(extension);
    assert.deepEqual(solver.variables(), ['extra', 'left', 'right']);
    const whole = and(base, extension);
    modelFor(whole, solver.solve({ extra: 1 }).model, { extra: 1 });
    modelFor(whole, solver.solve().model);
    // A failed add leaves the handle unchanged and reusable.
    assert.throws(() => solver.add({ and: 'nope' }), /invalid BooleanExpr/);
    assert.deepEqual(solver.variables(), ['extra', 'left', 'right']);
    assert.equal(solver.solve().status, 'sat');
    // Strengthening to UNSAT is retained, with an assumption-independent core.
    solver.add(and(not('left'), not('right'), not('extra')));
    assert.deepEqual(solver.solve(), { status: 'unsat', core: {} });
    assert.deepEqual(solver.solve({ extra: 1 }), { status: 'unsat', core: {} });
    return { variables: solver.variables() };
  });

  check(
    'construction units excluded from incremental stats; blockers excluded from live count',
    () => {
      const expr = and('root', implies('root', 'forced'), free('free'));
      const stats = counters(999);
      modelFor(expr, getSolution(expr, { stats }).model);
      assert.equal(stats.propagations, 2);
      const single = { ...stats };
      const solver = createSolver(expr);
      modelFor(expr, solver.solve(undefined, { stats }).model);
      assert.deepEqual(stats, { ...counters(), decisions: 1, propagations: 1 });
      const first = { ...stats };
      modelFor(expr, solver.solve({ free: 1 }, { stats }).model, { free: 1 });
      assert.deepEqual(stats, counters());
      const second = { ...stats };
      const enumeration = getAllSolutions(expr, { stats });
      assert.equal(enumeration.status, 'complete');
      modelSet(expr, enumeration.models, [
        { root: 1, forced: 1, free: 0 },
        { root: 1, forced: 1, free: 1 },
      ]);
      assert.ok(stats.decisions > 0);
      assert.equal(stats.learnedClauses, 0);
      assert.equal(stats.learnedClausesCurrent, 0);
      return { single, first, second, enumeration: stats };
    },
  );
  return { status: 'passed', resolution, exports, forbidden, checks };
}

async function readme(path, heading) {
  const logs = [];
  const original = console.log;
  // Import the untouched file in its own plain-Node process. Validate actual
  // objects (including descriptors) before serializing their recorded outputs.
  console.log = (...values) => {
    logs.push(values);
  };
  try {
    await import(pathToFileURL(path).href);
  } finally {
    console.log = original;
  }
  const worked = { a: 1, b: 0, c: 1, d: 1, e: 1 };
  if (heading === 'Basic Usage') {
    assert.deepEqual(logs, [[{ status: 'sat', model: { ready: 1 } }]]);
    shape(logs[0][0].model, ['ready']);
  } else if (heading === 'Finding a Single Solution') {
    assert.deepEqual(logs, [[{ status: 'sat', model: worked }]]);
    shape(logs[0][0].model, Object.keys(worked));
  } else if (heading === 'Finding All Solutions') {
    assert.deepEqual(logs, [
      [{ status: 'complete', models: [worked] }],
      [{ status: 'complete', models: [{ a: 0, b: 1 }] }],
    ]);
    shape(logs[0][0].models[0], Object.keys(worked));
    shape(logs[1][0].models[0], ['a', 'b']);
  } else if (heading === 'Reusing a Compiled Solver') {
    assert.deepEqual(logs, [
      [{ status: 'sat', model: { left: 1, right: 0 } }],
      [{ status: 'unsat', core: { left: 1, right: 1 } }],
      [{ status: 'sat', model: { left: 0, right: 1 } }],
      ['sat'],
    ]);
    shape(logs[0][0].model, ['left', 'right']);
    shape(logs[1][0].core, ['left', 'right']);
    shape(logs[2][0].model, ['left', 'right']);
  } else if (heading === 'Adding Constraints Incrementally') {
    const vertices = ['a', 'b', 'c', 'd'];
    const names = [];
    for (const v of vertices) for (let k = 0; k < 3; k += 1) names.push(`${v}#${k}`);
    assert.deepEqual(logs[0], ['palette 3: sat']);
    assert.deepEqual(logs[1], ['palette 2: sat']);
    assert.deepEqual(logs[2], ['palette 1: unsat']);
    assert.deepEqual(logs[3], [12]);
    const model = logs[4][0];
    shape(model, names);
    // Independently verify the final 2-coloring: palette 1 was UNSAT, so the
    // retained model is the palette-2 one — no '#2' variable may be set...
    for (const v of vertices) assert.equal(model[`${v}#2`], 0, 'color 2 forbidden');
    // ...every vertex is colored...
    for (const v of vertices) assert.ok(model[`${v}#0`] + model[`${v}#1`] >= 1, `colored: ${v}`);
    // ...and adjacent vertices never share one.
    for (const [u, v] of [
      ['a', 'b'],
      ['b', 'c'],
      ['c', 'd'],
      ['d', 'a'],
    ]) {
      for (const k of [0, 1]) {
        assert.ok(!(model[`${u}#${k}`] === 1 && model[`${v}#${k}`] === 1), `edge ${u}-${v} @${k}`);
      }
    }
    // The deterministic solver reproduces the exact fenced model.
    assert.deepEqual(model, {
      'a#0': 0,
      'a#1': 1,
      'a#2': 0,
      'b#0': 1,
      'b#1': 0,
      'b#2': 0,
      'c#0': 0,
      'c#1': 1,
      'c#2': 0,
      'd#0': 1,
      'd#1': 0,
      'd#2': 0,
    });
  } else if (heading === 'Cardinality Constraints') {
    // The on-call rotation example: SAT, exactly seven schedules (three
    // primaries; with Ada primary her reviewer self-conflict forbids
    // reviewer-ada, leaving reviewer-bo forced), and UNSAT with an
    // assumption-independent core once both reviewers are excluded.
    assert.deepEqual(logs, [['sat'], [7], [{ status: 'unsat', core: {} }]]);
  } else if (heading === 'Async Solving') {
    // The fenced example awaits a budgeted, fine-quantum async solve: its
    // output is exactly the sync result's, and top-level await settlement
    // under plain Node re-proves that no scheduler resource leaks.
    assert.deepEqual(logs, [[{ status: 'sat', model: { a: 1, b: 1 } }]]);
    shape(logs[0][0].model, ['a', 'b']);
  } else if (heading === '`SolverStats`') {
    assert.deepEqual(logs, [[1], [0]]);
  } else if (heading === 'Ported Hypergraph Heuristic') {
    assert.equal(logs.length, 2);
    assert.deepEqual(logs[0], [2, 16, 0]);
    assert.equal(logs[1].length, 2);
    const names = 'abcdefghijklmnopqrs'.split('');
    // Independent, fixed 19-variable/18-edge oracle, not read back from snippet data.
    const edges = [
      ['b', 'a'],
      ['c', 'a'],
      ['e', 'd'],
      ['g', 'c'],
      ['f', 'c'],
      ['f', 'e'],
      ['h', 'b'],
      ['h', 'g'],
      ['j', 'i'],
      ['k', 'j'],
      ['l', 'k'],
      ['m', 'l'],
      ['n', 'm'],
      ['o', 'n'],
      ['p', 'o'],
      ['q', 'p'],
      ['r', 'q'],
      ['s', 'r'],
    ];
    assert.equal(names.length, 19);
    assert.equal(edges.length, 18);
    for (const result of logs[1]) {
      assert.equal(result.status, 'sat');
      shape(result.model, names);
      for (const [target, prerequisite] of edges)
        assert.ok(result.model[target] === 0 || result.model[prerequisite] === 1);
      for (const forced of ['a', 'b', 'c', 'g', 'h']) assert.equal(result.model[forced], 1);
    }
  } else throw new Error(`Unrecognized executable README heading: ${heading}`);
  return { status: 'passed', heading, resolution, logs };
}

const [mode, path, heading] = process.argv.slice(2);
assert.ok(mode === 'runtime' || mode === 'readme', 'Expected runtime or readme mode');
const result = mode === 'runtime' ? await runtime() : await readme(path, heading);
console.log(JSON.stringify(result, null, 2));
