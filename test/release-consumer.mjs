// Copied into the fresh consumer by release-smoke.mjs, never run via tsx.
// The only library import is the installed package root; all oracles are local.
import assert from 'node:assert/strict';
import { realpathSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import * as sat from '@divmain/sat';

const { and, or, not, implies, xor, Value, getSolution, getAllSolutions, createSolver } = sat;
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
];
const counters = (value = 0) => Object.fromEntries(statNames.map((name) => [name, value]));

function variables(expr, result = new Set()) {
  if (typeof expr === 'string') result.add(expr);
  else if (Object.hasOwn(expr, 'not')) variables(expr.not, result);
  else for (const child of expr.and ?? expr.or) variables(child, result);
  return [...result].sort();
}

function evaluate(expr, model) {
  if (typeof expr === 'string') return model[expr] === 1;
  if (Object.hasOwn(expr, 'and')) return expr.and.every((child) => evaluate(child, model));
  if (Object.hasOwn(expr, 'or')) return expr.or.some((child) => evaluate(child, model));
  if (Object.hasOwn(expr, 'not')) return !evaluate(expr.not, model);
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

function runtime() {
  const exports = Object.keys(sat).sort();
  assert.deepEqual(exports, [
    'Value',
    'and',
    'createSolver',
    'getAllSolutions',
    'getSolution',
    'implies',
    'not',
    'or',
    'xor',
  ]);
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
  const checks = [];
  const check = (name, probe) => checks.push({ name, status: 'passed', ...probe() });

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
      assert.deepEqual(Object.keys(solver), ['solve']);
      for (const actual of [getSolution(expr), solver.solve(), solver.solve()]) {
        if (expected.length === 0) assert.equal(actual, null);
        else {
          modelFor(expr, actual);
          assert.ok(
            expected.some((model) => variables(expr).every((name) => model[name] === actual[name])),
          );
        }
      }
      modelSet(expr, getAllSolutions(expr), expected);
    }
    return { cases: cases.map(([name, , expected]) => ({ name, models: expected.length })) };
  });

  check('valid inconsistent assumptions, including total root models and empty formulas', () => {
    const expr = and('a', 'b');
    const solver = createSolver(expr);
    for (const assumptions of [{ a: 0 }, { a: 1, b: 0 }]) {
      assert.equal(getSolution(expr, { assumptions }), null);
      assert.deepEqual(getAllSolutions(expr, { assumptions }), []);
      assert.equal(solver.solve(assumptions), null);
      assert.deepEqual(modelFor(expr, solver.solve()), { a: 1, b: 1 });
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
    const first = modelFor(expr, getSolution(expr, { assumptions }), assumptions);
    modelSet(
      expr,
      getAllSolutions(expr, { assumptions }),
      [
        { ...assumptions, ordinary: 0 },
        { ...assumptions, ordinary: 1 },
      ],
      assumptions,
    );
    const solver = createSolver(expr);
    const before = modelFor(expr, solver.solve(assumptions), assumptions);
    const saved = { ...before };
    const opposite = Object.fromEntries(special.map((name) => [name, 1 - assumptions[name]]));
    const after = modelFor(expr, solver.solve(opposite), opposite);
    assert.notEqual(before, after);
    assert.deepEqual(before, saved);
    before.__proto__ = 1 - before.__proto__;
    modelFor(expr, solver.solve(assumptions), assumptions);
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
      const base = solver.solve(undefined, initial);
      if (base === null) {
        const cached = counters(999);
        assert.equal(solver.solve({}, cached), null);
        assert.deepEqual(cached, {
          ...counters(),
          learnedClausesCurrent: initial.learnedClausesCurrent,
        });
      }
      const calls = [
        (assumptions, stats) => getSolution(expr, { assumptions, stats }),
        (assumptions, stats) => getAllSolutions(expr, { assumptions, stats }),
        (assumptions, stats) => solver.solve(assumptions, stats),
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
        if (Array.isArray(actual)) {
          assert.equal(actual.length === 0, base === null);
          for (const model of actual) modelFor(expr, model);
        } else if (base === null) assert.equal(actual, null);
        else modelFor(expr, actual);
      }
    }
    const expr = or('a', 'b');
    const solver = createSolver(expr);
    for (const call of [
      (assumptions) => [getSolution(expr, { assumptions })],
      (assumptions) => getAllSolutions(expr, { assumptions }),
      (assumptions) => [solver.solve(assumptions)],
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
      assert.equal(solver.solve({ a: 1 }, stats), null);
      assert.ok(stats.conflicts > 0 && stats.learnedClauses > 0 && stats.learnedClausesCurrent > 0);
      const first = { ...stats };
      modelFor(expr, solver.solve({ a: 0, x: 1 }, stats), { a: 0, x: 1 });
      assert.deepEqual(stats, {
        ...counters(),
        learnedClausesCurrent: first.learnedClausesCurrent,
      });
      const retained = { ...stats };
      assert.equal(solver.solve({ a: 1 }, stats), null);
      assert.deepEqual(stats, retained);
      for (const assumptions of [{ missing: -1 }, { a: true }]) {
        Object.assign(stats, counters(999));
        assert.throws(() => solver.solve(assumptions, stats), /assumption/);
        assert.deepEqual(stats, retained);
      }
      modelFor(expr, solver.solve());
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
    modelFor(stale, reusable.solve());
    assert.deepEqual(modelFor(stale, reusable.solve({ c: 0 }), { c: 0 }), { a: 0, b: 1, c: 0 });
    modelFor(stale, reusable.solve({ a: 1 }), { a: 1 });
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
    const first = modelFor(expr, solver.solve(assumptions, stats), { a: 1, b: 1 });
    assert.equal(reads, 1);
    assert.ok(
      stats.conflicts > 0 && stats.learnedClauses > 0,
      'Replay witness must actually learn',
    );
    const next = modelFor(expr, solver.solve(assumptions), { a: 0, b: 0 });
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
      () => solver.solve({ a: 1 }, stats),
      (error) => error === failure,
    );
    assert.equal(stats.propagations, 1, 'Report work before callback failure');
    assert.equal(stats.decisions, 0);
    modelFor(expr, solver.solve({ a: 1 }), { a: 1 });
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
    const recovered = modelFor(expr, solver.solve({ a: 0, b: 0 }), { a: 0, b: 0 });
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
          ? [getSolution(expr, { variablePriority })]
          : api === 'all'
            ? getAllSolutions(expr, { variablePriority })
            : [createSolver(expr, { variablePriority }).solve()];
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
    assert.deepEqual(modelFor(expr, solver.solve()), { a: 1, b: 0, root: 1 });
    preferTrue = false;
    assert.deepEqual(modelFor(expr, solver.solve()), { a: 0, b: 1, root: 1 });
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
      assert.deepEqual(modelFor(expr, getSolution(expr, { variablePriority })), {
        a: 0,
        b: 1,
        root: 1,
      });
      assert.deepEqual(modelFor(expr, createSolver(expr, { variablePriority }).solve()), {
        a: 0,
        b: 1,
        root: 1,
      });
      modelSet(expr, getAllSolutions(expr, { variablePriority }), [
        { a: 0, b: 1, root: 1 },
        { a: 1, b: 0, root: 1 },
      ]);
      assert.ok(calls >= 3);
    }
    return { defensiveChoices: choices, savedPhaseOverridden: true };
  });

  check(
    'construction units excluded from incremental stats; blockers excluded from live count',
    () => {
      const expr = and('root', implies('root', 'forced'), free('free'));
      const stats = counters(999);
      modelFor(expr, getSolution(expr, { stats }));
      assert.equal(stats.propagations, 2);
      const single = { ...stats };
      const solver = createSolver(expr);
      modelFor(expr, solver.solve(undefined, stats));
      assert.deepEqual(stats, { ...counters(), decisions: 1, propagations: 1 });
      const first = { ...stats };
      modelFor(expr, solver.solve({ free: 1 }, stats), { free: 1 });
      assert.deepEqual(stats, counters());
      const second = { ...stats };
      const models = getAllSolutions(expr, { stats });
      modelSet(expr, models, [
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
    assert.deepEqual(logs, [[{ ready: 1 }]]);
    shape(logs[0][0], ['ready']);
  } else if (heading === 'Finding a Single Solution') {
    assert.deepEqual(logs, [[worked]]);
    shape(logs[0][0], Object.keys(worked));
  } else if (heading === 'Finding All Solutions') {
    assert.deepEqual(logs, [[[worked]], [[{ a: 0, b: 1 }]]]);
    shape(logs[0][0][0], Object.keys(worked));
    shape(logs[1][0][0], ['a', 'b']);
  } else if (heading === 'Reusing a Compiled Solver') {
    assert.deepEqual(logs, [[{ left: 1, right: 0 }], [null], [{ left: 0, right: 1 }], [true]]);
    shape(logs[0][0], ['left', 'right']);
    shape(logs[2][0], ['left', 'right']);
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
    for (const model of logs[1]) {
      shape(model, names);
      for (const [target, prerequisite] of edges)
        assert.ok(model[target] === 0 || model[prerequisite] === 1);
      for (const forced of ['a', 'b', 'c', 'g', 'h']) assert.equal(model[forced], 1);
    }
  } else throw new Error(`Unrecognized executable README heading: ${heading}`);
  return { status: 'passed', heading, resolution, logs };
}

const [mode, path, heading] = process.argv.slice(2);
assert.ok(mode === 'runtime' || mode === 'readme', 'Expected runtime or readme mode');
const result = mode === 'runtime' ? runtime() : await readme(path, heading);
console.log(JSON.stringify(result, null, 2));
