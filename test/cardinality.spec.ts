// Cardinality constraints (Design § Compiler, Cardinality constraints):
// constructor and compile-time validation, the sanctioned structural
// carve-outs, edge folds with named-universe preservation, multiplicity
// semantics, and the two encoding-oracle families —
//   - ASSERTED (conjunctive) counters: extension correctness for every valid
//     named valuation and propagation refutation of every violating one,
//     WITHOUT requiring all auxiliaries/clauses to be decided (a Sinz counter
//     over seven false inputs is valid even with every counter auxiliary
//     unset). The existing full-gate tests in compile.spec.ts are untouched
//     and do not apply here.
//   - NESTED (non-conjunctive) thresholds: fully reified totalizer outputs,
//     so the full-gate oracle DOES apply — propagation from a total named
//     assignment derives every auxiliary in both polarities, satisfying every
//     clause exactly when the reference evaluator accepts.
//
// Test files import internal modules via extensionless paths: tsx resolves
// them, and tsc never compiles test/.

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
  and,
  atLeast,
  atMost,
  atMostOne,
  exactly,
  getVariables,
  implies,
  not,
  or,
  Value,
  xor,
} from '../src/expr';
import type { BooleanExpr, Variable, VariableAssignments } from '../src/expr';
import { compile, litValue, neg, negLit, posLit } from '../src/compile';
import type { CompiledCnf } from '../src/compile';
import { getAllSolutions, getSolution } from '../src/index';
import {
  assertModelListsEqual,
  assertModelShape,
  enumerateAssignments,
  expectCompleteModels,
  expectSatModel,
  expressionValue,
  hasSatisfyingExtension,
  propagateCnf,
  propagationRefutes,
  referenceModels,
} from './helpers';

// Look up a named variable's index, failing loudly if absent.
function indexOf(cnf: CompiledCnf, name: Variable): number {
  const index = cnf.nameToIndex.get(name);
  if (index === undefined) {
    throw new Error(`missing named variable: ${name}`);
  }
  return index;
}

const clauseSet = (cnf: CompiledCnf): Set<string> =>
  new Set(cnf.clauses.map((clause) => clause.lits.join(',')));

// Every model of `expr` compared order-insensitively against the independent
// reference enumerator, with the getSolution verdict triangle and per-model
// shape/validity checks.
function assertSolverAgreement(expr: BooleanExpr): void {
  const reference = referenceModels(expr);
  const result = getSolution(expr);
  assert.strictEqual(result.status === 'sat', reference.length > 0, 'verdict triangle');
  const models = expectCompleteModels(getAllSolutions(expr));
  assertModelListsEqual(models, reference);
  for (const model of models) {
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE);
  }
  if (result.status === 'sat') {
    assertModelShape(result.model, expr);
    assert.ok(
      reference.some((candidate) =>
        Object.entries(result.status === 'sat' ? result.model : {}).every(
          ([name, value]) => candidate[name] === value,
        ),
      ),
      'the single-shot model is in the reference set',
    );
  }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

describe('cardinality constructors', () => {
  it('build the documented AST shapes', () => {
    assert.deepStrictEqual(atMostOne('a', 'b'), { atMost: { k: 1, exprs: ['a', 'b'] } });
    assert.deepStrictEqual(atMost(2, 'a', 'b'), { atMost: { k: 2, exprs: ['a', 'b'] } });
    assert.deepStrictEqual(atLeast(3, 'a'), { atLeast: { k: 3, exprs: ['a'] } });
    // exactly(k, ...) is and(atMost(k, ...), atLeast(k, ...)) sugar.
    assert.deepStrictEqual(exactly(1, 'a', 'b'), {
      and: [{ atMost: { k: 1, exprs: ['a', 'b'] } }, { atLeast: { k: 1, exprs: ['a', 'b'] } }],
    });
    // Zero operands and a zero bound are constructible; compilation folds them.
    assert.deepStrictEqual(atMost(0), { atMost: { k: 0, exprs: [] } });
    assert.deepStrictEqual(atLeast(0), { atLeast: { k: 0, exprs: [] } });
  });

  it('validate k at construction with a descriptive Error', () => {
    const badBounds: Array<[string, number]> = [
      ['-1', -1],
      ['1.5', 1.5],
      ['NaN', Number.NaN],
      ['Infinity', Number.POSITIVE_INFINITY],
      ['2^53', 2 ** 53],
    ];
    for (const [label, k] of badBounds) {
      assert.throws(() => atMost(k, 'a'), {
        name: 'Error',
        message: `atMost requires k to be a non-negative safe integer (got ${
          label === '2^53' ? 2 ** 53 : label
        })`,
      });
      assert.throws(() => atLeast(k, 'a'), {
        name: 'Error',
        message: `atLeast requires k to be a non-negative safe integer (got ${
          label === '2^53' ? 2 ** 53 : label
        })`,
      });
      assert.throws(() => exactly(k, 'a'), /atMost requires k to be a non-negative safe integer/);
    }
    // A non-numeric k is rejected even when the caller lies about the type.
    assert.throws(
      () => atMost('1' as unknown as number, 'a'),
      /atMost requires k to be a non-negative safe integer/,
    );
  });

  it('collect variables from cardinality operands (folded-away names included)', () => {
    assert.deepStrictEqual(
      [...getVariables(and(atMost(2, 'a', or('b', 'c')), atLeast(1, not('d'), 'e')))].sort(),
      ['a', 'b', 'c', 'd', 'e'],
    );
    // Collection runs before folding: atMost(5, 'a', 'b') folds to true but
    // both names stay in the universe.
    assert.deepStrictEqual([...getVariables(atMost(5, 'a', 'b'))].sort(), ['a', 'b']);
    // Multiplicity is a compile-time concern; the variable SET deduplicates.
    assert.deepStrictEqual([...getVariables(exactly(1, 'a', 'a'))], ['a']);
  });
});

// ---------------------------------------------------------------------------
// Compile-time validation of hand-built ASTs
// ---------------------------------------------------------------------------

describe('cardinality compile-time AST validation', () => {
  const invalidNodes: Array<[string, unknown, RegExp]> = [
    [
      'atMost with a negative k',
      { atMost: { k: -1, exprs: ['a'] } },
      /k must be a non-negative safe integer/,
    ],
    [
      'atLeast with a fractional k',
      { atLeast: { k: 1.5, exprs: ['a'] } },
      /k must be a non-negative safe integer/,
    ],
    [
      'atMost with k beyond MAX_SAFE_INTEGER',
      { atMost: { k: 2 ** 53, exprs: ['a'] } },
      /k must be a non-negative safe integer/,
    ],
    [
      'atLeast with a string k',
      { atLeast: { k: '1', exprs: ['a'] } },
      /k must be a non-negative safe integer/,
    ],
    [
      'atMost with k missing',
      { atMost: { exprs: ['a'] } },
      /k must be a non-negative safe integer/,
    ],
    ['atLeast with exprs missing', { atLeast: { k: 1 } }, /exprs must be an array/],
    ['atMost with non-array exprs', { atMost: { k: 1, exprs: 'a' } }, /exprs must be an array/],
    ['atMost with a scalar payload', { atMost: 1 }, /expected a { k, exprs } payload object/],
    ['atLeast with a null payload', { atLeast: null }, /expected a { k, exprs } payload object/],
    ['atMost with an array payload', { atMost: ['a'] }, /expected a { k, exprs } payload object/],
    [
      'an invalid cardinality operand',
      { atLeast: { k: 1, exprs: ['a', 7] } },
      /invalid BooleanExpr at \$\.atLeast\.exprs\[1\]/,
    ],
    [
      'multiple operator keys',
      { atMost: { k: 1, exprs: ['a'] }, or: ['b'] },
      /exactly one of 'and', 'or', 'not', 'atMost', 'atLeast'/,
    ],
    [
      'a nested invalid node',
      { or: ['a', { atMost: { k: -2, exprs: [] } }] },
      /invalid BooleanExpr at \$\.or\[1\]\.atMost: k/,
    ],
  ];

  it('rejects every malformed hand-built node with a descriptive Error', () => {
    for (const [label, node, message] of invalidNodes) {
      assert.throws(() => compile(node as BooleanExpr), { name: 'Error', message }, label);
    }
  });

  it('rejects a cyclic graph through a cardinality payload', () => {
    const cyclic: { atLeast: { k: number; exprs: unknown[] } } = { atLeast: { k: 1, exprs: [] } };
    cyclic.atLeast.exprs.push(cyclic, 'a');
    assert.throws(() => compile(cyclic as BooleanExpr), /cyclic expression graph/);
  });

  it('compiles a valid hand-built node identically to the constructor output', () => {
    const handBuilt = compile({ atMost: { k: 1, exprs: ['a', 'b', 'c'] } } as BooleanExpr);
    const constructed = compile(atMostOne('a', 'b', 'c'));
    assert.strictEqual(handBuilt.numVars, constructed.numVars);
    assert.deepStrictEqual(
      handBuilt.clauses.map((clause) => clause.lits),
      constructed.clauses.map((clause) => clause.lits),
    );
  });
});

// ---------------------------------------------------------------------------
// Structural carve-outs (node-based dispatch, sanctioned counts)
// ---------------------------------------------------------------------------

describe('cardinality structural carve-outs', () => {
  it('atMostOne over 3 variables compiles to exactly 3 binary clauses and no auxiliaries', () => {
    const cnf = compile(atMostOne('a', 'b', 'c'));
    assert.strictEqual(cnf.numNamedVars, 3);
    assert.strictEqual(cnf.numVars, 3, 'pairwise encoding: no auxiliaries');
    assert.strictEqual(cnf.clauses.length, 3, 'exactly one clause per operand pair');
    for (const clause of cnf.clauses) {
      assert.strictEqual(clause.lits.length, 2, 'every pairwise clause is binary');
    }
    assert.deepStrictEqual(
      clauseSet(cnf),
      new Set([
        [negLit(indexOf(cnf, 'a')), negLit(indexOf(cnf, 'b'))].sort((x, y) => x - y).join(','),
        [negLit(indexOf(cnf, 'a')), negLit(indexOf(cnf, 'c'))].sort((x, y) => x - y).join(','),
        [negLit(indexOf(cnf, 'b')), negLit(indexOf(cnf, 'c'))].sort((x, y) => x - y).join(','),
      ]),
    );
  });

  it('dispatches on the node, not the constructor: atMost(1, …) ≡ atMostOne(…)', () => {
    const sugar = compile(atMostOne('a', 'b', 'c'));
    const direct = compile(atMost(1, 'a', 'b', 'c'));
    assert.strictEqual(direct.numVars, sugar.numVars);
    assert.deepStrictEqual(clauseSet(direct), clauseSet(sugar));
  });

  it('uses the pairwise encoding at the n = 6 boundary and the sequential counter at n = 7', () => {
    const six = compile(atMost(1, 'a', 'b', 'c', 'd', 'e', 'f'));
    assert.strictEqual(six.numVars, 6, 'pairwise still needs no auxiliaries at n = 6');
    assert.strictEqual(six.clauses.length, 15, 'C(6, 2) binary clauses');
    for (const clause of six.clauses) {
      assert.strictEqual(clause.lits.length, 2);
    }
    const seven = compile(atMost(1, 'a', 'b', 'c', 'd', 'e', 'f', 'g'));
    assert.ok(seven.numVars > 7, 'the sequential counter allocates auxiliaries at n = 7');
  });

  it('asserts a repeated conjunct once: no duplicated counter auxiliaries', () => {
    // and-flattening preserves multiplicity, so the interned atMost node
    // appears twice as a conjunct; the second assertion is a no-op.
    const cnf = compile(and(atMost(1, 'a', 'b'), atMost(1, 'a', 'b')));
    assert.strictEqual(cnf.numVars, 2);
    assert.deepStrictEqual(
      cnf.clauses.map((clause) => clause.lits),
      [[negLit(indexOf(cnf, 'a')), negLit(indexOf(cnf, 'b'))].sort((x, y) => x - y)],
    );
  });

  it('reifies compound conjunctive operands through an ordinary gate first', () => {
    // atMost(1, and('a','b'), 'c'): the and-gate is fully reified, then the
    // pairwise clause constrains the gate literal against c.
    const cnf = compile(atMost(1, and('a', 'b'), 'c'));
    assert.strictEqual(cnf.numNamedVars, 3);
    assert.strictEqual(cnf.numVars, 4, 'exactly one gate auxiliary');
    const gate = posLit(3);
    assert.ok(
      clauseSet(cnf).has([neg(gate), negLit(indexOf(cnf, 'c'))].sort((x, y) => x - y).join(',')),
      'the pairwise clause mentions the gate literal',
    );
    assertSolverAgreement(atMost(1, and('a', 'b'), 'c'));
  });
});

// ---------------------------------------------------------------------------
// Edge folds and the preserved named universe
// ---------------------------------------------------------------------------

describe('cardinality edge folds', () => {
  it('atMost(k >= n, …) folds to true and keeps the universe', () => {
    for (const expr of [atMost(2, 'a', 'b'), atMost(5, 'a', 'b')]) {
      const cnf = compile(expr);
      assert.strictEqual(cnf.clauses.length, 0, 'no clauses');
      assert.strictEqual(cnf.numVars, 2, 'no auxiliaries');
      assert.deepStrictEqual(cnf.indexToName, ['a', 'b'], 'folded-away names stay in the universe');
      assert.strictEqual(cnf.levelZeroUnsat, false);
      // Complete two-variable models survive the fold.
      assert.strictEqual(expectCompleteModels(getAllSolutions(expr)).length, 4);
    }
  });

  it('atLeast(0, …) folds to true; atLeast(k > n, …) folds to false without dropping the universe', () => {
    const tautology = compile(atLeast(0, 'a', 'b'));
    assert.strictEqual(tautology.clauses.length, 0);
    assert.deepStrictEqual(tautology.indexToName, ['a', 'b']);
    assert.strictEqual(expectCompleteModels(getAllSolutions(atLeast(0, 'a', 'b'))).length, 4);

    const contradiction = compile(atLeast(3, 'a', 'b'));
    assert.strictEqual(contradiction.levelZeroUnsat, true);
    assert.deepStrictEqual(contradiction.indexToName, ['a', 'b']);
    assert.deepStrictEqual(
      contradiction.clauses.map((clause) => clause.lits),
      [[]],
    );
    assert.deepStrictEqual(getSolution(atLeast(3, 'a', 'b')), { status: 'unsat', core: {} });
    assert.deepStrictEqual(getAllSolutions(atLeast(3, 'a', 'b')), {
      status: 'complete',
      models: [],
    });
  });

  it('atMost(0, …) asserts every input false', () => {
    const cnf = compile(atMost(0, 'a', 'b'));
    assert.deepStrictEqual(
      cnf.clauses.map((clause) => clause.lits),
      [[negLit(indexOf(cnf, 'a'))], [negLit(indexOf(cnf, 'b'))]],
    );
    assert.strictEqual(cnf.numVars, 2, 'no auxiliaries');
    assertModelListsEqual(expectCompleteModels(getAllSolutions(atMost(0, 'a', 'b'))), [
      { a: Value.FALSE, b: Value.FALSE },
    ]);
    // A single surviving operand collapses to its negation; zero operands
    // fold to true.
    assertModelListsEqual(expectCompleteModels(getAllSolutions(atMost(0, 'a'))), [
      { a: Value.FALSE },
    ]);
    assert.deepStrictEqual(getSolution(atMost(0)), { status: 'sat', model: {} });
  });

  it('folds empty operand lists: atMost(k) true, atLeast(0) true, atLeast(k >= 1) false', () => {
    assert.deepStrictEqual(getSolution(atMost(1)), { status: 'sat', model: {} });
    assert.deepStrictEqual(getSolution(atLeast(0)), { status: 'sat', model: {} });
    assert.deepStrictEqual(getSolution(atLeast(1)), { status: 'unsat', core: {} });
    assert.deepStrictEqual(getSolution(exactly(0)), { status: 'sat', model: {} });
    assert.deepStrictEqual(getSolution(exactly(1)), { status: 'unsat', core: {} });
  });

  it('folds constant operands totally: true decrements the bound, false drops out', () => {
    // atMost(1, 'a', true): the constant consumes the bound → 'a' must be false.
    const shrunk = compile(atMost(1, 'a', and()));
    assert.deepStrictEqual(
      shrunk.clauses.map((clause) => clause.lits),
      [[negLit(indexOf(shrunk, 'a'))]],
    );
    assert.deepStrictEqual(shrunk.indexToName, ['a']);
    // atLeast(1, 'a', true): the constant satisfies the bound → tautology.
    const satisfied = compile(atLeast(1, 'a', and()));
    assert.strictEqual(satisfied.clauses.length, 0);
    assert.deepStrictEqual(satisfied.indexToName, ['a']);
    assert.strictEqual(expectCompleteModels(getAllSolutions(atLeast(1, 'a', and()))).length, 2);
    // atLeast(2, 'a', false): impossible → root-false fold, universe kept.
    const impossible = compile(atLeast(2, 'a', or()));
    assert.strictEqual(impossible.levelZeroUnsat, true);
    assert.deepStrictEqual(impossible.indexToName, ['a']);
    // atMost(0, true): the constant alone exceeds the bound → false.
    assert.strictEqual(compile(atMost(0, and())).levelZeroUnsat, true);
    // exactly(1, 'a', true) ⇔ not('a').
    assertModelListsEqual(expectCompleteModels(getAllSolutions(exactly(1, 'a', and()))), [
      { a: Value.FALSE },
    ]);
  });
});

// ---------------------------------------------------------------------------
// Multiplicity semantics: operands are a multiset
// ---------------------------------------------------------------------------

describe('cardinality multiplicity semantics', () => {
  it("exactly(1, 'a', 'a') is UNSAT: two occurrences of a true 'a' exceed the bound", () => {
    // atMost(1, 'a', 'a') forces 'a' false; atLeast(1, 'a', 'a') then fails.
    assert.deepStrictEqual(getSolution(exactly(1, 'a', 'a')), { status: 'unsat', core: {} });
    assert.deepStrictEqual(getAllSolutions(exactly(1, 'a', 'a')), {
      status: 'complete',
      models: [],
    });
  });

  it("atMost(1, 'a', 'a') forces 'a' false through the pairwise self-pair", () => {
    // The (a, a) pair yields (¬a ∨ ¬a), normalized to the unit ¬a.
    const cnf = compile(atMost(1, 'a', 'a'));
    assert.deepStrictEqual(
      cnf.clauses.map((clause) => clause.lits),
      [[negLit(indexOf(cnf, 'a'))]],
    );
    assertModelListsEqual(expectCompleteModels(getAllSolutions(atMost(1, 'a', 'a'))), [
      { a: Value.FALSE },
    ]);
  });

  it("atLeast(2, 'a', 'a') forces 'a' true", () => {
    assertModelListsEqual(expectCompleteModels(getAllSolutions(atLeast(2, 'a', 'a'))), [
      { a: Value.TRUE },
    ]);
  });

  it("atMost(2, 'a', 'b') still enumerates all four named models", () => {
    const models = expectCompleteModels(getAllSolutions(atMost(2, 'a', 'b')));
    assert.strictEqual(models.length, 4);
    assertModelListsEqual(models, referenceModels(or('a', not('a'), 'b', not('b'))));
  });

  it("exactly(2, 'a', 'a', 'b') counts 'a' twice", () => {
    // a=T,b=F counts two; every other valuation misses the bound.
    assertModelListsEqual(expectCompleteModels(getAllSolutions(exactly(2, 'a', 'a', 'b'))), [
      { a: Value.TRUE, b: Value.FALSE },
    ]);
  });

  it("preserves multiplicity inside nested positions: or(atMost(1, 'a', 'a'), 'b')", () => {
    // atMost(1,'a','a') ≡ ¬a, so the models are ¬a∨b: 3 of 4 valuations.
    assertModelListsEqual(expectCompleteModels(getAllSolutions(or(atMost(1, 'a', 'a'), 'b'))), [
      { a: Value.FALSE, b: Value.FALSE },
      { a: Value.FALSE, b: Value.TRUE },
      { a: Value.TRUE, b: Value.TRUE },
    ]);
  });
});

// ---------------------------------------------------------------------------
// Asserted-counter oracles: extension correctness + propagation refutation
// ---------------------------------------------------------------------------

// One row per asserted-encoding case; `encoding` pins the dispatch class
// structurally (pairwise/units: no COUNTER auxiliaries; sinz: counter
// auxiliaries present). `gateAux` accounts for auxiliaries that reify
// compound operands before the counter encoding runs.
const ASSERTED_CASES: ReadonlyArray<
  readonly [string, BooleanExpr, 'pairwise' | 'sinz' | 'units', number?]
> = [
  ['pairwise AMO n=3', atMostOne('a', 'b', 'c'), 'pairwise'],
  ['pairwise AMO boundary n=6', atMost(1, 'a', 'b', 'c', 'd', 'e', 'f'), 'pairwise'],
  ['Sinz AMO n=7', atMost(1, 'a', 'b', 'c', 'd', 'e', 'f', 'g'), 'sinz'],
  ['Sinz atMost(2) n=5', atMost(2, 'a', 'b', 'c', 'd', 'e'), 'sinz'],
  ['Sinz atMost(3) n=5', atMost(3, 'a', 'b', 'c', 'd', 'e'), 'sinz'],
  ['atLeast(2) n=3 rewrites to pairwise', atLeast(2, 'a', 'b', 'c'), 'pairwise'],
  ['atLeast(1) n=3 rewrites to Sinz', atLeast(1, 'a', 'b', 'c'), 'sinz'],
  ['atLeast(2) n=5 rewrites to Sinz', atLeast(2, 'a', 'b', 'c', 'd', 'e'), 'sinz'],
  ['atLeast(5) n=5 rewrites to units', atLeast(5, 'a', 'b', 'c', 'd', 'e'), 'units'],
  ['exactly(2) n=4', exactly(2, 'a', 'b', 'c', 'd'), 'sinz'],
  ['compound operand', atMost(1, and('a', 'b'), 'c'), 'pairwise', 1],
  ['multiplicity pair', atMost(1, 'a', 'a'), 'pairwise'],
];

describe('asserted cardinality counter oracles', () => {
  for (const [label, expr, encoding, gateAux = 0] of ASSERTED_CASES) {
    it(`${label}: extension for every valid valuation, refutation of every violating one`, () => {
      const cnf = compile(expr);
      assert.strictEqual(cnf.levelZeroUnsat, false, `${label}: fixture is not trivially UNSAT`);
      const variableCount = cnf.numNamedVars;
      if (encoding === 'pairwise' || encoding === 'units') {
        assert.strictEqual(
          cnf.numVars,
          variableCount + gateAux,
          `${label}: no counter auxiliaries`,
        );
      } else {
        assert.ok(cnf.numVars > variableCount + gateAux, `${label}: counter auxiliaries`);
      }
      const names = [...getVariables(expr)];
      assert.strictEqual(names.length, variableCount);
      let valid = 0;
      let violated = 0;
      for (const assignment of enumerateAssignments(names)) {
        const reference = expressionValue(expr, assignment) === Value.TRUE;
        if (reference) {
          // Extension correctness: some auxiliary extension satisfies every
          // clause. Propagation alone is NOT required to find it.
          assert.ok(
            hasSatisfyingExtension(cnf, assignment),
            `${label}: valid valuation ${JSON.stringify(assignment)} has a satisfying extension`,
          );
          valid += 1;
        } else {
          // Propagation refutation: unit propagation from the total named
          // assignment falsifies a clause, with no auxiliary decided.
          assert.ok(
            propagationRefutes(cnf, assignment),
            `${label}: violating valuation ${JSON.stringify(assignment)} is propagation-refuted`,
          );
          violated += 1;
        }
      }
      assert.strictEqual(valid + violated, 2 ** variableCount);
      assert.ok(violated > 0, `${label}: the case genuinely constrains`);
    });
  }

  it('seven-input Sinz AMO with all inputs false: valid with every counter auxiliary unset', () => {
    const expr = atMost(1, 'a', 'b', 'c', 'd', 'e', 'f', 'g');
    const cnf = compile(expr);
    assert.strictEqual(cnf.numNamedVars, 7);
    const allFalse: VariableAssignments = Object.fromEntries(
      ['a', 'b', 'c', 'd', 'e', 'f', 'g'].map((name) => [name, Value.FALSE]),
    );
    assert.strictEqual(expressionValue(expr, allFalse), Value.TRUE, 'all-false is valid');
    const { assigns, conflict } = propagateCnf(cnf, allFalse);
    assert.strictEqual(conflict, false, 'not propagation-refuted');
    // The weaker asserted-counter contract, pinned: propagation decides
    // NOTHING beyond the named inputs, yet a satisfying extension exists.
    const auxiliaries = [...assigns.slice(cnf.numNamedVars)];
    assert.ok(auxiliaries.length > 0, 'the counter has auxiliaries');
    assert.ok(
      auxiliaries.every((value) => value === Value.UNSET),
      'no counter auxiliary is derived by propagation',
    );
    assert.ok(hasSatisfyingExtension(cnf, allFalse), 'a satisfying extension exists');
    // And the solver accepts the valuation without deciding auxiliaries.
    const model = expectSatModel(getSolution(expr, { assumptions: allFalse }));
    assert.deepStrictEqual(model, allFalse);
  });
});

// ---------------------------------------------------------------------------
// Nested thresholds: fully reified in both polarities
// ---------------------------------------------------------------------------

// Nested-only formulas: no conjunctive cardinality, so propagation from a
// total named assignment must derive EVERY variable (gates and totalizer
// outputs alike) and satisfy every clause exactly when the reference accepts.
const NESTED_CASES: ReadonlyArray<readonly [string, BooleanExpr]> = [
  ['atLeast(2) under or', or(atLeast(2, 'a', 'b', 'c'), 'd')],
  ['atLeast(2) negated under or', or(not(atLeast(2, 'a', 'b', 'c')), 'd')],
  ['atMost(1) under or', or(atMost(1, 'a', 'b', 'c'), 'd')],
  ['atMost(1) negated under or', or(not(atMost(1, 'a', 'b', 'c')), 'd')],
  ['atLeast(2) over 4 under or', or(atLeast(2, 'a', 'b', 'c', 'd'), 'e')],
  ['atMost(2) over 4 negated under or', or(not(atMost(2, 'a', 'b', 'c', 'd')), 'e')],
  ['atLeast(3) over 4 under or', or(atLeast(3, 'a', 'b', 'c', 'd'), 'e')],
  ['xor over a nested atLeast', xor(atLeast(1, 'a', 'b'), 'c')],
  ['a compound operand reified first', or(atLeast(1, and('a', 'b'), 'c'), 'd')],
  ['a cardinality operand reified first', or(atMost(1, atLeast(1, 'a', 'b'), 'c'), 'd')],
  [
    'conjoined nested occurrences',
    and(or(atLeast(2, 'a', 'b', 'c'), 'd'), or(atMost(1, 'a', 'b'), 'e')),
  ],
  [
    'one shared node in both polarities',
    (() => {
      const shared = atLeast(1, 'a', 'b');
      return and(or(shared, 'c'), or(not(shared), 'd'));
    })(),
  ],
  ['implies over nested thresholds', implies(atLeast(2, 'a', 'b', 'c'), atMost(1, 'd', 'e'))],
];

describe('nested cardinality totalizer reification', () => {
  for (const [label, expr] of NESTED_CASES) {
    it(`${label}: propagation derives every auxiliary; clauses agree with the reference`, () => {
      const cnf = compile(expr);
      const names = [...getVariables(expr)];
      for (const assignment of enumerateAssignments(names)) {
        const reference = expressionValue(expr, assignment) === Value.TRUE;
        const { assigns, conflict } = propagateCnf(cnf, assignment);
        assert.strictEqual(
          conflict,
          !reference,
          `${label}: ${JSON.stringify(assignment)} propagation verdict`,
        );
        if (reference) {
          // Full reification in both polarities: propagation derives a
          // COMPLETE assignment (no undecided auxiliary) that satisfies every
          // clause — the full-gate oracle of compile.spec.ts applies.
          assert.ok(
            [...assigns].every((value) => value !== Value.UNSET),
            `${label}: every variable derived under ${JSON.stringify(assignment)}`,
          );
          assert.ok(
            cnf.clauses.every((clause) =>
              clause.lits.some((lit) => litValue(lit, assigns) === Value.TRUE),
            ),
            `${label}: every clause satisfied under ${JSON.stringify(assignment)}`,
          );
        }
      }
      assertSolverAgreement(expr);
    });
  }

  it('nested thresholds propagate under assumptions in both polarities', () => {
    // d=false, a=false, b=false leave atLeast(2) unachievable and d unusable.
    const positive = or(atLeast(2, 'a', 'b', 'c'), 'd');
    assert.strictEqual(
      getSolution(positive, { assumptions: { a: Value.FALSE, b: Value.FALSE, d: Value.FALSE } })
        .status,
      'unsat',
    );
    // Negated: a=true, b=true make atLeast(2) true, so not(...) is false and
    // d=false closes the disjunction.
    const negative = or(not(atLeast(2, 'a', 'b', 'c')), 'd');
    assert.strictEqual(
      getSolution(negative, { assumptions: { a: Value.TRUE, b: Value.TRUE, d: Value.FALSE } })
        .status,
      'unsat',
    );
    // Each is satisfiable when its pressure is lifted.
    assert.strictEqual(getSolution(positive, { assumptions: { d: Value.FALSE } }).status, 'sat');
    assert.strictEqual(getSolution(negative, { assumptions: { d: Value.FALSE } }).status, 'sat');
  });

  it('enumeration under assumptions matches the reference extension count', () => {
    const expr = or(atLeast(2, 'a', 'b', 'c'), 'd');
    const reference = referenceModels(expr);
    const partial = { a: Value.TRUE };
    const expected = reference.filter((model) => model.a === Value.TRUE);
    assert.ok(expected.length > 0 && expected.length < reference.length);
    assertModelListsEqual(
      expectCompleteModels(getAllSolutions(expr, { assumptions: partial })),
      expected,
    );
  });
});

// ---------------------------------------------------------------------------
// Solver-level agreement on mixed conjunctive/nested formulas
// ---------------------------------------------------------------------------

describe('cardinality solver agreement corpus', () => {
  const corpus: ReadonlyArray<readonly [string, BooleanExpr]> = [
    [
      'Sinz AMO with a side condition',
      and(atMost(1, 'a', 'b', 'c', 'd', 'e', 'f', 'g'), or('b', 'c')),
    ],
    ['exactly(2) with a xor', and(exactly(2, 'a', 'b', 'c', 'd'), xor('e', 'f'))],
    ['atLeast conjunctive over 5', and(atLeast(3, 'a', 'b', 'c', 'd', 'e'), or('f', 'g'))],
    ['atMost and atLeast band', and(atLeast(2, 'a', 'b', 'c', 'd'), atMost(3, 'a', 'b', 'c', 'd'))],
    ['compound operands on both sides', and(atMost(1, and('a', 'b'), 'c'), atLeast(1, 'd', 'e'))],
    [
      'nested under a conjunctive sibling',
      and(or(atLeast(2, 'a', 'b', 'c'), 'd'), atMost(1, 'd', 'e')),
    ],
    ['atMostOne with an implication', and(atMostOne('a', 'b', 'c'), implies('a', 'd'))],
    ['negated nested exactly', or(not(and(atMost(1, 'a', 'b'), atLeast(1, 'a', 'b'))), 'c')],
  ];
  for (const [label, expr] of corpus) {
    it(`agrees with the reference enumerator: ${label}`, () => {
      assertSolverAgreement(expr);
    });
  }

  it('produces a complete model with every named variable on a folded/mixed formula', () => {
    // atMost(9, …) folds away, but 'e' and 'f' stay in the universe and in
    // every returned model.
    const expr = and(atLeast(2, 'a', 'b', 'c'), atMost(9, 'e', 'f'));
    const model = expectSatModel(getSolution(expr));
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE);
    const models = expectCompleteModels(getAllSolutions(expr));
    assert.strictEqual(
      models.length,
      4 * 4,
      'C(3,2)+C(3,3) = 4 assignments times 4 free valuations',
    );
    for (const each of models) {
      assertModelShape(each, expr);
    }
  });
});
