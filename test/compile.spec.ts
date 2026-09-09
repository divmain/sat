// Unit and property tests for the Tseitin compiler (src/compile.ts).
//
// Structural assertions are confined to the documented carve-outs (zero-aux
// and single-plain-clause outcomes on hash-consing-free inputs) plus the
// normalization edge cases; everything else is validated semantically: CNF
// satisfiability under every one of the 2^k named assignments — with aux
// values derived by unit propagation (gate evaluation) — must agree with the
// reference evaluator.
//
// Test files import internal modules via extensionless paths: tsx resolves
// them, and tsc never compiles test/.

import assert from 'node:assert';
import { describe, it } from 'node:test';
import { and, getVariables, implies, not, or, Value, xor } from '../src/expr';
import type { BooleanExpr, Variable, VariableAssignments } from '../src/expr';
import {
  compile,
  isNeg,
  litValue,
  neg,
  negLit,
  normalizeClauseLits,
  posLit,
  varOf,
} from '../src/compile';
import type { Clause, CompiledCnf } from '../src/compile';
import { enumerateAssignments, expressionValue, mulberry32, randomFormula } from './helpers';

// ---------------------------------------------------------------------------
// Shared spec utilities
// ---------------------------------------------------------------------------

const clauseKey = (clause: Clause): string => clause.lits.join(',');

// Look up a named variable's index, failing loudly if absent.
function indexOf(cnf: CompiledCnf, name: Variable): number {
  const index = cnf.nameToIndex.get(name);
  if (index === undefined) {
    throw new Error(`missing named variable: ${name}`);
  }
  return index;
}

// Structural invariants that must hold for every compiled formula: named/aux
// index separation, normalized (sorted, deduplicated, non-tautological,
// unique, in-range) clauses, and agreement between levelZeroUnsat and the
// presence of the empty clause.
function assertWellFormed(cnf: CompiledCnf): void {
  // Named/aux index separation: named variables occupy 0..numNamedVars-1 and
  // aux variables (if any) occupy numNamedVars..numVars-1.
  assert.strictEqual(cnf.indexToName.length, cnf.numNamedVars);
  assert.strictEqual(cnf.nameToIndex.size, cnf.numNamedVars);
  assert.ok(cnf.numVars >= cnf.numNamedVars, 'aux indices come after named indices');
  for (let index = 0; index < cnf.numNamedVars; index += 1) {
    assert.strictEqual(cnf.nameToIndex.get(cnf.indexToName[index]), index);
  }
  for (const index of cnf.nameToIndex.values()) {
    assert.ok(index >= 0 && index < cnf.numNamedVars, 'named index within the named range');
  }

  const keys = new Set<string>();
  let hasEmptyClause = false;
  for (const clause of cnf.clauses) {
    assert.strictEqual(clause.learned, false, 'compiled clauses are never marked learned');

    const sorted = [...clause.lits].sort((a, b) => a - b);
    assert.deepEqual(clause.lits, sorted, 'clause literals are sorted');
    const litSet = new Set(clause.lits);
    assert.strictEqual(litSet.size, clause.lits.length, 'clause literals are deduplicated');
    for (const lit of clause.lits) {
      assert.ok(!litSet.has(neg(lit)), 'no tautological clauses');
      assert.ok(varOf(lit) >= 0 && varOf(lit) < cnf.numVars, 'literal variable in range');
    }

    const key = clauseKey(clause);
    assert.ok(!keys.has(key), 'no duplicate clauses');
    keys.add(key);
    if (clause.lits.length === 0) {
      hasEmptyClause = true;
    }
  }
  assert.strictEqual(
    cnf.levelZeroUnsat,
    hasEmptyClause,
    'levelZeroUnsat exactly when the empty clause is present',
  );
}

// Is the CNF satisfied when the named variables are fixed to `named`? Unit
// propagation to fixpoint derives every aux value by gate evaluation: each
// gate's clauses become unit once its inputs are assigned, so a clause left
// unsatisfied at fixpoint means no extension of `named` satisfies the CNF.
function cnfSatisfiedUnder(cnf: CompiledCnf, named: VariableAssignments): boolean {
  const assigns = new Int8Array(cnf.numVars).fill(Value.UNSET);
  for (const [name, value] of Object.entries(named)) {
    assigns[indexOf(cnf, name)] = value;
  }

  let changed = true;
  while (changed) {
    changed = false;
    for (const clause of cnf.clauses) {
      let unit: number | null = null;
      let unassignedCount = 0;
      let satisfied = false;
      for (const lit of clause.lits) {
        const value = litValue(lit, assigns);
        if (value === Value.TRUE) {
          satisfied = true;
          break;
        }
        if (value === Value.UNSET) {
          unassignedCount += 1;
          unit = lit;
        }
      }
      if (!satisfied && unassignedCount === 1 && unit !== null) {
        assigns[varOf(unit)] = isNeg(unit) ? Value.FALSE : Value.TRUE;
        changed = true;
      }
    }
  }

  return cnf.clauses.every((clause) =>
    clause.lits.some((lit) => litValue(lit, assigns) === Value.TRUE),
  );
}

// CNF satisfiability must agree with the reference evaluator under every
// assignment of the named variables.
function assertAgreement(expr: BooleanExpr): void {
  const cnf = compile(expr);
  assertWellFormed(cnf);
  for (const assignment of enumerateAssignments([...getVariables(expr)])) {
    const reference = expressionValue(expr, assignment) === Value.TRUE;
    assert.strictEqual(
      cnfSatisfiedUnder(cnf, assignment),
      reference,
      `CNF/reference disagree under ${JSON.stringify(assignment)}`,
    );
  }
}

// ---------------------------------------------------------------------------
// Literal helpers
// ---------------------------------------------------------------------------

describe('literal helpers', () => {
  it('round-trip variables and polarities', () => {
    for (const v of [0, 1, 2, 17, 1000]) {
      assert.strictEqual(varOf(posLit(v)), v);
      assert.strictEqual(varOf(negLit(v)), v);
      assert.strictEqual(isNeg(posLit(v)), false);
      assert.strictEqual(isNeg(negLit(v)), true);
      assert.strictEqual(neg(posLit(v)), negLit(v));
      assert.strictEqual(neg(negLit(v)), posLit(v));
      assert.strictEqual(neg(neg(posLit(v))), posLit(v));
    }
  });

  it('litValue is three-valued against the assignment array', () => {
    const assigns = new Int8Array([Value.UNSET, Value.FALSE, Value.TRUE]);
    assert.strictEqual(litValue(posLit(0), assigns), Value.UNSET);
    assert.strictEqual(litValue(negLit(0), assigns), Value.UNSET);
    assert.strictEqual(litValue(posLit(1), assigns), Value.FALSE);
    assert.strictEqual(litValue(negLit(1), assigns), Value.TRUE);
    assert.strictEqual(litValue(posLit(2), assigns), Value.TRUE);
    assert.strictEqual(litValue(negLit(2), assigns), Value.FALSE);
  });
});

// ---------------------------------------------------------------------------
// Clause normalization
// ---------------------------------------------------------------------------

describe('normalizeClauseLits', () => {
  it('sorts and deduplicates literals', () => {
    assert.deepEqual(normalizeClauseLits([5, 2, 5, 0]), [0, 2, 5]);
  });

  it('drops tautologies (returns null)', () => {
    assert.strictEqual(normalizeClauseLits([posLit(1), negLit(1), posLit(2)]), null);
    assert.strictEqual(normalizeClauseLits([negLit(3), posLit(3)]), null);
  });

  it('keeps the empty clause', () => {
    assert.deepEqual(normalizeClauseLits([]), []);
  });
});

// ---------------------------------------------------------------------------
// Structural carve-outs
// ---------------------------------------------------------------------------

describe('compile — structural assertions (sanctioned carve-outs)', () => {
  it("implies('b','a') compiles to exactly one plain binary clause", () => {
    const cnf = compile(implies('b', 'a'));
    assertWellFormed(cnf);
    assert.strictEqual(cnf.numNamedVars, 2);
    assert.strictEqual(cnf.numVars, 2, 'no aux variables');
    assert.strictEqual(cnf.clauses.length, 1, 'exactly one clause');
    assert.deepEqual(cnf.clauses[0].lits, [posLit(indexOf(cnf, 'a')), negLit(indexOf(cnf, 'b'))]);
  });

  it('a hypergraph of binary implies compiles with zero aux variables', () => {
    // The 18-prereq hypergraph instance from the v1 spec: each pair
    // [target, prereq] means `implies(target, prereq)` = (¬target ∨ prereq).
    const nodePrereqs: Array<[Variable, Variable]> = [
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
    const cnf = compile(and(...nodePrereqs.map(([target, prereq]) => implies(target, prereq))));
    assertWellFormed(cnf);
    assert.strictEqual(cnf.numNamedVars, 19);
    assert.strictEqual(cnf.numVars, 19, 'no aux variables');
    const expected = new Set(
      nodePrereqs.map(([target, prereq]) =>
        [negLit(indexOf(cnf, target)), posLit(indexOf(cnf, prereq))]
          .sort((a, b) => a - b)
          .join(','),
      ),
    );
    const actual = new Set(cnf.clauses.map(clauseKey));
    assert.deepEqual(actual, expected, 'each implies compiles to its plain binary clause');
    for (const clause of cnf.clauses) {
      assert.strictEqual(clause.lits.length, 2, 'every clause is binary');
    }
  });
});

// ---------------------------------------------------------------------------
// Normalization edge cases
// ---------------------------------------------------------------------------

describe('compile — normalization edge cases', () => {
  it("or('a', not('a')) drops the tautological plain clause", () => {
    const cnf = compile(or('a', not('a')));
    assertWellFormed(cnf);
    assert.strictEqual(cnf.clauses.length, 0);
    assert.strictEqual(cnf.levelZeroUnsat, false);
    assert.strictEqual(cnf.numNamedVars, 1);
    assert.strictEqual(cnf.numVars, 1, 'no aux variables');
  });

  it("and('a', 'a') drops the duplicate unit clause", () => {
    const cnf = compile(and('a', 'a'));
    assertWellFormed(cnf);
    assert.strictEqual(cnf.clauses.length, 1);
    assert.deepEqual(cnf.clauses[0].lits, [posLit(indexOf(cnf, 'a'))]);
  });

  it('and() compiles to the trivially satisfiable empty CNF', () => {
    const cnf = compile(and());
    assertWellFormed(cnf);
    assert.strictEqual(cnf.numVars, 0);
    assert.strictEqual(cnf.numNamedVars, 0);
    assert.strictEqual(cnf.clauses.length, 0);
    assert.strictEqual(cnf.levelZeroUnsat, false);
  });

  it('or() compiles to the empty clause (UNSAT before search)', () => {
    const cnf = compile(or());
    assertWellFormed(cnf);
    assert.strictEqual(cnf.levelZeroUnsat, true);
    assert.strictEqual(cnf.clauses.length, 1);
    assert.deepEqual(cnf.clauses[0].lits, []);
  });
});

// ---------------------------------------------------------------------------
// Sharing, flattening, and folding
// ---------------------------------------------------------------------------

// Compact structural snapshot of a CompiledCnf for handle-immutability and
// mutation-observation assertions (not the benchmark canonical form).
const cnfSnapshot = (cnf: CompiledCnf): string =>
  JSON.stringify({
    numVars: cnf.numVars,
    numNamedVars: cnf.numNamedVars,
    indexToName: cnf.indexToName,
    clauses: cnf.clauses.map((clause) => clause.lits),
    levelZeroUnsat: cnf.levelZeroUnsat,
  });

describe('compile — sharing, flattening, and folding', () => {
  it('compiles a left-deep xor chain with linearly bounded size (shared subtrees visited once)', () => {
    // xor(x, y) = or(and(x, not(y)), and(not(x), y)) duplicates both operand
    // identities, so an unshared traversal of a left-deep chain visits
    // 3·2^(n-1)-2 leaves (and allocated exponentially many aux variables
    // before sharing landed). Identity memoization plus hash-consing visit
    // each object once: every level needs at most three gates (two and, one
    // or). Bounded shape only — never an exact aux count on consed inputs.
    const length = 12;
    const width = String(length).length;
    const nameOf = (index: number) => `v${String(index).padStart(width, '0')}`;
    let expr = xor(nameOf(1), nameOf(2));
    for (let index = 3; index <= length; index += 1) {
      expr = xor(expr, nameOf(index));
    }
    const cnf = compile(expr);
    assertWellFormed(cnf);
    assert.strictEqual(cnf.numNamedVars, length);
    assert.ok(
      cnf.numVars <= 4 * length,
      `aux population stays linear in the chain length (got ${cnf.numVars} for ${length} named)`,
    );
  });

  it('agrees with the reference evaluator on a shared xor chain over all named assignments', () => {
    const length = 8;
    const width = String(length).length;
    const nameOf = (index: number) => `v${String(index).padStart(width, '0')}`;
    let expr = xor(nameOf(1), nameOf(2));
    for (let index = 3; index <= length; index += 1) {
      expr = xor(expr, nameOf(index));
    }
    assertAgreement(expr);
  });

  it('shares one gate set across structurally identical occurrences', () => {
    // Distinct objects, identical structure: hash-consing (key = node kind +
    // ordered flattened child keys) interns them to one canonical node.
    const fresh = () => or(and('a', 'b'), 'c');
    const twice = compile(and(fresh(), fresh()));
    const fourTimes = compile(and(fresh(), fresh(), fresh(), fresh()));
    assertWellFormed(twice);
    assertWellFormed(fourTimes);
    assert.strictEqual(twice.numNamedVars, 3);
    // Repeating the occurrence four times cannot grow the gate population:
    // the shared structure is compiled once. A bound, never an exact count.
    assert.ok(
      fourTimes.numVars <= twice.numVars,
      `occurrences share gates (two: ${twice.numVars}, four: ${fourTimes.numVars})`,
    );
    assertAgreement(and(fresh(), fresh(), fresh(), fresh()));
  });

  it('preserves operand order and multiplicity in consing keys', () => {
    // or(and(a,b),c) and or(and(b,a),c) differ only in operand order; both
    // compile correctly and neither is required to share the other's gates.
    assertAgreement(or(and('a', 'b'), 'c'));
    assertAgreement(or(and('b', 'a'), 'c'));
    // Multiplicity is preserved: and('a','a') in non-conjunctive position is
    // gated like any other two-operand conjunction, not collapsed to 'a'.
    const cnf = compile(or(and('a', 'a'), 'b'));
    assertWellFormed(cnf);
    assertAgreement(or(and('a', 'a'), 'b'));
  });

  it('keeps folded-away variables in the named universe', () => {
    // or('x', and()) folds to true (the and() operand is the identity for
    // or), so the whole conjunct vanishes; 'x' still belongs to the named
    // universe and therefore to complete models.
    const cnf = compile(and(or('x', and()), 'b'));
    assertWellFormed(cnf);
    assert.deepEqual(
      cnf.indexToName,
      ['b', 'x'],
      "the folded-away 'x' stays in the named universe",
    );
    assert.strictEqual(cnf.numVars, cnf.numNamedVars, 'a folded conjunct allocates no aux');
    assert.deepEqual(
      cnf.clauses.map((clause) => clause.lits),
      [[posLit(indexOf(cnf, 'b'))]],
      'only the surviving conjunct emits a clause',
    );
    assert.strictEqual(cnf.levelZeroUnsat, false);
  });

  it('folds a false root to the empty clause without dropping the universe', () => {
    const cnf = compile(and('a', or()));
    assertWellFormed(cnf);
    assert.strictEqual(cnf.levelZeroUnsat, true);
    assert.deepEqual(cnf.indexToName, ['a'], "'a' stays in the named universe");
    assert.deepEqual(
      cnf.clauses.map((clause) => clause.lits),
      [[]],
    );
  });

  it('folds negated constants in both directions', () => {
    const contradiction = compile(and(not(and()), 'b'));
    assertWellFormed(contradiction);
    assert.strictEqual(contradiction.levelZeroUnsat, true);
    assert.deepEqual(contradiction.indexToName, ['b']);
    const tautology = compile(and(not(or()), 'b'));
    assertWellFormed(tautology);
    assert.strictEqual(tautology.levelZeroUnsat, false);
    assert.deepEqual(
      tautology.clauses.map((clause) => clause.lits),
      [[posLit(indexOf(tautology, 'b'))]],
    );
  });

  it('observes caller mutations between compilations and never alters earlier handles', () => {
    // Caches are compilation-scoped and canonical forms are compiler-owned:
    // editing a shared caller AST is observed by the NEXT compilation, while
    // previously returned handles are frozen snapshots of their own compile.
    const shared = and('a', 'b');
    if (!('and' in shared)) {
      throw new Error('and() must produce an and-node');
    }
    const expr = or(shared, 'c');
    const first = compile(expr);
    const firstSnapshot = cnfSnapshot(first);
    shared.and.push(not('c'));
    const second = compile(expr);
    assertWellFormed(second);
    assert.strictEqual(cnfSnapshot(first), firstSnapshot, 'earlier handle is unchanged');
    assert.notStrictEqual(
      cnfSnapshot(second),
      firstSnapshot,
      'the second compilation observes the edited AST',
    );
    assertAgreement(expr);
  });

  it('refutes invalid total named assignments by propagation (ordinary invalid-model regression)', () => {
    // For or(and('a','b'), and('c','d')), the invalid total named assignment
    // a=TRUE, b=FALSE, c=TRUE, d=FALSE is refuted at the propagation
    // fixpoint under the bidirectional gate clauses: b=FALSE forces the first
    // and-gate false, d=FALSE forces the second and-gate false, and the
    // asserted root or-gate clause is then falsified. This is an ordinary
    // invalid-model regression for the established encoding: extension
    // correctness plus propagation refutation hold for every total named
    // assignment (assertAgreement below covers all sixteen). It neither
    // relies on nor claims anything about Plaisted-Greenbaum one-sided gates
    // — the proposed PG clauses refute this same assignment — and PG remains
    // a deferred scope decision (Design § Compiler), not a disproven one.
    const expr = or(and('a', 'b'), and('c', 'd'));
    const cnf = compile(expr);
    assertWellFormed(cnf);
    assert.strictEqual(
      cnfSatisfiedUnder(cnf, { a: Value.TRUE, b: Value.FALSE, c: Value.TRUE, d: Value.FALSE }),
      false,
      'the invalid total named assignment is propagation-refuted',
    );
    assertAgreement(expr);
  });
});

// ---------------------------------------------------------------------------
// Semantic agreement with the reference evaluator (fixed corpus)
// ---------------------------------------------------------------------------

// Every expression from the v1 spec, plus the normalization edge cases. The
// 19-variable hypergraph is excluded here (the naive enumerator caps at 8
// variables); it is covered structurally above.
const AGREEMENT_CORPUS: Array<[string, BooleanExpr]> = [
  ["and('a', 'b')", and('a', 'b')],
  ["or('a', 'b')", or('a', 'b')],
  ["not('b')", not('b')],
  ["implies('a', 'b')", implies('a', 'b')],
  ["implies('b', 'a')", implies('b', 'a')],
  ["xor('a', 'b')", xor('a', 'b')],
  [
    'complex worked example',
    and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e'))),
  ],
  [
    'unsolvable example',
    and(
      not('b'),
      or('a', 'b'),
      xor('b', 'c'),
      implies('c', and('d', 'e')),
      not('d'),
      xor('b', 'e'),
    ),
  ],
  ["or('a', not('a'))", or('a', not('a'))],
  ["xor('a', 'a')", xor('a', 'a')],
  ["and('a', 'a')", and('a', 'a')],
  ['and()', and()],
  ['or()', or()],
  // Flattening and constant folding edge cases (folded variables stay in the
  // named universe — see the folded-universe tests below).
  ["and('a', and('b', 'c')) flattens", and('a', and('b', 'c'))],
  ["or('a', or('b', 'c')) flattens", or('a', or('b', 'c'))],
  ["or('a', and()) folds to true", or('a', and())],
  ["and('a', or()) folds to false", and('a', or())],
  ['not(and()) folds to false', not(and())],
  ['not(or()) folds to true', not(or())],
  // Identity-shared and structurally shared subtrees.
  [
    'identity-shared subtree',
    (() => {
      const shared = xor('a', 'b');
      return and(implies('c', shared), or(shared, 'd'));
    })(),
  ],
  [
    'structurally shared subtree (distinct objects)',
    and(or(and('a', 'b'), 'c'), or(and('a', 'b'), 'c')),
  ],
];

describe('compile — fixed corpus agreement with the reference evaluator', () => {
  for (const [label, expr] of AGREEMENT_CORPUS) {
    it(`agrees on ${label} over all named assignments`, () => {
      assertAgreement(expr);
    });
  }
});

// ---------------------------------------------------------------------------
// Property gate: seeded random formulas
// ---------------------------------------------------------------------------

describe('compile — property gate', () => {
  const FORMULA_COUNT = 250;
  for (let seed = 0; seed < FORMULA_COUNT; seed += 1) {
    it(`agrees with the reference evaluator on seed ${seed}`, () => {
      const rng = mulberry32(seed);
      const { expr } = randomFormula(rng, { maxDepth: 4, maxWidth: 4, maxVariables: 6 });
      assertAgreement(expr);
    });
  }
});
