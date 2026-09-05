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
