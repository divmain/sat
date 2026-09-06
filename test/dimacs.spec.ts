// DIMACS mini-parser, programmatic generators, and end-to-end verdicts
// (Design § Testing and Benchmarking Strategy): the parser is verified by
// asserting exact parsed clause contents on hand-checkable inputs, the
// generators by their exact clause structure and determinism, and the whole
// pipeline (generator → serialized DIMACS → parser → BooleanExpr → solver)
// by end-to-end verdicts: pigeon-hole UNSAT (including conflict-bounded
// PHP(7,6)/PHP(8,7)), a satisfiable prereq chain SAT with n+1 enumeration,
// and seeded random 3-CNF.

import { describe, it } from 'node:test';
import assert from 'node:assert';
import { getAllSolutions, getSolution, Value } from '../src';
import { compile } from '../src/compile';
import { Solver } from '../src/solver';
import type { SolverStats } from '../src/solver';
import {
  assertModelListsEqual,
  assertModelShape,
  cnfToExpr,
  expressionValue,
  mulberry32,
  phpCnf,
  prereqChainCnf,
  random3Cnf,
  serializeDimacs,
  parseDimacs,
  referenceModels,
} from './helpers';
import type { DimacsCnf } from './helpers';
import { PHP_REGRESSIONS } from './php-regressions';

// ---------------------------------------------------------------------------
// Parser correctness on hand-checkable inputs
// ---------------------------------------------------------------------------

describe('DIMACS mini-parser', () => {
  it('parses a hand-checkable instance to its exact clause contents', () => {
    const text = [
      'c simple three-variable instance',
      'c a second comment line',
      'p cnf 3 2',
      '1 -2 0',
      '-1 2 3 0',
    ].join('\n');
    assert.deepEqual(parseDimacs(text), {
      numVars: 3,
      clauses: [
        [1, -2],
        [-1, 2, 3],
      ],
    });
  });

  it('tolerates blank lines, extra whitespace, and CRLF line endings', () => {
    const text = 'c comment\r\n\r\np cnf 2 1\r\n  1   2 \t 0\r\n';
    assert.deepEqual(parseDimacs(text), { numVars: 2, clauses: [[1, 2]] });
  });

  it('accepts clauses spanning multiple lines and comments after the data', () => {
    const text = ['p cnf 3 2', '1 -2', '2 0 -1 2 3 0', 'c trailing comment'].join('\n');
    assert.deepEqual(parseDimacs(text), {
      numVars: 3,
      clauses: [
        [1, -2, 2],
        [-1, 2, 3],
      ],
    });
  });

  it('rejects malformed inputs with descriptive errors', () => {
    assert.throws(() => parseDimacs(''), /missing the header line/);
    assert.throws(() => parseDimacs('1 2 0\n'), /before the header/);
    assert.throws(() => parseDimacs('p cnf 3 2\np cnf 3 2\n1 0\n'), /more than one header/);
    assert.throws(() => parseDimacs('p sat 3 2\n'), /malformed DIMACS header/);
    assert.throws(() => parseDimacs('p cnf 3\n'), /malformed DIMACS header/);
    assert.throws(() => parseDimacs('p cnf x 2\n'), /invalid DIMACS header counts/);
    assert.throws(() => parseDimacs('p cnf -1 2\n'), /invalid DIMACS header counts/);
    assert.throws(() => parseDimacs('p cnf 3 2\n1 x 0\n'), /non-integer DIMACS token: x/);
    assert.throws(
      () => parseDimacs('p cnf 3 1\n1 4 0\n'),
      /literal out of range \(4 for 3 variables\)/,
    );
    assert.throws(
      () => parseDimacs('p cnf 3 1\n1 0 0\n'),
      /terminator 0 with no preceding literal/,
    );
    assert.throws(() => parseDimacs('p cnf 3 1\n1 2\n'), /ends inside a clause/);
    assert.throws(
      () => parseDimacs('p cnf 3 2\n1 0\n'),
      /clause count mismatch: found 1, expected 2/,
    );
  });

  it('round-trips through the serializer', () => {
    const cnf: DimacsCnf = {
      numVars: 4,
      clauses: [
        [1, -2],
        [-1, 2, -3],
        [3, -4],
      ],
    };
    assert.deepEqual(parseDimacs(serializeDimacs(cnf)), cnf);
    assert.equal(serializeDimacs(cnf), 'p cnf 4 3\n1 -2 0\n-1 2 -3 0\n3 -4 0\n');
  });
});

// ---------------------------------------------------------------------------
// Programmatic generators
// ---------------------------------------------------------------------------

describe('programmatic CNF generators', () => {
  it('builds PHP(5,4) with the exact pigeon-grouped clause structure', () => {
    const php = phpCnf(5, 4);
    assert.equal(php.numVars, 20);
    // 5 pigeon clauses (one per pigeon, width 4) + C(5,2) * 4 hole clauses.
    assert.equal(php.clauses.length, 5 + 10 * 4);
    // Pigeon 0 must be in at least one hole.
    assert.deepEqual(php.clauses[0], [1, 2, 3, 4]);
    // Pigeon 1 must be in at least one hole.
    assert.deepEqual(php.clauses[1], [5, 6, 7, 8]);
    // Pigeons 0 and 1 cannot share hole 0.
    assert.deepEqual(php.clauses[5], [-1, -5]);
    // Pigeons 0 and 1 cannot share hole 3.
    assert.deepEqual(php.clauses[8], [-4, -8]);
  });

  it('serializes PHP as valid DIMACS and re-parses to the same structure', () => {
    const php = phpCnf(5, 4);
    assert.deepEqual(parseDimacs(serializeDimacs(php)), php);
  });

  it('builds a prereq chain with exactly n-1 binary clauses', () => {
    assert.deepEqual(prereqChainCnf(5), {
      numVars: 5,
      clauses: [
        [-2, 1],
        [-3, 2],
        [-4, 3],
        [-5, 4],
      ],
    });
  });

  it('rejects invalid generator arguments', () => {
    assert.throws(() => phpCnf(0, 4));
    assert.throws(() => phpCnf(4, 0));
    assert.throws(() => prereqChainCnf(0));
    assert.throws(() => random3Cnf(mulberry32(1), 2, 1));
    assert.throws(() => random3Cnf(mulberry32(1), 3, -1));
  });

  it('generates deterministic fixed-width 3-CNF from a seed', () => {
    const a = random3Cnf(mulberry32(42), 20, 85);
    const b = random3Cnf(mulberry32(42), 20, 85);
    const c = random3Cnf(mulberry32(43), 20, 85);
    assert.deepEqual(a, b, 'same seed must produce the identical CNF');
    assert.notDeepEqual(a, c, 'different seeds must produce different CNFs');
    assert.equal(a.numVars, 20);
    assert.equal(a.clauses.length, 85);
    for (const clause of a.clauses) {
      assert.equal(clause.length, 3, 'every clause is exactly ternary');
      assert.equal(new Set(clause.map(Math.abs)).size, 3, 'three distinct variables per clause');
      for (const literal of clause) {
        assert.ok(literal !== 0 && Math.abs(literal) <= a.numVars, `in-range literal: ${literal}`);
      }
    }
  });
});

// ---------------------------------------------------------------------------
// End-to-end verdicts through generator → DIMACS → parser → solver
// ---------------------------------------------------------------------------

describe('end-to-end DIMACS verdicts', () => {
  // Round-trip the generators through the parser so end-to-end verdicts
  // exercise the complete test-internal DIMACS pipeline.
  const throughDimacs = (cnf: DimacsCnf) => cnfToExpr(parseDimacs(serializeDimacs(cnf)));

  it('proves PHP(5,4) UNSAT', () => {
    assert.strictEqual(getSolution(throughDimacs(phpCnf(5, 4))), null);
  });

  it('proves PHP(6,5) UNSAT with clause learning', () => {
    const stats = {
      decisions: 0,
      propagations: 0,
      conflicts: 0,
      restarts: 0,
      learnedClauses: 0,
      learnedClausesCurrent: 0,
    };
    assert.strictEqual(getSolution(throughDimacs(phpCnf(6, 5)), { stats }), null);
    assert.ok(stats.learnedClauses > 0, 'learning, not merely conflicts, distinguishes CDCL');
  });

  for (const { pigeons, holes, calibratedConflicts, maxConflicts } of PHP_REGRESSIONS) {
    it(`proves PHP(${pigeons},${holes}) UNSAT reproducibly below ${maxConflicts} conflicts`, () => {
      // Independent verdict: each pigeon must occupy a hole, and the binary
      // clauses prohibit shared holes. More pigeons than holes is impossible;
      // no prior solver result supplies the expected UNSAT answer.
      assert.ok(pigeons > holes);
      assert.strictEqual(maxConflicts, calibratedConflicts * 10, 'fixed 10x calibration padding');
      const runs: SolverStats[] = [];
      for (let run = 0; run < 2; run += 1) {
        // Recompile for each fresh solver: watched clause literal order and
        // clause activity are mutable. Mirror single-shot PLE, without a hook.
        const solver = new Solver(compile(throughDimacs(phpCnf(pigeons, holes))), {
          enablePle: true,
          maxConflicts,
        });
        // A budget exception must fail this test, never masquerade as UNSAT.
        assert.strictEqual(solver.solve(), false);
        assert.ok(solver.stats.conflicts < maxConflicts, 'UNSAT proof finishes before exhaustion');
        assert.ok(solver.stats.learnedClauses > 0, 'clause learning must actually engage');
        assert.ok(solver.stats.restarts > 0, 'default-budget restarts must actually engage');
        runs.push({ ...solver.stats });
      }
      assert.deepStrictEqual(runs[1], runs[0], 'fresh default solves have identical counters');
    });
  }

  it('finds a model for a satisfiable prereq chain and enumerates all n+1 models', () => {
    const expr = throughDimacs(prereqChainCnf(8));
    const model = getSolution(expr);
    assert.ok(model !== null, 'the chain is satisfiable');
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE);

    const all = getAllSolutions(expr);
    assert.strictEqual(all.length, 9, 'an 8-variable chain has exactly 9 models');
    assertModelListsEqual(all, referenceModels(expr));
    for (const m of all) {
      assertModelShape(m, expr);
      assert.strictEqual(expressionValue(expr, m), Value.TRUE);
    }
  });

  it('solves a seeded random 3-CNF instance end-to-end with a valid model', () => {
    const expr = throughDimacs(random3Cnf(mulberry32(42), 20, 85));
    const model = getSolution(expr);
    assert.ok(model !== null, 'seed 42 at 20 vars/85 clauses is satisfiable (pinned)');
    assertModelShape(model, expr);
    assert.strictEqual(expressionValue(expr, model), Value.TRUE);
  });
});
