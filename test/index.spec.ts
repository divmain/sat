import { describe, it } from 'node:test';
import { hrtime } from 'node:process';
import assert from 'node:assert';
import {
  and,
  or,
  not,
  implies,
  xor,
  bruteForceAllSolutions,
  getSolution,
  type BooleanExpr,
  type SelectNextVariable,
  Value,
} from '../src';

const oneOf = (...assertions: (() => void)[]) => {
  const errors = assertions
    .map((assertion) => {
      try {
        assertion();
        return null;
      } catch (err) {
        return err;
      }
    })
    .filter((result) => result !== null);

  if (assertions.length === errors.length) {
    throw assertions[0];
  }
};

describe('getSolution', () => {
  describe('solvable', () => {
    it('supports and operator', () => {
      assert.deepEqual(getSolution(and('a', 'b')), { a: true, b: true });
    });

    it('supports or operator', () => {
      oneOf(
        () => assert.deepEqual(getSolution(or('a', 'b')), { a: true, b: true }),
        () => assert.deepEqual(getSolution(or('a', 'b')), { a: true, b: false }),
        () => assert.deepEqual(getSolution(or('a', 'b')), { a: false, b: true }),
      );
    });

    it('supports not operator', () => {
      assert.deepEqual(getSolution(not('b')), { b: false });
    });

    it('supports implies operator', () => {
      assert.deepEqual(getSolution(implies('a', 'b')), { a: false, b: false });
    });

    it('supports xor operator', () => {
      assert.deepEqual(getSolution(xor('a', 'b')), { a: false, b: true });
    });

    it('supports complex clauses', () => {
      assert.deepEqual(
        getSolution(and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')))),
        {
          a: true,
          b: false,
          c: true,
          d: true,
          e: true,
        },
      );
    });

    describe('hypergraph traversal problems', () => {
      // With the following rgraph, each node can only be visited if _all_
      // parent nodes were visited.
      //        ╭─╮
      //     ┌─▶│b│────────┐
      // ╭─╮ │  ╰─╯    ╭─╮ │
      // │a│─┤      ┌─▶│g│─┤
      // ╰─╯ │  ╭─╮ │  ╰─╯ │  ╭─╮
      //     └─▶│c│─┤      ├─▶│h│
      //        ╰─╯ │  ╭─╮ │  ╰─╯
      //            ├─▶│f│─┘
      // ╭─╮    ╭─╮ │  ╰─╯
      // │d│───▶│e│─┘
      // ╰─╯    ╰─╯

      // There may also be nodes that do not need to be visited in order for
      // particular terminal nodes (e.g. 'h') to be reached.
      // ╭─╮   ╭─╮   ╭─╮   ╭─╮   ╭─╮   ╭─╮
      // │i│──▶│j│──▶│k│──▶│l│──▶│m│──▶│n│
      // ╰─╯   ╰─╯   ╰─╯   ╰─╯   ╰─╯   ╰─╯
      //                                │
      //  ┌─────────────────────────────┘
      //  ▼
      // ╭─╮   ╭─╮   ╭─╮   ╭─╮   ╭─╮
      // │o│──▶│p│──▶│q│──▶│r│──▶│s│
      // ╰─╯   ╰─╯   ╰─╯   ╰─╯   ╰─╯

      // ... the edges can be expressed as prerequisites...
      const nodePrereqs = [
        // for b to be true/visited, a must be true/visited
        ['b', 'a'],
        // etc
        ['c', 'a'],
        ['e', 'd'],
        ['g', 'c'],
        ['f', 'c'],
        ['f', 'e'],
        ['h', 'b'],
        ['h', 'g'],
        // including the disjoint subgraph
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

      // ... which can then be transformed into clauses...
      const baseClauses: BooleanExpr[] = nodePrereqs.map(([a, b]) => implies(a, b));
      // ... and relationships.
      const relationships = nodePrereqs.reduce((memo, [a, b]) => {
        if (!memo.has(b)) {
          memo.set(b, []);
        }
        // biome-ignore lint/style/noNonNullAssertion: existence was just checked
        memo.get(b)!.push(a);
        return memo;
      }, new Map<string, string[]>());

      // When a solution is being sought, we can use the structure of the hypergraph to
      // select the next variable that should receive a value.
      const selectNextVar: SelectNextVariable = (variables, assignments) => {
        const candidates = variables.filter((varName) => assignments[varName] === Value.UNSET);
        if (!candidates.length) {
          return null;
        }

        const satisfiedRelationships = Object.fromEntries(
          candidates.map((candidate) => [candidate, 0]),
        );

        // for each variable under consideration
        for (const candidate of candidates) {
          // identify its "parent" variables/nodes
          const connectedVars = relationships.get(candidate);
          if (connectedVars) {
            // and track how many parents are already satisfied
            for (const connectedVar of connectedVars) {
              if (assignments[connectedVar] === Value.TRUE) {
                satisfiedRelationships[candidate] += 1;
              } else if (assignments[connectedVar] === Value.FALSE) {
                satisfiedRelationships[candidate] = -1 * variables.length;
              }
            }
          }
        }

        let topCandidate: string = candidates[0];
        let topCandidateRank = Number.NEGATIVE_INFINITY;
        for (const candidate of candidates) {
          const rank = satisfiedRelationships[candidate];
          if (rank > topCandidateRank) {
            topCandidate = candidate;
            topCandidateRank = rank;
          }
        }

        return topCandidateRank >= 1 ? [topCandidate, true] : [topCandidate, false];
      };

      it('can be efficiently solved', () => {
        const slowStart = hrtime.bigint();
        const slowSolution = getSolution(and(...baseClauses), { h: Value.TRUE });
        const slowEnd = hrtime.bigint();

        const fastStart = hrtime.bigint();
        const fastSolution = getSolution(and(...baseClauses), { h: Value.TRUE }, selectNextVar);
        const fastEnd = hrtime.bigint();

        assert.deepEqual(slowSolution, fastSolution);

        const slowTime = slowEnd - slowStart;
        const fastTime = fastEnd - fastStart;

        assert.ok(
          slowTime > fastTime * 1000n,
          'heuristic based solver should be at least 1000 times faster',
        );
      });
    });
  });

  describe('unsolvable', () => {
    assert.deepEqual(
      getSolution(
        and(
          not('b'),
          or('a', 'b'),
          xor('b', 'c'),
          implies('c', and('d', 'e')),
          not('d'),
          xor('b', 'e'),
        ),
      ),
      null,
    );
  });
});

describe('bruteForceAllSolutions', () => {
  describe('solvable', () => {
    describe('and', () => {
      assert.deepEqual(bruteForceAllSolutions(and('a', 'b')), [{ a: true, b: true }]);
    });

    describe('or', () => {
      assert.deepEqual(bruteForceAllSolutions(or('a', 'b')), [
        { a: false, b: true },
        { a: true, b: false },
        { a: true, b: true },
      ]);
    });

    describe('not', () => {
      assert.deepEqual(bruteForceAllSolutions(not('b')), [{ b: false }]);
    });

    describe('implies', () => {
      assert.deepEqual(bruteForceAllSolutions(implies('a', 'b')), [
        { a: false, b: false },
        { a: false, b: true },
        { a: true, b: true },
      ]);
    });

    describe('xor', () => {
      assert.deepEqual(bruteForceAllSolutions(xor('a', 'b')), [
        { a: false, b: true },
        { a: true, b: false },
      ]);
    });

    describe('complex', () => {
      assert.deepEqual(
        bruteForceAllSolutions(
          and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e'))),
        ),
        [
          {
            a: true,
            b: false,
            c: true,
            d: true,
            e: true,
          },
        ],
      );
    });
  });

  describe('unsolvable', () => {
    assert.deepEqual(
      bruteForceAllSolutions(
        and(
          not('b'),
          or('a', 'b'),
          xor('b', 'c'),
          implies('c', and('d', 'e')),
          not('d'),
          xor('b', 'e'),
        ),
      ),
      [],
    );
  });
});
