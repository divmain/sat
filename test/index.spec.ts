import { describe } from 'node:test';
import assert from 'node:assert';
import { and, or, not, implies, xor, bruteForceAllSolutions, getDpllSolution } from '../src';

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

describe('getDpllSolution', () => {
  describe('solvable', () => {
    describe('and', () => {
      assert.deepEqual(getDpllSolution(and('a', 'b')), { a: true, b: true });
    });

    describe('or', () => {
      oneOf(
        () => assert.deepEqual(getDpllSolution(or('a', 'b')), { a: true, b: true }),
        () => assert.deepEqual(getDpllSolution(or('a', 'b')), { a: true, b: false }),
        () => assert.deepEqual(getDpllSolution(or('a', 'b')), { a: false, b: true }),
      );
    });

    describe('not', () => {
      assert.deepEqual(getDpllSolution(not('b')), { b: false });
    });

    describe('implies', () => {
      assert.deepEqual(getDpllSolution(implies('a', 'b')), { a: true, b: true });
    });

    describe('xor', () => {
      assert.deepEqual(getDpllSolution(xor('a', 'b')), { a: true, b: false });
    });

    describe('complex', () => {
      assert.deepEqual(
        getDpllSolution(and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')))),
        {
          a: true,
          b: false,
          c: true,
          d: true,
          e: true,
        },
      );
    });
  });

  describe('unsolvable', () => {
    assert.deepEqual(
      getDpllSolution(
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
