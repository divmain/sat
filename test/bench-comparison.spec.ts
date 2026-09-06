import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { comparisonCells } from './bench-comparison.js';

describe('benchmark comparison cells', () => {
  it('labels a reduction with the original/current ratio and signed delta', () => {
    assert.deepEqual(comparisonCells(51, 38), ['51', '38', '-13', '1.34x', 'lower']);
  });

  it('retains regressions rather than inverting the ratio to look like a gain', () => {
    assert.deepEqual(comparisonCells(6, 9), ['6', '9', '+3', '0.67x', 'higher']);
  });

  it('distinguishes positive parity from an undefined zero/zero ratio', () => {
    assert.deepEqual(comparisonCells(2, 2), ['2', '2', '0', '1.00x', 'parity']);
    assert.deepEqual(comparisonCells(0, 0), ['0', '0', '0', 'n/a (0/0 parity)', 'parity']);
  });

  it('does not turn missing Phase-1 data into zero, a timeout, or an infinite gain', () => {
    assert.deepEqual(comparisonCells(undefined, 723), [
      'not recorded',
      '723',
      'n/a',
      'n/a',
      'not comparable',
    ]);
    assert.deepEqual(comparisonCells(undefined, 0), [
      'not recorded',
      '0',
      'n/a',
      'n/a',
      'not comparable',
    ]);
  });

  it('keeps learning from zero as a higher count, not a speedup', () => {
    assert.deepEqual(comparisonCells(0, 27), ['0', '27', '+27', '0.00x', 'higher']);
  });

  it('handles a zero current count without emitting a non-finite ratio', () => {
    assert.deepEqual(comparisonCells(5, 0), ['5', '0', '-5', 'n/a (Phase2 is zero)', 'lower']);
  });
});
