import type { SolverStats } from '../src/solver.js';

export const COUNTERS = [
  'decisions',
  'propagations',
  'conflicts',
  'restarts',
  'learnedClauses',
  'learnedClausesCurrent',
] as const satisfies readonly (keyof SolverStats)[];

// Cells: Phase1, Phase2, delta (Phase2 - Phase1), ratio (Phase1 / Phase2),
// count change. "Higher" is not automatically worse for learning counters.
export function comparisonCells(phase1: number | undefined, phase2: number): string[] {
  if (phase1 === undefined) {
    return ['not recorded', String(phase2), 'n/a', 'n/a', 'not comparable'];
  }
  const delta = phase2 - phase1;
  const ratio =
    phase2 === 0
      ? phase1 === 0
        ? 'n/a (0/0 parity)'
        : 'n/a (Phase2 is zero)'
      : `${(phase1 / phase2).toFixed(2)}x`;
  return [
    String(phase1),
    String(phase2),
    `${delta > 0 ? '+' : ''}${delta}`,
    ratio,
    delta === 0 ? 'parity' : delta > 0 ? 'higher' : 'lower',
  ];
}
