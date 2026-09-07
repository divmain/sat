// Pinned once at implementation: two identical runs with fresh compiled
// formulas, the default brancher, enablePle: true, and maxConflicts: 200_000.
// Each cap is exactly 10x the observed conflicts, never recalibrated at runtime.
// UNSAT follows independently from the pigeonhole principle (pigeons > holes).
// Passing proves only this budget, not that earlier implementations were
// infeasible or improved orders of magnitude; the reference recorded
// neither of these larger instances.
export const PHP_REGRESSIONS = [
  { pigeons: 7, holes: 6, calibratedConflicts: 723, maxConflicts: 7_230 },
  { pigeons: 8, holes: 7, calibratedConflicts: 3_627, maxConflicts: 36_270 },
] as const;
