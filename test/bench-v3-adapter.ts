// Candidate-side scenario runner for the v3 harness. It mirrors the frozen
// v2 recorder's adapter (test/v3-baseline-overlay/adapter.ts, never imported
// here) against the CURRENT candidate sources: PLE only for single-shot, one
// persistent solveAssuming core for incremental calls, and the
// permanent-blocker loop for enumeration, with one positive lifetime conflict
// cap spanning construction and the whole scenario. Until public conflict
// budgets land (Phase 3), the candidate adapter uses the same internal
// maxConflicts mechanism as the frozen v2 adapter; this is not a claim that
// v2 had public budgets. Partial calls/models survive cap exhaustion, and the
// interrupted core is discarded immediately.

import assert from 'node:assert/strict';
import { compile } from '../src/compile.js';
import { Value } from '../src/expr.js';
import { Solver } from '../src/solver.js';
import type { SolverStats } from '../src/solver.js';
import { compiledSnapshot, digest, inputIdentity, modelEvidence } from './bench-evidence.js';
import type { Scenario } from './bench-v3-corpus.js';

export const workCounters = [
  'decisions',
  'propagations',
  'conflicts',
  'restarts',
  'learnedClauses',
  'learnedLiterals',
  'minimizedLiterals',
] as const;
export const zeroStats = (): SolverStats => ({
  decisions: 0,
  propagations: 0,
  conflicts: 0,
  restarts: 0,
  learnedClauses: 0,
  learnedClausesCurrent: 0,
  learnedLiterals: 0,
  minimizedLiterals: 0,
});

export interface CallEvidence {
  index: number;
  status: 'sat' | 'unsat' | 'exhausted';
  modelDigest: string | null;
  stats: SolverStats;
}

export function runScenario(scenario: Scenario, cap: number) {
  assert.ok(Number.isSafeInteger(cap) && cap > 0, 'v3 scenario caps must be positive');
  const inputSha256 = digest(inputIdentity(scenario));
  const cnf = compile(scenario.expr);
  const compiledSha256 = digest(compiledSnapshot(cnf));
  const stats = zeroStats();
  const solver = new Solver(cnf, {
    enablePle: scenario.mode === 'single',
    assumptions: scenario.mode === 'incremental' ? undefined : scenario.assumptions,
    maxConflicts: cap,
    stats,
  });
  const construction = { ...stats };
  const calls: CallEvidence[] = [];
  const modelDigests: string[] = [];
  let status: 'sat' | 'unsat' | 'complete' | 'exhausted' = 'exhausted';
  let activeCall: CallEvidence | null = null;
  try {
    if (scenario.mode === 'incremental') {
      for (const [index, assumptions] of scenario.calls.entries()) {
        activeCall = { index, status: 'exhausted', modelDigest: null, stats: zeroStats() };
        calls.push(activeCall);
        const model = solver.solveAssuming(assumptions, activeCall.stats);
        activeCall.status = model === null ? 'unsat' : 'sat';
        activeCall.modelDigest =
          model === null ? null : modelEvidence(scenario.expr, assumptions, model);
      }
      status = 'complete';
    } else if (scenario.mode === 'enumeration') {
      while (solver.solve()) {
        modelDigests.push(modelEvidence(scenario.expr, scenario.assumptions, solver.model()));
        const blocker: number[] = [];
        for (let variable = 0; variable < cnf.numNamedVars; variable += 1) {
          blocker.push(variable * 2 + (solver.assigns[variable] === Value.TRUE ? 1 : 0));
        }
        solver.addPermanentClause(blocker);
      }
      status = 'complete';
    } else {
      status = solver.solve() ? 'sat' : 'unsat';
      if (status === 'sat') {
        modelDigests.push(modelEvidence(scenario.expr, scenario.assumptions, solver.model()));
      }
    }
  } catch (error) {
    // Only this exact exception is evidence of cap exhaustion. The
    // cap-reaching conflict is counted BEFORE analysis; never reuse this core.
    if (
      !(error instanceof Error) ||
      error.message !== `maximum conflict budget exhausted (${cap})`
    ) {
      throw error;
    }
    assert.equal(stats.conflicts, cap);
    status = 'exhausted';
  }
  if (status !== 'exhausted') assert.ok(stats.conflicts < cap);
  if (scenario.mode === 'incremental') {
    for (const key of workCounters) {
      assert.equal(
        stats[key],
        construction[key] + calls.reduce((sum, call) => sum + call.stats[key], 0),
      );
    }
    if (activeCall)
      assert.equal(activeCall.stats.learnedClausesCurrent, stats.learnedClausesCurrent);
  }
  assert.equal(new Set(modelDigests).size, modelDigests.length, 'duplicate enumerated model');
  return {
    id: scenario.id,
    mode: scenario.mode,
    inputSha256,
    compiledSha256,
    cap,
    status,
    construction,
    stats: { ...stats },
    calls,
    completedCalls: calls.filter((call) => call.status !== 'exhausted').length,
    unexecutedCalls: scenario.calls.length - calls.length,
    orderedCallDigest: digest(
      calls.map(({ index, status, modelDigest }) => ({ index, status, modelDigest })),
    ),
    modelCount: modelDigests.length,
    modelDigest: scenario.mode === 'single' ? modelDigests[0] ?? null : null,
    modelSetDigest: digest([...modelDigests].sort()),
    orderedModelPrefixDigest: digest(modelDigests),
    // Ordered per-model digests make exhausted prefixes independently inspectable.
    modelDigests,
  };
}

export type Measurement = ReturnType<typeof runScenario>;
