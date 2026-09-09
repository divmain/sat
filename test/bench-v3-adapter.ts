// Candidate-side scenario runner for the v3 harness. It mirrors the frozen
// v2 recorder's adapter (test/v3-baseline-overlay/adapter.ts, never imported
// here) against the CURRENT candidate sources: PLE only for single-shot, one
// persistent solveAssuming core for incremental calls, and the production
// enumeration loop, with one positive conflict BUDGET spanning construction
// and the whole scenario. The candidate uses the non-throwing conflictBudget
// mechanism: incremental calls receive the REMAINING scenario cap and the
// scenario stops before another call once it reaches zero — never silently
// multiplying the 32-call cap — while single-shot and enumeration spans pass
// it once. An exhausted call/search returns 'unknown' (the final conflict's
// atomic transaction IS counted and learned, unlike v2's pre-analysis throw;
// disclosed, and historical counters are never relabeled). Partial
// calls/models survive exhaustion, and the interrupted core is discarded
// immediately.

import assert from 'node:assert/strict';
import { compile } from '../src/compile.js';
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
    // Single-shot and enumeration spans pass the scenario-wide cap once;
    // incremental calls pass the REMAINING cap per call below.
    conflictBudget: scenario.mode === 'incremental' ? undefined : cap,
    stats,
  });
  const construction = { ...stats };
  const calls: CallEvidence[] = [];
  const modelDigests: string[] = [];
  let status: 'sat' | 'unsat' | 'complete' | 'exhausted' = 'exhausted';
  let activeCall: CallEvidence | null = null;
  if (scenario.mode === 'incremental') {
    let spent = 0;
    for (const [index, assumptions] of scenario.calls.entries()) {
      const remaining = cap - spent;
      if (remaining <= 0) {
        // Never invoke the budget-zero startup exception as a loophole: stop
        // before another call once the scenario-wide cap is spent.
        break;
      }
      activeCall = { index, status: 'exhausted', modelDigest: null, stats: zeroStats() };
      calls.push(activeCall);
      const result = solver.solveAssuming(assumptions, activeCall.stats, remaining);
      spent += activeCall.stats.conflicts;
      if (result.status === 'unknown') {
        // Budget exhaustion mid-call: keep the partial-call evidence and
        // stop the scenario; the interrupted core is discarded.
        break;
      }
      activeCall.status = result.status === 'unsat' ? 'unsat' : 'sat';
      activeCall.modelDigest =
        result.status === 'sat' ? modelEvidence(scenario.expr, assumptions, result.model) : null;
    }
    if (calls.length === scenario.calls.length && activeCall?.status !== 'exhausted') {
      status = 'complete';
    }
  } else if (scenario.mode === 'enumeration') {
    const outcome = solver.enumerateModels();
    for (const model of outcome.models) {
      modelDigests.push(modelEvidence(scenario.expr, scenario.assumptions, model));
    }
    status = outcome.status === 'complete' ? 'complete' : 'exhausted';
  } else {
    const verdict = solver.search();
    if (verdict === 'unknown') {
      status = 'exhausted';
    } else {
      status = verdict === 'sat' ? 'sat' : 'unsat';
      if (status === 'sat') {
        modelDigests.push(modelEvidence(scenario.expr, scenario.assumptions, solver.model()));
      }
    }
  }
  if (status === 'exhausted') {
    // The final conflict's atomic transaction is counted: exhaustion lands
    // exactly at the cap, never beyond it.
    assert.equal(stats.conflicts, cap);
  } else {
    assert.ok(stats.conflicts < cap);
  }
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
