// Test-suite preload for solver debug audits, wired as
// `tsx --import ./test/debug.ts` in every npm test script. Node propagates
// --import to each node:test worker (verified on Node v26.8.1), so audits run
// for the whole suite without per-file wiring. The globalThis marker below is
// the load-proof: test/platform-guard.spec.ts asserts it inside a worker, so
// a silently skipped preload fails loudly instead of quietly dropping audit
// coverage. Never import this file from a spec file — the marker must be
// attributable to the preload alone, or the guard would be vacuous.
import { setDebugAssertions } from '../src/solver.js';

setDebugAssertions(true);

type DebugAuditGlobal = typeof globalThis & { __SAT_DEBUG_AUDITS__?: boolean };
(globalThis as DebugAuditGlobal).__SAT_DEBUG_AUDITS__ = true;
