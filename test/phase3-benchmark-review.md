# Phase-3 Evidence Review — task-af80

**Phase 3 is independently verified and approved for its commit.** The phase
verifier reviewed all three tickets and recorded SUCCESS on each. The original
task-level evidence below is retained; the independent approval and its scope
are recorded in the final section. Phase 4 and the future performance objective
are not approved or completed by this result.

## Reproduction and provenance

- `npm run build`, `npm run check`, `npm test`, `npm run bench`, and
  `git diff --check` passed. The full suite passed **594 tests in 67 suites**,
  with no failures, skips, or cancellations. Reported source line coverage was
  98.46% for `compile.ts`, 98.08% for `solver.ts`, and 100% for `index.ts`.
- Two completed benchmark runs produced byte-identical evidence:
  `phase3-benchmark.json` Git blob `d2eb15f01b60a8e639268a94a8081c30570ec6fa`,
  `phase3-benchmark.md` Git blob `36a6910ad1695d48e73b40b64a4d33cc22dbaada`.
  Neither artifact stores models, timestamps, or wall times. Timing is console-only.
- The authenticated Phase-1 reference remains
  `7037f823d192dc3cf2dc9119c8063781e143113c:test/baseline.json`,
  blob `489af8c72ed9c37befa806ccef03404d0a818e61`.
- The authenticated Phase-2 reference is
  `ade64e558ee47c60ae7b4b2cc29f861ccfb245cf:test/phase2-benchmark.json`,
  blob `e838c35c6d99fde7c73627254ecec18255958c58`.
  Its original reference, recorded HEAD, and source hashes are retained in the
  Phase-3 JSON. The runner checks those source hashes against the committed files.
- Current implementation identity comes from actual working-byte SHA-256 hashes,
  not HEAD alone. Source snapshots bracket implementation loading and solving;
  fixture hashes, assumptions, coverage, and conflict caps must match Phase 2.
  Every benchmark SAT model is independently checked against the AST, exact own
  numeric model shape, and constant assumptions. Exhaustion throws, never UNSAT.
- The working `baseline.json` remains the pre-existing dirty blob
  `db759f95c491e685f27ed12039897dcb10c8e4a1`; it is neither the reference nor an
  output target and was not staged. All three historical Phase-2 report/review
  files remain byte-for-byte equal to their versions at `ade64e5`.

## Single-shot comparisons: regressions are real

The generated reports retain all six counters and all eight fixtures. This table
summarizes conflicts; it does not substitute a count ratio for a time speedup.

| Instance | Phase 1 conflicts | Phase 2 conflicts | Phase 3 conflicts | Phase 3 restarts | Current cap |
| --- | --- | --- | --- | --- | --- |
| hypergraph | 0 | 0 | 0 | 0 | 200000 |
| PHP(5,4) | 52 | 28 | 28 | 0 | 200000 |
| PHP(6,5) | 375 | 147 | 152 | 1 | 200000 |
| PHP(7,6) | not recorded | 723 | 834 | 6 | 7230 |
| PHP(8,7) | not recorded | 3627 | 5946 | 29 | 36270 |

Hypergraph retains exactly **2 decisions / 16 propagations / 0 conflicts**.
PHP(6,5), PHP(7,6), and PHP(8,7) have higher decisions, propagations, and conflicts
than Phase 2; all nine count regressions are explicitly listed in the reports.
PHP(5,4) and all three random 3-SAT rows have Phase-2 counter parity. Relative to
Phase 1, small-PHP decision/conflict ratios are 1.34x/1.86x and 1.82x/2.47x.
Phase 1 has no large-PHP measurements and no live-learned counter: missing data
is not evidence of a timeout or infeasibility. All historical caps are unchanged.
No blanket performance gain or orders-of-magnitude improvement is claimed.
The separate future-performance objective `objv-b2ca` is not satisfied here.

## Persistent enumeration: independent correctness and reduction evidence

`getAllSolutions` compiles once, constructs one PLE-disabled solver, and delegates
to `Solver.enumerateModels`. Tests force constructor knobs on that same inherited
loop, not a copied implementation. Assumptions are installed once at root. Each
named-only blocker becomes permanent, followed by root cancellation and explicit
root-aware watch/unit/conflict handling. Learned clauses, activity, and phases
survive; live counters describe that single database.

For `and(or(a1,b1), ..., or(a10,b10))`, each pair admits FT, TF, or TT independently,
so the product is **3^10 = 59049**. The spec cross-checks the independent reference
at k=0..4, and checks small-k learned entailment against the strengthened formula.
At k=10 it validates every model's AST value, exact own named keys, numeric values,
pair constraints, and uniqueness. Validity plus uniqueness plus the mathematical
count proves the full model set without relying on another solver's large count.

| Threshold-32 enumeration measurement | Observed |
| --- | --- |
| Models / permanent blockers | 59049 / 59049 |
| Solve calls including terminal UNSAT | 59050 |
| Decisions / propagations / conflicts / restarts | 514268 / 677578 / 29525 / 0 |
| Total learned / final live learned | 29524 / 87 |
| Peak live learned / fixed bound | 103 / strictly below 256 |
| Automatic reductions / deleting rounds / actual deletions | 922 / 922 / 29437 |
| First deletion | after model 63 |
| High-LBD active-reason retentions across rounds | 5407 |
| Final total database size (10 originals + blockers + live learned) | 59146 |

Total/live snapshots at models 19683, 39366, and 59049 are 9841/68, 19683/67,
and 29524/87. Every automatic reduction checks full watch/canonical-database
invariants, survivor identity/order, protected clauses, and enqueue-prefix reason
validity. Root facts, VSIDS, and saved phases are checked at every model boundary.
The live bound 256 was fixed after valid/unique/product/reference calibration:
twice observed peak 103, rounded up to a power of two. The new enumeration conflict
cap 295250 is ten times the validated 29525 observation; no prior cap was raised.
Permanent blockers intentionally grow with output. This is not a claim that total
memory is bounded by 256, nor that default-threshold enumeration has that bound.

A separate exact-reference enumeration with constant assumptions and internal
restart base 1 / reduction threshold 1 returns all 18 models, with 10 genuine
restarts and 9 actual deletions (17 total / 8 live learned). The repeated run is
deterministic. Empty-formula termination, zero-once stats, PLE counterexamples,
40-variable enumeration, root-satisfied/unit/conflicting admission, normalized
duplicates, and non-vacuously proved learned-to-permanent promotion also pass.

Both property variants retain **1024 formulas / 3824 assumption samples** each,
three repeated single solves, all five constructors, and both eight-name pools.
Each pool has 512 formulas, 509 distinct ASTs, 988 consistent and 924 contradictory
samples. Forced threshold-1 single-shot deletions remain 18 / 24. Forced persistent
enumeration records 17043 / 17205 reductions and 9029 / 9252 actual deletions;
of those, 9023 / 9244 deletions occur after the first model. Counts are kept
separate so single-shot activity cannot stand in for enumeration engagement.

No unresolved correctness, design, or checkpoint blocker was found. The known
Node/tsx DEP0205 warning is non-failing. Parent phase verification and any Git
actions remain outstanding; no later-phase feature was started.

## Independent Phase-3 verification — approved

The phase verifier (`ses_f8a6f8325ffe0kh83Ydd62RXaI`) independently approved
`task-10b8`, `task-e4d1`, and `task-af80` under the current plan and explicit
owner clarifications. This supersedes the preceding task-level statement that
phase verification was outstanding. No implementation or test repair was made
by the verifier.

- Fresh build, Biome check, full tests, benchmark, and whitespace checks passed.
  The full suite passed **594/594 tests across 67 suites**, with no failures or
  skips. Full strict source/test typechecking, a strict NodeNext public-type
  consumer, plain-Node ESM checks, and 48 production-mode restart/Luby/reduction
  tests also passed.
- Independent Luby checks covered 65,535 terms and 53 large-integer boundaries.
  Actual restart ordering, root-no-op epochs, retained root facts, and heap,
  phase, watch, and learned-clause state were verified.
- An independent raw-CNF audit passed **8,192 solves in each of normal and
  production modes**, producing identical results, with exact resolution,
  entailment, reduction-selection, counter, reason, watch, and heap checks.
- A separate helper-independent observer reproduced every stress measurement
  above: all 59,049 unique valid models and permanent blockers, peak 103 live
  learned clauses below 256, 922 deleting rounds, and 29,437 actual deletions.
  The separate constant-assumption 18-model witness reproduced ten actual
  restarts and nine deletions. The learned bound is not a total-memory bound.
- Both complete property variants and their normal/arbitrary-name pools were
  reverified, including 1,024 formulas and 3,824 assumption samples per variant
  and the stated actual single-shot/enumeration deletion counts.
- Both fresh benchmark runs produced identical Phase-3 reports. The verifier
  authenticated historical and current provenance, checked fixture/counter
  consistency, and rejected 22 invalid-evidence cases before report writes.
  The disclosed PHP count regressions remain real; the default benchmark does
  not reach the reduction threshold, so dedicated stress supplies that proof.

No unresolved Phase-3 blocker remains. The parent reviewed the phase diff and
evidence after approval. The pre-existing `test/baseline.json` edit is excluded
from the phase commit and preserved separately; frozen Phase-2 evidence is
unchanged. No later-phase implementation or future-performance achievement is
implied by this approval.
