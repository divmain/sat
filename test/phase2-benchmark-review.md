# Phase-2 Benchmark Review

Manual review, not an automated performance gate. The generated [comparison](./phase2-benchmark.md) and [raw counters](./phase2-benchmark.json) retain every original row plus both new PHP rows. Earlier checkpoint claims and verification hashes are retained below; the latest artifact identities are in [Test-Harness Repair Checkpoint](#test-harness-repair-checkpoint).

**Phase 2 is independently verified and approved.** The original verifier re-attempted verification after the scoped harness repairs and recorded SUCCESS on `task-884f` at `2026-09-06T04:57:58Z`. That result supersedes its `2026-09-06T02:17:57Z` FAILURE. The historical task and repair checkpoints below remain intact; the latest disposition is in [Independent Phase-2 Reverification](#independent-phase-2-reverification).

## Owner-Approved Acceptance Clarification

**Superseding disposition note:** the owner-approved note on `task-884f` at **2026-09-06T01:56:58Z** supersedes only the original orders-of-magnitude PHP and unsupported Phase-1-infeasibility requirements. The original findings and failure history below are retained, but those two claims are no longer acceptance blockers for this ticket. This is an authorized correction of the acceptance interpretation, not evidence that the original advertised reductions were achieved.

Current performance acceptance requires an authentic, reproducible comparison against the committed Phase-1 reference; honest actual improvements and regressions; learning engaged on PHP rows; hypergraph parity at **2 decisions, 16 propagations, 0 conflicts**; and PHP(7,6)/PHP(8,7) UNSAT within the independently calibrated, fixed **10x-padded conflict budgets**. Missing baseline measurements remain missing, not timeouts or infeasibility. All other requirements, including the expanded property suite, repeated verdicts, green tooling, and unchanged public API, remain binding.

The parent created only objective **`objv-b2ca` — Demonstrate substantial principled CDCL performance improvements** for the future algorithmic goals. That objective is independent of `plan-7748`, remains unrealized, and is not satisfied by completing this ticket or plan. No follow-up ticket or additional objective was created by this work. Solver code, counters, tests, fixtures, budgets, and baseline values were not changed to obtain this disposition.

## Historical Acceptance Blocker — Superseded

**FAILURE against the original task-884f performance acceptance.** Learning is engaged on the PHP rows and the hypergraph control has parity, but the comparable PHP reductions are not orders of magnitude:

| instance | decisions (Phase1 -> Phase2) | Phase1/Phase2 | conflicts (Phase1 -> Phase2) | Phase1/Phase2 | learnedClauses (Phase1 -> Phase2) |
| --- | --- | --- | --- | --- | --- |
| php_5_4 | 51 -> 38 | 1.34x | 52 -> 28 | 1.86x | 0 -> 27 |
| php_6_5 | 374 -> 195 | 1.92x | 375 -> 147 | 2.55x | 0 -> 146 |

The original Phase-1 baseline contains completed small PHP rows, no budget-exhausted rows, and no PHP(7,6)/PHP(8,7) rows. There is no recorded Phase-1 counterpart from which to calculate a reduction or establish infeasibility for the two larger cases. Missing data is not a timeout, a capped measurement, or an infinite improvement.

PHP(7,6) completed with 723 conflicts against its fixed 7,230 cap; PHP(8,7) completed with 3,627 conflicts against 36,270. Both caps are exactly 10x the implementation-time observations, not auto-recalibrated. UNSAT follows independently from the pigeonhole principle. Passing establishes only these budgets; the padded caps are not baseline measurements or evidence of orders-of-magnitude improvement.

All six original rows still use the 200,000 conflict cap and the original generators, including 20-variable/85-clause random 3-SAT with seeds 42/43/44. All eight runs use fresh compilation, the default brancher, and `enablePle: true`. Full old/current counters, signed deltas, and labelled ratios are in the generated comparison, including zero/zero parity and the unrecorded Phase-1 `learnedClausesCurrent` counter.

## Immutable Reference

- Reference: `7037f823d192dc3cf2dc9119c8063781e143113c:test/baseline.json`
- Verified Git blob: `489af8c72ed9c37befa806ccef03404d0a818e61`
- Original baseline SHA-256: `826b4ce3b30a160ab54be48fefd4ca63affc7707786609bd481aabda6536b8ac`
- Measured working-tree `src/solver.ts` SHA-256: `cee5031d304b5dacd9d8ed0a4de0b8908c4bd1ae5edd5f528aca79c0c85a12a1`
- The generated artifacts include raw-byte SHA-256 fingerprints for the implementation, benchmark tooling, and package/compiler configuration, plus generated formula/assumption fingerprints for all eight fixtures. HEAD is context only, not a claim that the measured implementation was committed.
- The pre-existing, modified working-tree `test/baseline.json` was neither used as Phase 1 nor edited. The runner always loads and verifies the fixed Git reference, never HEAD's baseline or the previous benchmark output.

## Historical Repeatability And Preservation — Before Clarification

Two successful `npm run bench` invocations on Node `v26.8.1` with `NODE_ENV` unset produced identical complete counters and identical artifact SHA-256 hashes. These hashes also stayed unchanged across the negative reference checks. Relevant artifact parents were verified with `ls` before benchmark commands.

| file | checkpoints | SHA-256 |
| --- | --- | --- |
| test/baseline.json | Before implementation, after first run, after negative checks, after second run | 6828679df735765cf3d9a4ede04333366742efe7ff5899fc5fdb823425d9ab9a |
| test/phase2-benchmark.json | First run = after negative checks = second run | 174e79dfcecffbc15bace62db30493db3ee8906fd8fe24fec3341a5f3cc45d8b |
| test/phase2-benchmark.md | First run = after negative checks = second run | 5162b1114ab5739fe36ad8d5ae06ad678ab6bcc0be793bad66e8973ee10868b0 |

The reports store no models, timestamps, or wall times. Wall time was printed only to the console. No wall-clock assertions were added.

## Historical Scoped Verification — Before Clarification

- `npm run bench` twice: both completed all eight rows with the counters in the retained artifacts.
- `npx tsx --test test/bench-comparison.spec.ts`: all six tests passed. Cases cover reductions, regressions, positive parity, zero/zero parity, missing measurements (including missing versus zero), learning from zero, and a zero current denominator.
- `npx biome check test/bench.ts test/php-regressions.ts test/bench-comparison.ts test/bench-comparison.spec.ts test/phase2-benchmark.json`: passed for all five files after an `apply_patch` formatting correction.
- `npx tsc --noEmit --module NodeNext --moduleResolution NodeNext --target es2022 --strictNullChecks --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck test/bench.ts test/bench-comparison.spec.ts test/php-regressions.ts`: passed without emitting files.
- `git diff --check -- test/bench.ts`: passed.
- Unavailable history: an isolated child `npm run bench` with `GIT_DIR` pointing at the non-Git `test/php-regressions.ts` file exited 1 before recording. The verification wrapper was corrected to expect Git's actual `invalid gitfile format` diagnostic, then passed; the runner needed no change.
- Mismatched bytes: an isolated Node/tsx process substituted `{}` for `git show` output and asserted the exact full-commit lookup arguments. Importing the runner rejected with `Phase-1 baseline blob mismatch` before solving or recording.
- Budget semantics only: a fresh current PHP(5,4) solver with `maxConflicts: 1` threw `maximum conflict budget exhausted (1)` at one conflict rather than returning UNSAT. This negative check wrote no evidence and was not used as a Phase-1 measurement or improvement claim.

The benchmark work made no solver, public API, existing Phase-2 test, working-tree baseline, AGENTS, or Janus edits. No staging, commits, amendments, pushes, or PRs were performed.

## Historical Task-884f Checkpoint — Before Owner Clarification

The main implementation expanded `property.spec.ts` from 320 to 512 seeded formulas, with an additional assertion that at least 500 structurally distinct ASTs are exercised (the fixed stream contains 509). Each formula and each applicable consistent/contradictory assumption sample receives three fresh single solves of the same input objects. Every verdict is checked against the independently computed reference, every returned single model is validated, and the existing exact enumeration-count/set, shape, and duplicate checks are retained. The seven fixed battery cases are retained too.

The new DIMACS PHP regressions each run twice with fresh compiled clauses, require UNSAT and actual learning, enforce the pinned 10x conflict caps, and compare complete counters across the two runs. The expected UNSAT verdict is mathematical, not calibrated from solver output; only the resource bound is calibrated. Budget exceptions are not caught as results.

| verification | result |
| --- | --- |
| `npm run build` | Passed |
| `npm run check` | Passed; 19 files, no lint or format fixes needed |
| `npm test` | Passed; 430/430 tests, 45 suites, no failures or skips |
| `npx tsx --test './test/property.spec.ts' './test/dimacs.spec.ts'` | Passed; 22/22 tests |
| `npx tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strictNullChecks --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck test/property.spec.ts test/dimacs.spec.ts` | Passed |
| Main-agent `npm run bench` | Passed; all eight rows, byte-identical to both earlier generated reports |
| Separate reference-evaluator/model-shape checks for hypergraph and all three random 3-SAT benchmark models | Passed; hypergraph additionally asserted exactly 2 decisions, 16 propagations, 0 conflicts, and 0 learned clauses |
| `git diff --check` | Passed |
| `git diff --exit-code HEAD -- src/expr.ts src/compile.ts src/index.ts test/helpers.ts package.json package-lock.json` | Passed; API, compiler, formula/generator code, and dependencies remain unchanged |
| `git diff --cached --stat` | Empty; nothing staged |

Coverage printed by the full suite: `src/compile.ts` 98.46% lines, `src/solver.ts` 98.05% lines. Only the existing Node/tsx `module.register()` deprecation warning appeared; it did not fail a command.

Before and after the main benchmark run, `git hash-object` returned identical values for the pre-existing working-tree baseline (`db759f95c491e685f27ed12039897dcb10c8e4a1`), raw report (`693f45d38aae1877eb6291c1ba2058252e3caf10`), Markdown report (`44de463c6f5d6e3423a667587349bf62a066b379`), and solver (`578d2a9bf7a5a78ad3e7e79d3944dc7252e362be`). No solver changes were needed or made for this ticket. Existing uncommitted Phase-2 changes were preserved, including the authorized two-decision hypergraph behavior. The benchmark intentionally requires the pinned Phase-1 Git history and fails if that reference is unavailable rather than silently choosing a different baseline.

Historical status statement, retained verbatim and superseded by the owner-approved note above:

> **The green checkpoint does not satisfy the disputed performance acceptance.** Task-884f remains `in_progress`, with a blocker note and a FAILURE report. No acceptance criterion was rewritten or waived, and no future-phase implementation was started. The retained artifacts are uncommitted evidence for the parent's independent review, not a claim that the required committed-output review or the phase has completed. The unresolved orders-of-magnitude/infeasibility claims must be resolved before the ticket can be completed.

## Historical Checkpoint — PASS Under Owner-Clarified Acceptance

Revalidated after applying the owner-approved `2026-09-06T01:56:58Z` clarification. **All current task-884f requirements are satisfied.** Only documentation/evidence disposition changed on resume: two explanatory notes in `bench.ts`, regenerated JSON/Markdown reports, this review addendum, and a narrowly scoped Notes entry in `.janus/plans/plan-7748.md`. The original ticket history and superseding authorization note are preserved. No solver, test, budget, fixture, counter, or baseline changes were needed or made on resume.

### Acceptance Review

1. **Property gate:** the unchanged 512-seed harness passes, with its >=500-distinct-AST assertion, all five constructors, three repeated single-solve verdicts per input, independent reference/model checks, exact enumeration checks, assumption subsets, and fixed battery.
2. **PHP regressions:** both fresh runs per case prove UNSAT and have identical complete counters. PHP(7,6) remains at 723 conflicts/722 learned clauses under the fixed 7,230 cap; PHP(8,7) remains at 3,627 conflicts/3,626 learned under 36,270. UNSAT is justified independently by the pigeonhole principle; only the 10x resource bounds are calibrated. Budget exceptions fail rather than becoming UNSAT results.
3. **Authentic comparison:** both benchmark runs retain all six actual Phase-1 rows and both larger Phase-2-only rows, with the pinned original Git blob, full raw counters, signed deltas, correctly directed ratios, and source/fixture fingerprints. Every measured counter is unchanged from the historical run; only the explanatory notes and corresponding benchmark-source fingerprint changed. Missing data is still not interpreted as timeout or infeasibility.
4. **Behavior and current performance acceptance:** PHP learning is engaged (27, 146, 722, and 3,626 learned clauses across the PHP series). Hypergraph parity remains exactly 2 decisions/16 propagations/0 conflicts/0 learned clauses. The small-PHP decision/conflict ratios remain 1.34x/1.86x and 1.92x/2.55x, not orders of magnitude. Full tooling is green; public API, algorithm, PLE scope, counter semantics, determinism, and zero runtime dependencies are unchanged. The future performance objective `objv-b2ca` remains independent and unrealized.

### Fresh Verification

| verification | result |
| --- | --- |
| `npm run build` | Passed |
| `npm run check` | Passed; 19 files, no lint or format fixes needed |
| `npm test` | Passed; 430/430 tests, 45 suites, no failures or skips; expanded property suite included |
| `npx tsx --test './test/property.spec.ts' './test/dimacs.spec.ts'` | Passed; 22/22 tests |
| `npx tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strictNullChecks --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck test/property.spec.ts test/dimacs.spec.ts test/bench.ts test/bench-comparison.spec.ts test/php-regressions.ts` | Passed |
| `npm run bench` twice | Passed; eight completed rows each; byte-identical current reports |
| Separate fresh reference-evaluator/model-shape checks for hypergraph and random 3-SAT seeds 42/43/44 | Passed; hypergraph also explicitly asserted exactly 2/16/0 with no learning |
| `git diff --check` | Passed |
| `git diff --exit-code HEAD -- src/expr.ts src/compile.ts src/index.ts test/helpers.ts package.json package-lock.json` | Passed |
| `git diff --cached --stat` | Empty; nothing staged |

Existing hypergraph unit assertions retain their `propagations >= 10` threshold; exact 16-propagation parity was separately confirmed by both live benchmarks and the fresh explicit stats check. Coverage remains 98.46% lines for `compile.ts` and 98.05% for `solver.ts`. The existing Node/tsx deprecation warning is non-failing.

### Current Artifact Identity And Preservation

These hashes identify the post-clarification reports, rather than the historical report hashes above. The two current runs had identical Git blob hashes (`git hash-object`): JSON `ab6e6fb98a55b6bcf8e355657f98722e6fe3c06e`, Markdown `6cacd73df0f46ed84c1558977c20826862eaf396`. SHA-256 values were also recorded:

| file | current SHA-256 |
| --- | --- |
| test/phase2-benchmark.json | 645cd1195379e811e5fcca5eff0bc3fd6bd75fea224800cb3a8568a50d44b2a5 |
| test/phase2-benchmark.md | fd0c19e2611b25d83155be790f2b647e69aa2d54e7568697009b767207bab2c3 |
| test/baseline.json (preserved incoming working-tree file; not the comparison reference) | 6828679df735765cf3d9a4ede04333366742efe7ff5899fc5fdb823425d9ab9a |
| src/solver.ts (preserved incoming Phase-2 implementation) | cee5031d304b5dacd9d8ed0a4de0b8908c4bd1ae5edd5f528aca79c0c85a12a1 |

Before/after Git blob hashes also matched for all 17 checked solver/API/compiler, fixture/helper, existing test, budget, and package files. The only changed benchmark-source fingerprint is attributable to the two owner-clarification notes. The original comparison reference remains `7037f823d192dc3cf2dc9119c8063781e143113c:test/baseline.json`, blob `489af8c72ed9c37befa806ccef03404d0a818e61`.

**Remaining disposition:** no unresolved blocker under the owner-clarified task acceptance. The original orders-of-magnitude and Phase-1-infeasibility claims remain unproven, not retroactively achieved; their future goals belong solely to `objv-b2ca`. No additional objective or ticket was created, and no other ticket was started. The artifacts are left uncommitted for the parent's independent phase verification; no staging, commit, amendment, push, or PR was performed. This successful task checkpoint does not claim that the parent's phase verification or commit has already occurred.

## Test-Harness Repair Checkpoint

SUCCESS for the two scoped harness repairs requested after the verifier's `2026-09-06T02:17:57Z` FAILURE. `task-884f` remains `in_progress` for the parent to close and the original phase verifier to recheck. Earlier completion claims above are historical, not independent approval. No production algorithm, API, fixture, conflict budget, counter, dependency, or performance acceptance was changed.

### Repairs And Independent Checks

- Assignment enumeration, consistent subsets, contradiction shrinking, and extension merging now define own data properties for arbitrary string names without invoking inherited setters. Records still have `Object.prototype`, not a substituted null prototype. Reference variable reads reject missing, inherited, Boolean-valued, and UNSET inputs instead of silently classifying them.
- Canonical model keys encode sorted name/value tuples as JSON. The previous delimiter encoding collided for `{ a: FALSE, b: TRUE }` and `{ 'a=0,b': TRUE }`; a negative regression now establishes distinct keys and a positive permutation check establishes order independence. Model comparisons use strict equality, including values and prototypes.
- Both assumed and unassumed property enumeration use one independently testable validator: exact own enumerable string keys, ordinary public prototype, numeric TRUE/FALSE only, reference-formula satisfaction, strict per-entry assumption extension, exact count, no duplicates, and order-insensitive strict model equality. Reference extension filtering is checked separately, including ignored UNSET entries and rejection of inherited or coerced values.
- Hand-computed positive/negative truth tables and assumption checks cover `__proto__`, `constructor`, `toString`, `hasOwnProperty`, the empty name, an integer-like name, delimiter-bearing names, and escaped quote/backslash/newline/Unicode names. Fixed public-API cases check both literal polarities, compatible and incompatible assumptions, ignored UNSET, UNSAT formulas, and ordinary own-key model shapes without obtaining expectations from either solver.
- Seven malformed-model cases are tested at BOTH positions of an assumed two-model enumeration: Boolean TRUE, Boolean FALSE, UNSET, missing key, extra key, falsifying model, and assumption violation. Assertions check the specific failing contract, so strict set comparison alone cannot conceal a missing formula or assumption check. Separate helper negatives cover strings coerced to numbers, wrong counts, duplicates, inherited/missing keys, null prototypes, hidden properties, and symbol keys.
- All original 512 seed/AST pairs are retained unchanged, with a second 512-seed arbitrary-name corpus. Each pool has 509 distinct ASTs, all five constructors, at most eight variables, 494 satisfiable formulas, 988 consistent subsets, and 924 contradictory subsets. Every pool name appears in formulas and in both kinds of assumptions. That is 1,024 formula cases and 3,824 assumption samples, with three fresh single solves of every applicable input and independent expected truth computed before solver calls.

The first helper-only regression run, before the helper repair, failed 8/48 tests. It reproduced the lost `__proto__` assignments, erroneous consistent-assumption exception, and Boolean/numeric comparison acceptance, as well as the additional key-encoding/read/shape blind spots. After repair all 48 helper tests pass. No production solver output was mutated or used as reference truth.

### Validation Results

| command or check | result |
| --- | --- |
| `npx tsx --test --test-reporter spec './test/helpers.spec.ts' './test/property.spec.ts' './test/index.spec.ts'` | Passed; 111/111 tests, 24 suites, both complete 512-seed corpora |
| `npm run build` | Passed |
| `npm run check` | Passed; 19 files after ordinary formatting corrections via `apply_patch` |
| `npm test` | Passed; 472/472 tests, 47 suites, no failures, skips, cancellations, or todos |
| No-emit TypeScript check of the four touched test/helper files, ESNext/Bundler, ES2022, strict null/optional and unused checks | Passed |
| `npm run bench` twice | Passed; all eight rows, byte-identical JSON and Markdown reports |
| Reference-only in-memory corpus audit | Passed; all original ASTs unchanged, counts and name coverage as recorded above |
| In-memory report provenance comparison | Passed; restoring ONLY the prior helper fingerprint reproduces incoming JSON Git blob `ab6e6fb98a55b6bcf8e355657f98722e6fe3c06e` |
| `git diff --check` | Passed |
| Production/frontend/compiler/package preservation and incoming untouched-file hashes | Passed; no changes from this repair |
| `git diff --cached --stat` | Empty; nothing staged |

Full-suite line coverage remains 98.46% for `src/compile.ts` and 98.05% for `src/solver.ts`. The existing Node `v26.8.1`/tsx `DEP0205` warning is reported, not suppressed. No new production correctness issue was found by these checks.

### Artifact Identity And Scope

Artifact parent directories were inspected with `ls` before producing outputs. Both benchmark runs retained the pinned original Phase-1 blob `489af8c72ed9c37befa806ccef03404d0a818e61`. Every verdict, fixture fingerprint, budget, counter, comparison, and interpretation note is unchanged; only the `test/helpers.ts` source fingerprint changed to SHA-256 `6b4d2556063f52a568fad5e1c87a5ce31789c97088640feb245b3bb636d71d39`.

| file | Git blob hash after both benchmark runs |
| --- | --- |
| `test/phase2-benchmark.json` | `e838c35c6d99fde7c73627254ecec18255958c58` |
| `test/phase2-benchmark.md` | `f2a48a8dfa7b82f8a9bc17e9243490496cc64d12` |
| `test/helpers.ts` | `824da88c43094415c677649e49ee3fba3991e6a0` |
| `test/baseline.json`, preserved exactly as found | `db759f95c491e685f27ed12039897dcb10c8e4a1` |
| `src/solver.ts`, preserved incoming Phase-2 work | `578d2a9bf7a5a78ad3e7e79d3944dc7252e362be` |

Hypergraph remains 2 decisions/16 propagations/0 conflicts. PHP(7,6) and PHP(8,7) remain UNSAT at 723 and 3,627 conflicts, with learning, under unchanged 7,230 and 36,270 caps. Small-PHP decision/conflict ratios remain 1.34x/1.86x and 1.92x/2.55x; no Phase-1 infeasibility or orders-of-magnitude improvement is claimed.

Repair scope: `test/helpers.ts`, `test/helpers.spec.ts`, `test/property.spec.ts`, four strict enumeration assertions in `test/index.spec.ts`, the regenerated JSON/Markdown reports, this evidence addendum, and a note on existing `task-884f`. All other incoming uncommitted work is preserved. No ticket/objective creation, future-phase work, staging, commit, amendment, push, or PR occurred. Remaining work is parent disposition and independent Phase-2 reverification; commit only after the verifier succeeds.

## Independent Phase-2 Reverification

The original phase verifier independently approved `plan-7748` Phase 2 and recorded SUCCESS on `task-884f` at `2026-09-06T04:57:58Z`. Both original blockers are resolved: arbitrary-name reference enumeration/assumptions preserve own numeric properties, and every assumed and unassumed enumeration result receives strict shape, formula, assumption, count, duplicate, and set checks. The general helper-key collision repair is also covered. No production SAT/UNSAT counterexample or unresolved Phase-2 acceptance issue was found.

- Fresh `npm run build`, `npm run check`, and `git diff --check` passed.
- Fresh `npm test` passed 472/472 tests across 47 suites, without failures or skips. The targeted helper/property/API run passed 111/111 tests, and both repair-scoped and expanded full-strictness TypeScript checks passed.
- Both 512-case pools were independently checked: 509 distinct ASTs per pool, all original seed/AST pairs retained, 3,824 assumption samples, and 58,832 reference truth-table rows.
- Independent diagnostics passed 4,608 raw-CNF solves, including 590 checked analyses, 28 non-chronological jumps, and 256 unary learnings. Additional own-property probes covered ten legal names, 20 hand-derived positive/negative cases, and 1,920 assumption/shrinking checks.
- Both fresh benchmark runs completed all eight rows with byte-identical reports. The verifier checked all SAT benchmark models independently, the authentic pinned Phase-1 reference, and the unchanged PHP budgets and owner-approved hypergraph parity.
- Plain-Node compiled ESM validation passed, including 10,000 ordinary iterative decisions with exact counters. Line coverage remained 98.46% for `compile.ts` and 98.05% for `solver.ts`.
- The existing Node/tsx `DEP0205` warning remains disclosed. An exploratory partial-strictness TypeScript command exposed an older test's mode-dependent `never[]` inference; compiler-API analysis isolated the mode difference, and the identical expanded file set passed full `--strict` without edits or suppression. This was not a configured-build or runtime failure; details are retained in Janus.

The verifier made no implementation, test, fixture, expectation, counter, or baseline changes. The parent reviewed the complete phase diff and artifacts after approval. The pre-existing `test/baseline.json` working-tree edit is intentionally excluded from the Phase-2 commit and preserved separately; benchmark comparisons continue to use the authentic Phase-1 reference. Future algorithmic performance goals remain independently tracked in `objv-b2ca`, not claimed as achieved here.
