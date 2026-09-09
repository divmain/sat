# v3.0.0 Final Acceptance Review — task-080d (release validation) and task-9aa2 (acceptance verification)

Release validation record for `@divmain/sat` **3.0.0** under plan-d285. This is an evidence
artifact in the style of the phase reviews: what ran, where, and what it proved — plus the
known limitations. It is not publication approval: per the controlling instruction for this
task, **no commit, tag, push, PR, or npm publication was performed**, and every change below
remains uncommitted in the working tree alongside the prior task-2965 documentation work.

## Candidate Identity and Honest Overlay

The validated tree is HEAD plus an explicit, uncommitted overlay. It is **not Git-status-clean**
and is not claimed to be.

| Identity | Value |
| --- | --- |
| Base HEAD | `91e61aa8011f27cde44234fa21646c66cc5ca660` (`feat: add rich results, async solving, and cardinality constraints`) |
| Overlay paths | `AGENTS.md`, `README.md`, `src/compile.ts`, `src/index.ts`, `src/solver.ts` (task-2965 docs/comment work); `package.json`, `package-lock.json`, `test/release-smoke.mjs` (this task's 3.0.0 version bump) |
| Overlay SHA-256 | `AGENTS.md` b7cb1682…, `README.md` a50771b0…, `src/compile.ts` f709c6d4…, `src/index.ts` 074dc31a…, `src/solver.ts` 682d8176…, `package.json` 93e6beec…, `package-lock.json` 4b859f3f…, `test/release-smoke.mjs` 7ba5eeab… |
| Isolated candidate | `…/T/opencode/sat-080d-release-20260909/candidate` — fresh `git clone --no-local`, full history (all six pinned commits `7037f82`/`ade64e5`/`53a059c`/`ae1a4fe`/`2ba0a39`/`cd44ed1` present; `git fsck --full --strict --no-reflogs` clean), no `node_modules`/`dist`/`.janus` before fresh `npm ci`; the eight overlay files were then copied in and verified byte-identical to the workspace |
| Version bump | `package.json` and **both** `package-lock.json` locations → `3.0.0`; `test/release-smoke.mjs` manifest assertion → `'3.0.0'`; all three changed **before** any benchmark/pack artifact was produced |

Environment: Node **v26.8.1**, npm **12.0.2**, locked TypeScript **5.4.5**, macOS arm64.
`npm ci` under npm 12 prints `allowScripts` warnings (biome/esbuild/fsevents postinstalls
blocked); all gates passed regardless, and the development-tree audit warnings remain
disclosed, not suppressed. The tsx `DEP0205` notice remains visible on harness runs.

## Gate Results

| Gate | Workspace | Isolated candidate |
| --- | --- | --- |
| `npm ci` | (pre-existing install) | PASS, fresh isolated `node_modules` |
| `npm run build` | PASS | PASS (clean `dist/`) |
| `npm run check` (biome lint+format) | PASS, 55 files, no fixes | PASS |
| `npm run typecheck` (strict src+test command) | PASS | PASS |
| `npm test` (full suite incl. enumeration stress) | **958 tests / 136 suites, 0 fail/cancel/skip/todo**, 133.5 s | **958 tests / 136 suites, 0 fail/cancel/skip/todo**, 134.2 s |
| Enumeration stress gate | 59,049 models; peak live **120 < 256**; 922 deleting rounds; 29,413 deletions | same |
| `npm run bench:legacy` (gates) | PASS; 19 of 48 counter deltas disclosed non-fatal; nothing written | PASS, identical deltas |
| `npm run bench` (v3 gates) | PASS; 285 disclosed deltas non-fatal; wrote `test/v3-benchmark.{json,md}` | PASS, identical; deterministic content byte-compared equal between locations (only environment paths/wall times differ) |
| `git diff --check` | clean | clean |

### Coverage (test reporter line %, read from both runs)

| Module | Line % | Required |
| --- | --- | --- |
| `src/expr.ts` | **100.00** | ≥90 |
| `src/compile.ts` | **99.76** | ≥90 |
| `src/index.ts` | **100.00** | ≥90 |
| `src/solver.ts` | **99.20** | ≥90 |

## Benchmark Evidence and Corpus Deltas

- **Legacy verifier (`bench:legacy`, gates mode):** authentication of the frozen Phase-1/2/3/4
  references and pristine-v2 compiled snapshots passed; all verdicts, oracles (hypergraph
  2/16/0), and caps (PHP 7,230/36,270) held. The 19 disclosed counter deltas are the known
  Phase-2/3 changes; large PHP improved (php_8_7 conflicts 5,946 → 3,152). Nothing written.
- **v3 harness (`bench`, gates mode):** all **23 sealed scenarios** ran at their immutable
  calibrated caps; every verdict, outcome, per-call status, and the pairs(8) model-set digest
  matched the sealed v2 baseline (**hard checks**; pairs8 6,561/6,561 models). No failures.
- **285 disclosed deltas (non-fatal, by design):** 250 counter deltas (search statistics and
  per-call incremental32 counters), 27 model-digest/ordering differences (different valid
  first models and enumeration order; the order-insensitive set is hard-compared and equal),
  3 compiled-output deltas limited to `xor8`/`xor12`/`xor16` (hash-consed operand sharing from
  the compiler task), and the remainder small status-adjacent fields. Conflict totals on the
  hard rows improved (php_9_8 38,370 → 19,666; random3_n250_seed3 126,003 → 63,436);
  disclosed regressions stand on some easy rows (e.g. random3_n200_seed2 2,162 → 12,685).
  Per-task analysis lives in `test/v3-benchmark-review.md`; the regenerated machine artifacts
  now carry the 3.0.0-tree source hashes and HEAD context `91e61aa`.

## Fresh Tarball and Consumer Checks

`npm pack` ran in the candidate from a **clean build state** (`dist/` deleted and rebuilt
first; `npm pack` does not build automatically).

| Artifact | Value |
| --- | --- |
| Tarball | `…/sat-080d-release-20260909/divmain-sat-3.0.0.tgz`, **138,915 bytes**, SHA-256 `e07aff4c63f04217c2241808debbb84b2b80861e51a145c7f410a0b6f3f7fec0` |
| Contents | exactly 14 files: `dist/{compile,expr,index,solver}.{js,d.ts,js.map}`, `package.json`, `README.md`; no `.d.ts.map`, no tests/Janus data |
| Release evidence | `…/consumer/release-evidence.json`, SHA-256 `e35570e0…`; status `passed` |

`node test/release-smoke.mjs <tarball> <new-consumer>` **passed**: offline
`--ignore-scripts` install into a fresh consumer outside the repo; installed manifest version
asserted **3.0.0** (the bumped assertion); pure-ESM export map, `sideEffects: false`,
`files: ["dist"]`, empty dependencies, no `engines` all re-verified; JS and `.d.ts` import
closures exact; strict TypeScript consumer (`strict`, `exactOptionalPropertyTypes`,
`noUnusedLocals/Parameters`, `skipLibCheck: false`, NodeNext) compiled clean with **49
negative `@ts-expect-error` checks**; export surface confirmed at **16 runtime values** and
**13 type-only** exports (`Value` alone in both namespaces); the plain-Node ESM runtime probe
and all **9 runnable README examples** passed, including the real-scheduler async group
(yields forced at `yieldQuantum: 64`, budget `'unknown'`, pre-aborted signal, handle reuse)
and the byte-exact hypergraph oracle output `2 16 0`.

### Process-Less Real-Yield/Scheduler Smoke

A second, separate consumer installed the same tarball, then ran a probe that deletes
`globalThis.process` **before** any library load, dynamically imports the installed package,
wraps `MessageChannel` to count scheduler activity, and solves deterministic fixtures at the
minimum real quantum (`yieldQuantum: 64`; this Node has no `scheduler` global, so yields use
one owned `MessageChannel` per yield):

```text
PROCESSLESS_SMOKE_OK channels=3        (exit 0, natural exit in 0.08 s)
```

The guarded `globalThis.process?.env?.SAT_DEBUG` module-load read tolerated the missing
global; the 96-variable single solve returned `sat` with a complete verified model and the
two-model enumeration completed; **3 real event-loop yields** were observed; and the process
exited naturally and immediately — any leaked port or listener would have pinned the event
loop. Probe source retained at
`…/sat-080d-release-20260909/processless-consumer/processless-smoke.mjs` (SHA-256
`3e212d9f…`). This is a platform-global/scheduler smoke, **not** a claim of testing every
browser or every Node version.

## Known Limitations

- Single exercised environment (Node v26.8.1 / macOS arm64 / TypeScript 5.4.5 / npm 12.0.2);
  the package intentionally has no `engines` field and no per-version testing claim is made.
- Benchmarks compare counters/models against the sealed v2 baseline; wall times are
  informational only and never gated. Results are not scalability, total-memory, or
  default-reduction-engagement evidence, and disclosed counter regressions on some rows stand.
- The v3-corpus compiled snapshots for the three XOR chains differ from the v2 baseline by
  design (compiler hash-consing); input identities, caps, and verdicts are unchanged.
- The candidate is an honest uncommitted overlay on `91e61aa`, not a Git-clean committed tree;
  the committed-tree confirmation, and any tag/push/publish, remain out of scope without an
  explicit request. This review was written after the gates above and is itself uncommitted;
  it is not an input to any gate it records.

## Plan-Level Acceptance Verification — task-9aa2

task-9aa2 independently re-verified every plan-d285 acceptance criterion against the same
tree (HEAD `91e61aa` + the unchanged overlay). The working tree was first confirmed
**byte-identical** to the tree validated above: all eight recorded overlay SHA-256 prefixes
match the current files, and no other paths are modified. Every gate was then re-run in the
workspace (Node v26.8.1 / macOS arm64), and the frozen artifacts, history, and source/test
contracts were inspected directly. Result: **all 11 plan-level criteria PASS.**

### Re-run Gate Results (task-9aa2, this workspace)

| Gate | Result |
| --- | --- |
| `npm run build` | PASS |
| `npm run check` (biome lint+format) | PASS, 55 files, no fixes |
| `npm run typecheck` (strict src+test) | PASS |
| `npm test` | **958 tests / 136 suites, 0 fail/cancel/skip/todo**, 133.8 s |
| Coverage (reporter line %) | `expr.ts` 100.00, `compile.ts` 99.76, `index.ts` 100.00, `solver.ts` 99.20 — all ≥90 |
| `npm run bench:legacy` (gates) | PASS: authentication, verdicts, hypergraph oracle 2/16/0, PHP caps 7,230/36,270; 19/48 counter deltas non-fatal; nothing written |
| `npm run bench` (v3 gates) | PASS: immutable inputs, outcomes, caps, per-call verdicts all hard-checked; 285 disclosed deltas non-fatal |
| `git diff --check` | clean (re-run after this section was added) |
| Fresh `npm pack` from clean `dist/` | **byte-identical tarball**: 138,915 bytes, SHA-256 `e07aff4c63f04217c2241808debbb84b2b80861e51a145c7f410a0b6f3f7fec0` — identical to the task-080d artifact above |
| `node test/release-smoke.mjs` (fresh consumer, offline `--ignore-scripts` install) | PASS: installed manifest 3.0.0, pure-ESM export map, `sideEffects:false`, `files:["dist"]`, empty dependencies, no `engines`, exact JS/`.d.ts` import closures, strict-TypeScript consumer with 49 negative `@ts-expect-error` checks, plain-Node ESM runtime, all 9 runnable README examples |
| Process-less real-yield smoke (fresh probe in the installed consumer) | `PROCESSLESS_SMOKE_OK channels=1`, exit 0, natural exit in 0.07 s — `globalThis.process` deleted before load, installed package imported dynamically, verified complete sat model + complete 2-model enumeration at `yieldQuantum: 64`, ≥1 real MessageChannel yield, no leaked scheduler resources |

The verification `npm run bench` rewrote `test/v3-benchmark.{json,md}` as designed (the
harness writes on success): candidate source hashes and HEAD context are identical to the
values recorded above, the 285 disclosed deltas and every hard gate are unchanged, and only
informational wall-time cells jittered. No other prior working-tree content was touched.

### Criterion-by-Criterion Evidence

1. **Platform-neutral, fast-by-default runtime — PASS.** `src/` contains no `node:` imports
   (`from 'node:` / `from "node:` search empty) and exactly one `process` reference: the
   guarded `globalThis.process?.env?.SAT_DEBUG === '1'` at `src/solver.ts:156`, matching the
   exact-string allow-list in `test/platform-guard.spec.ts:18`; audits initialize once at
   module load and are opt-in; `setDebugAssertions` is exported from `src/solver.ts` only,
   never re-exported from `src/index.ts`; the suite runs audits globally via the
   `--import ./test/debug.ts` preload in every test script. The audits-on/off overhead
   contrast (~2.8×; 375–379K props/s vs ~1.05–1.07M props/s) is recorded informationally in
   `test/v3-benchmark-review.md` and is never unit-test gated. Direct runtime proof: the
   process-less smoke above imports and solves with `globalThis.process` deleted.
2. **Honest performance evidence — PASS.** Frozen Phase-1/2/3/4 artifacts, `test/v3-baseline.json`,
   `test/legacy-compiled-cnf.json`, and the entire `test/v3-baseline-overlay/` tree are
   unmodified (zero changed paths under `git status`); the overlay is never imported from
   outside itself (only authentication path-strings reference it). `test/v3-baseline.json`
   records `baselineCommit: ae1a4fe`, `recorderSealCommit: 2ba0a39`, `overlay: true`, and
   per-source Git blob + SHA-256 provenance; each scenario carries distinct `inputSha256` /
   `compiledSha256` identities and separate `calibration` trials vs final-cap measurements.
   `bench:legacy` re-authenticated all frozen references and passed in gates mode with 19/48
   disclosed deltas; the v3 harness passed with 285 disclosed deltas analyzed in
   `test/v3-benchmark-review.md`. The 32-call incremental scenario shares one calibrated cap.
   No fixture was changed and no measurement invented.
3. **Modern, provenance-safe learning — PASS.** Iterative recursive minimization
   (ccmin_mode=2 over an explicit stack, `src/solver.ts:1129`); per-variable `rootBasis`
   bitmask with assumption/PLE bits (`src/solver.ts:124,770-774,2436,2487`); only
   base-derived (`rootBasis === 0`) root literals drop (`:1028,:1152`); LBD over distinct
   non-zero levels of the final minimized clause (`:1109-1111`), so retained tainted roots
   never inflate LBD (`test/property.spec.ts:666`, `test/reduction.spec.ts:318`).
   Unconditional permanent-database entailment checks remain intact, including base models
   violating the active assumptions (`test/learning.spec.ts:465-546`, e.g. the
   `(¬a∨¬x)`-not-`¬x` test with `assertEntailed(base, learned)`). Core-erasure (seeded
   rejection, `test/cores.spec.ts:50-109`) and tainted-implication witnesses
   (`test/cores.spec.ts:34-37`, `test/learning.spec.ts:622-763`, `test/index.spec.ts:281`)
   are covered and green.
4. **Retention and restarts — PASS.** Two-tier glue (LBD≤2, never a candidate) / reducible
   deletion with stable activity sort and `claInc *= 1/0.999` decay (`src/solver.ts:1493-1518`),
   plus dynamic LBD tightening with ≥2-improvement hysteresis, never increasing
   (`:996-1003`). `EmaRestartPolicy` (α=0.25/0.02, first-LBD seeding, interval 32, ratio
   1.25, 32-conflict blocking sampled after the conflict transaction) is the default;
   `LubyRestartPolicy` remains selectable only via the internal `restartPolicy` option
   (`:349,:400,:640-689`). The unchanged 59,049-model enumeration stress gate passed in the
   full suite with its pinned bounds (`peakLive < 256`, threshold 32, deletion rounds > 1;
   `test/enumeration.spec.ts:960-1036`).
5. **Propagation engineering — PASS.** Both experiments have documented keep/drop outcomes
   in `test/v3-benchmark-review.md` (lines 320-409): Experiment A (blocker-literal watch
   entries with cross-linked twins, single `litValue` per visit) **KEPT with exact parity**;
   Experiment B (dedicated binary-clause watch lists, implicit propagation) **KEPT as a
   disclosed-delta variant** with written analysis (php_8_7 −42% conflicts, honest php_7_6
   +25% regression, 8/23 v3 rows moved, verdicts/caps/model-sets intact). Both were measured
   against task-local captures of the same pre-edit tree (received-artifact byte-identity
   checked first), and the n=400 probe profile plus audits contrast are recorded
   informationally. Blocker entries and drained-first binary lists are present in
   `src/solver.ts` with per-visit debug audits.
6. **Compiler integrity — PASS.** Compilation-scoped identity memoization plus structural
   hash-consing with multiplicity/order-preserving keys, same-kind flattening, and total
   constant folding on compiler-owned canonical nodes (`src/compile.ts:15-26,171,252-278,401-416`);
   caller ASTs are never mutated (snapshot-ownership tests, `test/compile.spec.ts:412` area,
   `test/add.spec.ts:293-299`). Named-universe preservation is tested
   (`test/compile.spec.ts:367-391` folded-away variables stay; cardinality edge folds keep
   the universe, `test/cardinality.spec.ts:294`). Extension correctness plus propagation
   refutation of invalid total named assignments are asserted for expression gates
   (`test/compile.spec.ts:435-453`) and for asserted counters with explicitly unset
   auxiliaries allowed (`test/cardinality.spec.ts:438-464`); nested outputs are fully
   reified through the totalizer. PG stays deferred as a scope decision with the false
   counterexample explicitly retired (`src/compile.ts:43-45`,
   `test/compile.spec.ts:435-445`). Legacy complete compiled snapshots compare equal to the
   authenticated v2 references inside the passing `bench:legacy` gate.
7. **3.0 API as specified — PASS.** Every entry point returns rich results (asserted shapes
   throughout `test/index.spec.ts`, `test/cores.spec.ts:126-150` for `core: {}` exactly when
   assumption-independent/no assumptions). Hard positive caps with the atomic final
   transaction, the explicit budget-zero startup exception, the budget-1
   second-root-conflict boundary witness, verdict > abort > budget precedence, and
   enumeration-wide accounting are all tested (`test/budget.spec.ts`, incl. lines 17, 99-150,
   261, 312). Async errors reject Promises and zero stats before rejecting
   (`test/async.spec.ts:83-116`); yields reach safe points without per-model allowance
   resets; `async ≡ sync` for identical non-aborted histories
   (`test/async.spec.ts:336-360`). Cores satisfy `core ⊆ assumptions` and brute-force
   `base ∧ core` UNSAT on every seeded draw (`test/cores.spec.ts:162`,
   `test/property.spec.ts`). `add()` is failure-atomic with unchanged universe/behavior after
   failed adds (`test/add.spec.ts:230-264`) and snapshot-owned against caller-AST mutation
   (`:293-299`), with deterministic history-dependent indices. Cardinality preserves the
   pinned multiplicity and asserted/nested encoding contracts (`test/cardinality.spec.ts`,
   38 tests). The installed-tarball export surface is pinned at 16 runtime + 13 type-only
   exports by the passing release smoke.
8. **Soundness invariants — PASS.** PLE is enabled only for single-shot
   `getSolution`/`getSolutionAsync` (`enablePle: true` at `src/index.ts:181,223` only; `false`
   at `:275,302,326`); assumption validation/replay/cancellation semantics are unchanged and
   covered by the incremental suites; enumeration completeness is cross-validated against
   brute force in the preserved 512-seed × two-pool property battery
   (`test/property.spec.ts:3,64,627`), with determinism under fixed seeds asserted
   (`:792`); cardinality arrived as a separate versioned stream (`cardinality stream v1`,
   `:852-965`) without re-rolling old cases. `dependencies` is `{}` (zero runtime
   dependencies); the solver core is iterative (resumable `searchSlice` driver loops,
   explicit-stack minimization; 59,049-model and deep-chain stress pass without stack
   recursion — compiler recursion over expression nesting is the documented, accepted
   exception); no wall-clock primitives appear in any spec file.
9. **Quality gates — PASS.** Every gate in the table above is green on the final
   version-3.0.0 tree; coverage is ≥90% lines for each `src/` module from the reporter
   (99.20-100.00%); the version bump (`package.json` + both lockfile locations + the
   release-smoke assertion) preceded all packing; the fresh-tarball checks (plain Node ESM,
   strict TypeScript with 49 negative checks, all 9 runnable README examples, and the
   process-less real-yield/scheduler-cleanup smoke) were re-executed here against a
   byte-identical 3.0.0 tarball; the candidate overlay is reported honestly (this file and
   the table above); `git diff --check` is clean.
10. **Documentation complete — PASS.** `README.md` documents the full 3.0 API with a real
    v2→v3 migration table (`README.md:437`, before/after rows for every changed
    signature/options bag plus additive async/`add()`/cardinality rows and the
    history-dependent-restart-timing disclosure) and retains the v1→v2 table
    (`README.md:418`); Environments documents platform neutrality, `SAT_DEBUG`, the yield
    chain, and the ambient `AbortSignal` requirement; Limits states the no-wall-clock-claims
    policy and the iterative-core/compiler-recursion boundary. `AGENTS.md` reflects the final
    module layout, commands (`typecheck`, `bench`, `bench:legacy`), the six-commit
    full-checkout list, corpus policy, coverage expectations, and the refined hard
    constraints (history-dependent sorted indexing under `add()`; PLE scoped to
    single-shot).
11. **Deferred scope — PASS.** No streaming/projected enumeration, raw CNF entry, aux-only
    preprocessing, PG encodings, DRAT, or MaxSAT exists in `src/` (only a comment noting the
    absence of a streaming API). Version is **3.0.0** in the manifest, both lockfile
    locations, and the installed tarball. This review is the final acceptance review
    artifact. Git tags remain the pre-existing v1.x set only — **no v3 tag, no commit, no
    push, no PR, and no npm publication was performed** by this task.

### Verdict

All 11 plan-level acceptance criteria are satisfied with direct, re-executed evidence.
plan-d285 is accepted at version 3.0.0 on the honest uncommitted overlay described above;
publication mechanics remain explicitly out of scope.
