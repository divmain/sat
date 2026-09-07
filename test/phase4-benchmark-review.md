# Phase-4 Release Documentation, Packaging, and Validation Review

## Current Independent Disposition

**SUCCESS — original verifier resumed; plan-7748 Phase4 independently approved for the parent
phase commit.** The exact historical public-enumeration regression is retained and passes; the
original failure was resolved by the authorized GENERAL-agent repair, not waived. Task-2c7f is
complete. See [current independent verification](phase4-acceptance-review.md#current-independent-phase-4-disposition)
for the nine-criterion map, all commands, supplemental probes, and remaining post-commit gate.

The verifier independently reconstructed and freshly executed the 46-file tree
`8fe8b56bc567a4dd5ca15945cb73e0c59cbf093e` in a new full-history `--no-local` clone, with an explicit
private-index overlay and fresh install/build state. Workspace and fresh candidate each pass
**669 tests / 78 suites**, build/check/strict types/diff checks, and explicit compiler **99.50%** /
solver **98.65%** line coverage. A newly packed and installed tarball passes plain Node ESM,
strict NodeNext with **39 negative checks**, and all six actual README examples. It is 41,105 bytes,
SHA-256 `6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41`, byte-compared with
the earlier repair artifact. Neither the source isolation nor these annotations are a committed
Git-clean checkout.

New verifier scratch is `/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-phase4-verifier-20260906`.
Its **two new actual benchmark runs** retain separate `candidate-bench-{1,2}.report.{json,md}`
pairs. They reproduce all current report bytes: **48/48 Phase3 counter parity**, **nine Phase2
PHP regressions**, and **834/5946 conflicts within unchanged7230/36270 caps**. Both writes follow
real CLI solves and immediate hash/source-preservation assertions. The repair agent's six pairs
were audited separately as prior evidence. The older task-aa07 retention limitation remains
historical; none of these comparisons measures incremental/enum performance or total memory.

Only the three evidence records are annotated after that executed tree. Their actual final tree
and differences are in the new scratch `final-annotation-inputs.json`, with final checks in
`verification-results.json`; 8fe8b56... is not mislabelled as the full post-annotation tree.
All executable/config/test/package bytes and all frozen Phase2/3 artifacts are unchanged. Parent
commit and subsequent genuine committed fresh-checkout confirmation remain separate; objv-b2ca
is not achieved. The original failure and repair checkpoint below remain intact as history.

## Current Repair Status

The owner-authorized task-2c7f repair now retains the exact v1 worked-UNSAT enumeration expression
under `describe('getAllSolutions')` in `test/index.spec.ts:463-480`, with strict `[]` assertions
and independent AST/32-assignment truth-table proof. The independent verifier's
2026-09-06T10:40:08Z **FAILURE** was a real missing-test deficit, not a solver defect or a waived
requirement. That omission was fixed; **independent Phase-4 re-verification was pending at this
repair checkpoint and has now passed as recorded above**.

The new workspace and fresh full-history private-overlay candidate both pass build/check/test/
strict types/diff check, with **669 tests / 78 suites** and **99.50% compiler / 98.65% solver line
coverage**. The 59,049-model stress, all fixed property batteries, and conflict caps are unchanged.
The repaired execution-input tree is `0ef5b93de519281ad0a5beaae05a3d4eacb2f33b` (46 files, including
the new regular test and the existing acceptance review), not the historical 43/45-file trees.
New scratch root: `/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-2c7f-repair-20260906`.

Two real benchmark runs per location retain separate raw `.report.json` and `.report.md` copies
and verify their hashes immediately. All four new pairs match the existing Phase-4 bytes:
48/48 Phase-3 counter parity, nine honest Phase-2 regressions, PHP conflicts 834/5946 within
7230/36270. No measured counters, fixtures, provenance, or frozen Phase-2/3 artifacts were edited.
The fresh built/packed/offline-installed consumer passes plain Node, strict NodeNext with 39
negative checks, and all six actual installed README examples. New tarball equality is verified:
41,105 bytes, SHA-256 `6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41`.

See [current repair evidence](phase4-acceptance-review.md#current-repair-checkpoint) and the
manifest's `currentRepair` for hashes, raw logs, preservation, and the external final annotation
tree/second fresh-clone results. No active-index staging or commit occurred. The ticket was
`in_progress` when this repair checkpoint was written; it is now complete and independently
verified above. Any authorized parent commit and committed clean-checkout confirmation remain
separate. objv-b2ca is not achieved.

## Historical Task-aa07 Record

All candidate identities and execution counts below are the original pre-repair task-aa07
record, preserved for provenance rather than asserted as fresh measurements of the changed test.

Task: **task-aa07**, plan **plan-7748**. Release-source checkpoint: **PASS**.
This is not task-2c7f, independent Phase-4 verification, publication approval, or satisfaction of future performance objective objv-b2ca. Those remain separate. No commits, tags, pushes, PRs, registry publication, or active-workspace Git staging were performed.

## Scope and Deliverables

All five task checklist items are satisfied by actual source/package execution:

1. **Final README:** CDCL framing; complete nine-value/seven-type public surface; self-contained Basic Usage, single/all worked examples, reuse and stats examples; strict numeric own-property models; validation/empty formulas; enumeration ordering/output sensitivity/exponential and memory limits; single-shot-only PLE; incremental snapshot/replay/cache/cleanup semantics; full decision-hook contract and ported 19-variable hypergraph. Migration covers the old positional signature, `initialAssignments`, `selectNextVar`, `SelectNextVariable`, `NextVariable`, `bruteForceAllSolutions`, `getInitialAssignments`, `defaultSelect`, `allPossibleAssignments`, `dpllSolution`, `sequence`, and test-only `expressionValue`. Internal helpers are not advertised as public exports.
2. **Version/package:** package and both root lockfile versions are `2.0.0`. `dependencies: {}`, `files: ["dist"]`, ESM `main: "dist/index.js"`, and no `engines` remain. Locked dependency entries are unchanged. Installed strict NodeNext resolution succeeds using the adjacent declarations, so no speculative `types`/`exports` metadata or runtime/API change was needed.
3. **Real publish artifact:** fresh isolated build, actual `npm pack`, offline installation of that tarball into a separate consumer, then plain Node ESM and strict TypeScript validation. `*.tgz` is now ignored; the tarball exists only in preapproved scratch, not the repository.
4. **Fresh candidate gates and explicit coverage:** build, lint/format, full test suite, strict source/test types, and real benchmarks pass in both the workspace and the isolated intended-source candidate. Compiler and solver line coverage both exceed 90%; see the actual reporter values below.
5. **README consumer:** all six executable snippets were extracted from the *installed README*, copied byte-for-byte, and executed. Their actual outputs/model descriptors were checked, not merely process exit codes. Every public entry point and all seven types are exercised; exact exports and removed/internal symbols are checked.

The Installation subsection is byte-identical to HEAD. SHA-256 of the text between its heading and Basic Usage: `adfad6d04870ee8e6f357a19562672671ce854bd950cfcbb7ac2183e4673c928`.

`AGENTS.md` now describes implemented modules/APIs, actual benchmark commands, full-history and fresh-pack requirements, strict checks, long stress-test timeouts, fixed caps, and incremental assumptions/stats constraints. No hard rule was weakened.

Task-owned files: `.gitignore`, `AGENTS.md`, `README.md`, `package.json`, `package-lock.json`; `test/bench.ts`, `test/bench-comparison.ts`, `test/bench-comparison.spec.ts`; `test/release-smoke.mjs`, `test/release-consumer.mjs`, `test/release-consumer.mts`; `test/phase4-benchmark.json`, `test/phase4-benchmark.md`, this review, and `test/phase4-release-manifest.json`. No solver/compiler, fixture generator, property corpus, stress bound, or conflict-cap edit was made by this task.

## Exact Candidate and Isolation

The machine-readable [release manifest](phase4-release-manifest.json) records all **43 frozen input files** with raw-byte SHA-256, Git blob, mode, and length; the 20-file explicit overlay; command/log identities; every packed file; and README snippet fingerprints.

- Workspace: `/Users/dalebustad/dev/sat`.
- Preapproved scratch: `/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-aa07-release-20260906`. Darwin resolves this to `/private/var/...`; these are aliases for the same location, not two checkouts.
- Base HEAD: `53a059c761e9b3591b8513a03309699ecef0c889`.
- Private source tree: `8b58af7efa801254b7c3a515b0e046ea4a3e6d87` (a Git tree, **not a commit**).
- `candidate-source.tar` SHA-256: `b4a8b051a0d2e5d30e84a8650d819aa6027f4771b1c891f569f693354a34c388`.
- Full scratch `candidate-inputs.json` SHA-256: `03513d5b7f316fee06a4b5c5854df3a15d5f8f72f19da0126971a985e84eeae6`.

A temporary **private** `GIT_INDEX_FILE` was seeded with the base tree and given only the explicit overlay paths. It included every incoming incremental source/test file, not merely committed Phase 3. It did not include the unowned working baseline edit, ignored Janus files/secrets, existing `node_modules`, or `dist`. The candidate's `test/baseline.json` is the original committed blob `489af8c72ed9c37befa806ccef03404d0a818e61`; the workspace's unowned blob `db759f95c491e685f27ed12039897dcb10c8e4a1` was neither edited nor restored.

`git clone --no-local --no-checkout` made a separate full-history repository with its own Git objects. After checking out the base HEAD, the private-tree archive was extracted over it. Every candidate file was checked against the manifest; **no `node_modules`, `dist`, or `.janus` existed before `npm ci`**. The checkout was verified non-shallow and all three pinned historical commits were present. Development tools were freshly installed there; nothing from the workspace install/build directories was copied or linked.

**This candidate is an explicitly uncommitted source overlay, not Git-status-clean.** Its 20 changed/untracked paths are recorded verbatim in the manifest. That distinction is intentional and authorized: source hashes and the tarball identify the actual intended release bytes. The parent can additionally verify a Git-clean checkout after the final phase commit; an old committed Phase-3 checkout is not substituted for this proof.

This review and the manifest are post-execution records, excluded from the non-self-referential 43-file input manifest. Neither is packaged. All executable/configuration/test inputs and all ten packaged files were frozen before validation; their bytes were cross-checked again afterward, including equality of workspace build, isolated build, and installed package. The post-execution records do not change any tested release input.

## Commands and Actual Results

Environment: Node **v26.8.1**, locked TypeScript **5.4.5**, child-process/consumer npm **11.19.0**. The interactive proto shim reported npm 12.0.2; recorded child commands and the consumer use the child version, not a claimed universal npm version. Suites and benchmarks ran with `NODE_ENV` unset and `TSX_DISABLE_CACHE=1`. The external command timeout was 900 seconds; no in-test timer or cap was changed.

| Command | Workspace | Fresh isolated candidate |
| --- | --- | --- |
| `npm ci` | Existing install used for workspace checkpoint | PASS, new install; warnings disclosed below |
| `npm run build` | PASS | PASS, previously absent `dist` |
| `npm run check` (lint + format) | PASS | PASS |
| `npm test` | PASS: 668 tests / 77 suites | PASS: 668 tests / 77 suites |
| Strict source/test `tsc --noEmit` below | PASS | PASS |
| `npm run bench` | PASS twice | PASS twice; reports identical to workspace |
| `git diff --check` | PASS | PASS |
| `npm pack --json --pack-destination <scratch>` | Not used as isolation evidence | PASS; ten package files |
| `node test/release-smoke.mjs <tarball> <new-consumer>` | Not a workspace source import | PASS, actual installed tarball |
| `npm audit --omit=dev --json` | Not an extra release requirement | PASS: zero runtime vulnerabilities |

Full strict command, with cwd at the respective source checkout (the ordinary build compiles source only):

```bash
npx --no-install tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strict --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck src/*.ts test/*.ts
```

Both full test runs reported **0 failed, 0 cancelled, 0 skipped, 0 todo**. The 59,049-model stress, fixed property batteries, and incoming incremental tests ran unchanged. The increase from incoming 632 to 668 tests is 36 additional benchmark-infrastructure tests; the benchmark comparison file now has 78 tests. The release-only consumer files deliberately do not match `*.spec.ts` and are not counted in those 668.

### Explicit Coverage Gate

Read directly from each `node:test --experimental-test-coverage` reporter, including its `line %` header; not inferred from a successful test exit:

| File | Workspace lines | Candidate lines | Branches (both) | Functions (both) | ≥90% line gate |
| --- | --- | --- | --- | --- | --- |
| `src/compile.ts` | 99.50% | 99.50% | 98.28% | 100.00% | PASS |
| `src/solver.ts` | 98.65% | 98.65% | 92.13% | 100.00% | PASS |

Raw suite logs in scratch: `workspace-test.stdout.log` SHA-256 `bac00b9f947983bc60d776b0f6d0fe03e45d7015e89b8fe4cb5cf012392c6f73`; `candidate-test.stdout.log` SHA-256 `ad5daa7773e168e106ea08bb3039d70f4e18c2006b773dbe8adc81a13ac58923`. Each ends with the 668/77 summary and coverage table. The manifest records all 17 captured command records and stdout/stderr hashes. Scratch `record-command.mjs` records the real child status/signal/error and full streams, never a synthetic success code.

## Installed Tarball and README Proof

- Tarball: `<scratch>/divmain-sat-2.0.0.tgz`, **41,105 bytes**, unpacked **160,627 bytes**.
- SHA-256: `6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41`.
- npm shasum: `637b5664066645dacaa7cb6b7b9d8cec08bfd61f`.
- npm integrity: `sha512-aCaYlGULP/kFNyHi3mIBBdjTeA3j6gqnHpX5ZYOD4Lk7JBvQ1guVvfZJ4UujP4C09eDpg8zMWTukNbqWnZWLHQ==`.
- Consumer: `<scratch>/consumer` (new directory, empty local npm cache/config, offline install, scripts disabled, only `@divmain/sat` in its dependency tree).
- Raw installed-consumer evidence: `<scratch>/consumer/release-evidence.json`, SHA-256 `68a64d9541439db43adbcd28d2817e6b98f0d5947676f46366c2d2bf05e46979`.

The ten package files are `README.md`, `package.json`, and four JavaScript/four declaration modules under `dist/`. No test files, source TS, old legacy module, Janus data, dependency tree, symlinks, or scratch artifacts were packed. Both JavaScript and declaration import closures reach exactly `compile`, `expr`, `index`, and `solver`; relative module edges retain `.js` suffixes. Package and declaration realpaths remain inside the consumer, never in workspace `src/` or `dist/`.

Plain Node verifies the exact nine runtime exports, complete own numeric ordinary-object models (including arbitrary names), SAT/UNSAT/empty outcomes, enumeration and constant assumptions, validation even before cached UNSAT, the lost-assumption and stale-PLE witnesses, one-read assumption replay, exception/reentry cleanup, defensive hook output, and actual stats scopes. A retained learned-clause probe observes first-call work `0/2/1/0/1/1`, then `0/0/0/0/0/1`: new admissions reset while the live gauge remains one. Constructor-unit exclusion is checked separately. All ten runtime probe groups also pass with `NODE_ENV` unset, with results identical to the production-mode consumer run.

Strict TypeScript uses NodeNext, `strict`, `exactOptionalPropertyTypes`, `noUnusedLocals`, `noUnusedParameters`, `verbatimModuleSyntax`, **`types: []`**, and **`skipLibCheck: false`**. The compiler consumes only consumer files, installed declarations, and the isolated candidate's TypeScript standard libraries. It checks all seven public type-only exports and **39 meaningful negative contract checks**; the compiler's symbol table also verifies the exact export set (not merely successful imports). `Value` alone occupies both type and value namespaces. `compileCount`, `Solver`, `Clause`, `CompiledCnf`, legacy names, and DIMACS are absent from the root API.

All six executable README fences are independently inventoried and hashed. The wrapper imports each untouched snippet in its own **plain Node process without loaders/preloads** and captures real `console.log` arguments for strict output/model checks. The TypeScript hypergraph is first compiled against the installed package and its emitted ESM is then run by plain Node. Bash installation/development instructions and the explicitly non-executable API signature reference are not mislabelled as executable examples.

| Actual installed README example | Verified result |
| --- | --- |
| Basic Usage | `{ ready: 1 }`, all runtime imports resolve |
| Finding a Single Solution | Exact `{ a: 1, b: 0, c: 1, d: 1, e: 1 }` |
| Finding All Solutions | The unique worked model, plus constrained OR model `{ a: 0, b: 1 }` |
| Reusing a Compiled Solver | Valid XOR model, call-local UNSAT, opposite valid model, successful later unconstrained call |
| SolverStats | Single-shot one decision, assumed incremental call zero ordinary decisions |
| Ported Hypergraph Heuristic | `2 16 0`; both complete 19-name models satisfy all 18 independently listed edges and forced `a,b,c,g,h = 1` |

Installed README SHA-256: `78941a6f5c646e9b3379cb1cdea6bd233d112189abd3b33709178d21d8f11879`. Individual original/emitted snippet hashes are in the manifest.

## Truthful Phase-4 Single-Shot Benchmarks

The writer was adapted, not copied into competing per-phase implementations. It now writes only **`phase4-benchmark.json` and `.md`**, explicitly labelled Phase4/single-shot. It authenticates original Phase-1 and committed Phase-2/3 evidence by full commit, Git blob, and raw SHA-256, checks historical implementation bytes at their **artifact commits**, and preserves the Phase-3 embedded Phase-1/2 provenance verbatim. Recorded HEADs remain context, not a claim that uncommitted measurements were Git-clean.

Source snapshots precede dynamic implementation imports, include all source modules plus actual benchmark/helper/budget/package/compiler inputs, and recheck both hashes and file versions before writing. Fixture hashes, labels, assumptions, coverage, and caps must exactly agree with authenticated history and are checked before and after solving. Every SAT result undergoes independent AST evaluation and strict model/own-numeric-assumption validation. Verdict disagreement, malformed counters/models, changed sources/fixtures, or budget exhaustion fail before report writes. PHP UNSAT additionally follows from the pigeonhole principle.

Unit tests capture exactly two in-memory Phase-4 writes and inject failures through the actual runner. Their real-SAT/stubbed-PHP controls and synthetic renderer cases are explicitly labelled and **are not the recorded benchmark measurements**. The four actual CLI benchmark runs use real compilation/solving for all eight rows, without stubs or altered knobs.

All **48 current counters** equal committed Phase 3. Each report provides 144 per-counter comparisons across all three historical phases, preserving missingness and zero-denominator handling:

| Instance | Verdict | Decisions | Propagations | Conflicts | Restarts | Learned total/live |
| --- | --- | --- | --- | --- | --- | --- |
| hypergraph | SAT | 2 | 16 | 0 | 0 | 0 / 0 |
| PHP(5,4) | UNSAT | 38 | 301 | 28 | 0 | 27 / 27 |
| PHP(6,5) | UNSAT | 205 | 1905 | 152 | 1 | 151 / 151 |
| 3-SAT seed42 | SAT | 16 | 137 | 13 | 0 | 13 / 13 |
| 3-SAT seed43 | SAT | 6 | 27 | 2 | 0 | 2 / 2 |
| 3-SAT seed44 | SAT | 7 | 24 | 1 | 0 | 1 / 1 |
| PHP(7,6) | UNSAT | 1061 | 12237 | 834 | 6 | 833 / 833 |
| PHP(8,7) | UNSAT | 7179 | 100904 | 5946 | 29 | 5945 / 5945 |

**No blanket gain:** the nine Phase-2 decision/propagation/conflict count regressions remain explicit. PHP(6,5) conflicts rose 147→152 (+3.40%), PHP(7,6) 723→834 (+15.35%), and PHP(8,7) 3627→5946 (+63.94%). Small-PHP decision/conflict ratios versus Phase 1 are 1.34x/1.86x and 1.82x/2.47x, not orders of magnitude or wall-time speedups. Phase 1 completed its small PHP rows and has no large-PHP measurements; missing is not a timeout or infeasibility claim.

The original six caps stay 200,000; PHP(7,6)/(8,7) caps stay **7,230/36,270**, historical calibrations 723/3627. Random fixtures remain 20 variables, 85 clauses, seeds 42/43/44. Hypergraph parity remains **2 decisions / 16 propagations / 0 conflicts**, including ordinary named don't-cares.

These runs do **not** measure `createSolver` reuse or persistent enumeration performance. No row reaches the unchanged 10,000-admission reduction threshold; final live counts do not demonstrate deletion, peak memory, or a total-memory bound. Dedicated existing tests cover reduction. Enumeration output/permanent blockers and protected learned clauses can grow; exponential worst cases remain.

Task-aa07 originally reported all four actual report pairs as byte-identical. Its four CLI logs
and surviving reports were retained, but not four separate JSON copies; that claim alone is not
four independently retained byte comparisons. The later read-only task-2c7f pass added two
immediate per-run hash assertions. The current repair above retains all four new actual pairs;
it does not retroactively manufacture the missing historical copies. The surviving identities are:

| Artifact | Git blob | SHA-256 |
| --- | --- | --- |
| Phase-4 JSON | `3f75b8d819a6b2e0fed45bed662b3bb575ca2868` | `4e0bf82088935537737a2e61e011875988a66b703b105c5f6c61c1b5b61ab795` |
| Phase-4 Markdown | `669dee20a621d3575a3efe0518739cbc5b54d733` | `9c42e40e47158d0fb7f47a5a59cbe61b7d02d8ec06f862cf2b5fb3f15a15bc24` |

## Reproduction Without Commits or the Active Index

Use a new directory under the preapproved scratch parent and this reviewed source state. The exact 20-path overlay is also in the manifest. The following Git `add` affects **only the named private index**, never the active workspace index. It excludes the unowned baseline change and the two post-execution review records. No `commit-tree`, commit, or tag is involved.

```bash
W=/Users/dalebustad/dev/sat
S=/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-aa07-reproduce
BASE=53a059c761e9b3591b8513a03309699ecef0c889
ls /var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode
mkdir "$S"
I="$S/candidate.index"
GIT_INDEX_FILE="$I" git -C "$W" read-tree "$BASE"
GIT_INDEX_FILE="$I" git -C "$W" add -- .gitignore AGENTS.md README.md package-lock.json package.json src/compile.ts src/index.ts src/solver.ts test/index.spec.ts test/incremental-helpers.ts test/incremental-property.spec.ts test/incremental.spec.ts test/bench.ts test/bench-comparison.ts test/bench-comparison.spec.ts test/release-consumer.mjs test/release-consumer.mts test/release-smoke.mjs test/phase4-benchmark.json test/phase4-benchmark.md
TREE=$(GIT_INDEX_FILE="$I" git -C "$W" write-tree)
git -C "$W" archive --format=tar --output="$S/candidate-source.tar" "$TREE"
git clone --no-local --no-checkout "$W" "$S/candidate"
git -C "$S/candidate" checkout --detach "$BASE"
tar -xf "$S/candidate-source.tar" -C "$S/candidate"
git -C "$S/candidate" rev-parse --is-shallow-repository
git -C "$S/candidate" status --short
```

Set the command working directory to `$S/candidate` for the following (do not copy any existing install/build directory). Check the manifest's raw source hashes before and after. For this recorded candidate, `$TREE` is `8b58af7efa801254b7c3a515b0e046ea4a3e6d87`; a different reviewed source state must not borrow these measurements.

```bash
npm ci
npm run build
npm run check
TSX_DISABLE_CACHE=1 npm test
npx --no-install tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strict --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck src/*.ts test/*.ts
TSX_DISABLE_CACHE=1 npm run bench
TSX_DISABLE_CACHE=1 npm run bench
git diff --check
ls "$S"
npm pack --json --pack-destination "$S"
node test/release-smoke.mjs "$S/divmain-sat-2.0.0.tgz" "$S/consumer"
```

The committed release smoke runner derives its toolchain from its own candidate location, refuses an existing consumer, installs offline into an empty cache, and leaves full evidence under the new consumer. Tests and benchmarks require the retained full history. Re-running after a future commit changes the report's HEAD-context field; do not rewrite frozen historical reports or claim that field alone identifies measured implementation bytes.

## Preservation, Warnings, and Remaining Work

- All seven incoming incremental files retain their entry hashes (listed in the manifest). Their uncommitted implementation was included in the candidate, not edited by this task.
- Frozen Phase-2 JSON/Markdown/review match `ade64e558ee47c60ae7b4b2cc29f861ccfb245cf`; frozen Phase-3 JSON/Markdown/review match `53a059c761e9b3591b8513a03309699ecef0c889`. None was an output target. The unowned baseline remains `db759f95c491e685f27ed12039897dcb10c8e4a1`.
- Active workspace index remains byte-identical: Git blob `bfd376204b766cee0d0bfbb9a91caecbf26d2222`, raw SHA-256 `d59661cdc556269ed1e997312297a7c3122c11d26b255a91e14e587e6a924f73`. HEAD is unchanged and staged diff is empty. The private index/tree/archive are only scratch validation inputs.
- `npm ci` was successful **but not warning-free**: the existing locked development tree reports two moderate/two high vulnerabilities, old transitive-tool deprecations, and install-script notices. No audit fix or dependency upgrade was performed outside scope. The isolated installed runtime package has zero dependencies, and the explicit runtime-only audit reports zero vulnerabilities. This is not a claim that development dependencies are vulnerability-free.
- The Node26/tsx `DEP0205 module.register()` deprecation notice remains visible in benchmark/suite logs. Build, lint/format, strict consumer types, and plain-Node consumer processes have no such error or suppressed failure. No new Node floor is declared; this evidence covers the recorded environment, not every Node release.
- A separate read-only task-aa07 audit checked documentation, source/package identities, export/type negatives, installed README paths, and benchmark provenance against raw evidence and found no blocker. It did not perform or claim the parent's independent Phase-4/final-acceptance review.
- **Remaining:** task-2c7f, independent Phase-4 verification, and any later parent-controlled final commit/clean-checkout confirmation/publication decision. This record authorizes none of those Git/registry actions and does not satisfy objv-b2ca.
