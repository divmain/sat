# Phase-4 Acceptance Verification — task-2c7f

## Current Independent Phase-4 Disposition

**SUCCESS — plan-7748, Phase4 (Incremental Solving and Release).** The original independent
verifier resumed after the owner-authorized GENERAL-agent repair and approves the parent phase
commit. This is independent pre-commit approval, not publication approval or a claim that the
parent's subsequent committed Git-clean confirmation has happened. Task-2c7f is complete.

The original **FAILURE** was correct: a required retained regression was missing. The GENERAL
agent added the exact historical test, rather than substituting a different contradiction or
waiving the requirement. The resumed verifier independently checked the actual retained syntax,
historical/current constructor ASTs, all 32 assignments, both strict assertions, and the test's
execution in the full suite. The original finding and repair-agent evidence remain below as
history. No production source, executable test, fixture, budget, expectation, dependency, or
public contract was changed during the resumed verification; only these final evidence records
were annotated.

### Newly Executed Independent Evidence

New scratch root `V` (distinct from every repair/earlier-verification checkout):

```text
/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-phase4-verifier-20260906
```

| Identity | Independently verified value |
| --- | --- |
| Base HEAD | `53a059c761e9b3591b8513a03309699ecef0c889` |
| Executed, complete 46-file input tree | `8fe8b56bc567a4dd5ca15945cb73e0c59cbf093e` |
| `V/candidate-source.tar` SHA-256 | `57c403485db057ba81befb6f0ad5b955360e7e18c5185f00e573944e63c051c6` |
| Pre-annotation execution summary | `V/verification-checkpoint-results.json` |
| Summary SHA-256 | `90426a5d891be68bcdd461021c33095cac6f760eff10e3fd79a47b93968d14fa` |
| New installed-consumer evidence | `V/consumer/release-evidence.json` |
| Consumer evidence SHA-256 | `cfe2a48f95769e1270de24d7eacc42b56f035ca83e2a74cc6990f2c96f490e91` |

A new private index was seeded from the base and given the explicit 23-path allowlist, including
the repaired test and all three existing evidence records. The reconstructed tree matched the
actual current candidate, not an older 668-test snapshot. A new `git clone --no-local --no-checkout`
retained the full historical objects; the private-index overlay was materialized into that clone.
Before fresh `npm ci` and build, checks proved no `node_modules`, `dist`, `.janus`, or Git object
alternates existed there. All three historical commits and `git fsck --full --strict --no-reflogs`
passed. The real workspace index was not used for staging. **This was an uncommitted overlay,
not Git-status-clean.** Every intended source file matched its input inventory before and after
execution; only the unowned baseline was deliberately replaced by its committed bytes in scratch.

| Newly executed gate | Result |
| --- | --- |
| Workspace build / Biome lint+format / strict source-test types / diff check | PASS |
| Workspace `npm test` | **669 tests / 78 suites; zero failed, cancelled, skipped, or todo** |
| Fresh candidate `npm ci`, build / check / strict types / diff check | PASS |
| Fresh candidate `npm test` | **669 tests / 78 suites; zero failed, cancelled, skipped, or todo** |
| Explicit reporter line coverage in both runs | **compile.ts 99.50%; solver.ts 98.65%**, each >=90% |
| Fresh candidate `npm run bench`, twice | PASS; two separately retained real JSON/Markdown pairs |
| Fresh candidate `npm pack`, isolated installed Node ESM / strict NodeNext / README checks | PASS |
| Additional installed runtime with NODE_ENV unset | PASS, matching the smoke's production results |
| Independent truth-table, lifecycle, event-accounting, static/v1, and deep-search probes | PASS |
| Runtime-only `npm audit --omit=dev` | Zero vulnerabilities; development warnings remain disclosed |

The strict command was `npx --no-install tsc --noEmit --module ESNext --moduleResolution Bundler
--target es2022 --strict --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters
--skipLibCheck src/*.ts test/*.ts`. The source build itself uses NodeNext. Full suites retained
their unchanged stress and used a 900-second external allowance, not weakened in-test limits.
The new collector authenticates command exit/signal/error fields and both stream hashes; the
checkpoint contains 18 command records. Final annotation checks and the final workspace rerun
are recorded externally in `V/verification-results.json`, not borrowed from repair-agent results.

### Current Criterion-to-Evidence Map

1. **PASS — CDCL mechanisms.** Actual watched propagation, batch scoped PLE, first-UIP resolution,
   asserting backjump, VSIDS/index ties, phase saving, Luby restarts, and LBD/reason protection were
   inspected. The unchanged targeted suites passed, including the reachable eager-search 4→1
   implied-UIP witness and exact restart/rescaling/deletion oracles. Supplemental observations
   delegate to the real production operations and independently reconcile actual events.
2. **PASS — API/version.** Installed symbol-table and runtime checks confirm exactly **9 runtime
   exports / 7 type-only exports**, with Value alone in both namespaces; frontend contracts are
   unchanged. Package/root-lock versions are 2.0.0, dependencies are empty, files is `["dist"]`,
   and engines is absent. No legacy entry point, compiler instrumentation, or DIMACS root export.
3. **PASS — search pathologies.** Real compileCount is **1 across 256 changing public calls**;
   the expression getter is read twice at construction and never afterward. A separate transparent
   observer records **one actual public core over 128 calls**, not merely cached compilation.
   Independent 40-variable enumeration gives 41 unique valid models (21 with the tested constant
   assumption). Two plain-Node production searches reach **16,384 levels / 32,768 decisions** with
   one compilation and stable mutable storage. Hypergraph remains exactly **2/16/0**. This is not
   an allocation-free claim: hook snapshots and debug audits still allocate.
4. **PASS — all promised v1 cases, including the repaired omission.** The seven original
   enumeration expressions run through the newly installed package and a separate truth table,
   yielding **1,3,1,3,2,1,0** models. The exact original UNSAT test is now retained in npm test and
   passes, as do both empty cases and strict numeric/own-key/auxiliary-exclusion checks. Its
   constructor AST hash and prefix survivors **16,8,4,1,0,0** reproduce independently. Approved
   PLE-aware first-model dispositions are preserved rather than weakening exact required cases.
5. **PASS — incremental soundness and stats.** Prefix processing precedes decisions **and SAT**;
   dummy levels, propagation between assumptions, replay after backjump/restart, validation and
   one-read snapshots before cache/hooks, local versus permanent UNSAT, and finally-root cleanup
   all pass. New explicit **3→0 non-assumption learning still returns SAT** with both assumptions
   replayed. Caught/uncaught reentry and getter/hook/output exceptions recover correctly. Per-call
   work/admissions match independently observed events; the live gauge matches the real database,
   constructor units stay outside per-call counts, and lifetime reduction cadence is retained.
6. **PASS — correctness batteries and fixed gates.** Both main variants execute **1,024 formulas
   / 3,824 assumption samples**; each of three incremental configurations executes **256 formulas
   / 2,048 calls**. All prior-phase strict/negative oracles and DIMACS/PHP gates remain unchanged.
   The **59,049-model** stress again reports peak live **103 < 256**, **922 deleting rounds**,
   **29,437 deletions**, and final live87. PHP caps remain **7,230 / 36,270**; exceptions are never
   interpreted as UNSAT.
7. **PASS — constraints/determinism.** No runtime dependencies, public DIMACS, legacy core, solver
   recursion, or wall-clock unit assertions. The new static check finds no cycle among 31
   non-constructor core helper/method nodes; construction was also inspected. All 15 spec files
   pass the timing/skipped-call audit. Independent handles give identical results and stats for
   identical ordered histories. Compiler/frontend nesting remains recursive and documented.
8. **PASS — tooling/package.** All 13 relative source import/export edges retain `.js`. Fresh
   build, lint+format, strict source/test types, and installed strict declarations pass. The new
   package has exactly ten intended files, with all bytes equal across workspace build, isolated
   build, and installation. **39 meaningful negative type checks**, every public entry point,
   and all six real installed README examples pass without ambient/workspace fallback.
9. **PASS — documentation and authorized freshness.** README matches actual assumptions, stats,
   hook, ordering, liveness, empty-formula, migration, and limitation contracts; Installation is
   byte-identical to v1. All required commands ran on the actual isolated intended source. The
   parent's post-commit Git-clean confirmation remains a separate required next step, not waived.

### Supplemental Independent Results and Boundaries

The verifier's own `diagnostics.mjs` uses separate evaluators, variable discovery, and an xorshift
corpus, not project reference helpers or prior solver models as an oracle. It checks all 256
three-variable truth functions with all absent/UNSET/FALSE/TRUE subsets and reordered calls:
**32,768 public calls**, 26,864 SAT / 5,904 UNSAT, and 1,465 observed UNSAT-to-SAT transitions.
It also checks **2,718 calls on 86 SAT bases**, **578 analyzed clauses / 14,143 non-vacuous
clause-model entailments**, **18,806 retained-root consequence checks**, 1,510 dummy levels,
367 restarts, 572 reductions, and 81 deletions (74 after earlier calls). A full auxiliary-CNF
truth table is included and its projection agrees with an independent AST reference. Twelve
deliberately malformed model/collection controls are rejected. The same battery passes against
both fresh compiled code and the installed tarball; those repetitions are not distinct corpora.

New tarball: `V/divmain-sat-2.0.0.tgz`, **41,105 bytes**, SHA-256
`6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41`.
It was compared byte-for-byte with the repair tarball. Its consumer contains only the package
and npm metadata; strict TypeScript consumes only installed declarations, consumer inputs, and
the fresh candidate's TypeScript standard libraries. All six untouched README fences have
actual output checks, including hypergraph **2 16 0**.

The two new benchmark runs retain `V/candidate-bench-{1,2}.report.{json,md}` as separate files.
They reproduce JSON SHA-256 `4e0bf82088935537737a2e61e011875988a66b703b105c5f6c61c1b5b61ab795`
and Markdown SHA-256 `9c42e40e47158d0fb7f47a5a59cbe61b7d02d8ec06f862cf2b5fb3f15a15bc24`.
Independent checks authenticate all three historical references and 22 historical source hashes;
all **48 counters equal Phase3** and the **nine Phase2 PHP regressions** remain explicit. Large
PHP conflicts are **834 / 5,946**, below unchanged caps. The repair's six separately retained
pairs were additionally audited as prior evidence, not claimed as this verifier's executions.
The older task-aa07 four-run JSON-retention limitation is not retroactively repaired.

Only this review, the benchmark review, and the release manifest change after the executed input
tree above. They are non-packaged evidence annotations, not runtime/test/configuration changes.
The exact resulting 46-file tree and per-file differences are recorded in
`V/final-annotation-inputs.json`; final checks are in `V/verification-results.json`. **Do not call
8fe8b56... the full post-annotation tree.** All source/test/package bytes remain identical to the
freshly executed isolation. HEAD remains53a059c, the active index remains blob
`bfd376204b766cee0d0bfbb9a91caecbf26d2222`, and the unowned baseline remains
`db759f95c491e685f27ed12039897dcb10c8e4a1`, unchanged and unstaged. Frozen Phase2/3 artifacts match
their commits. No commits, staging of the active index, tags, pushes, PRs, publication, new
tickets/objectives, or objective completion occurred.

Limits remain explicit: Node26.8.1 / TypeScript5.4.5 is the exercised environment, not every Node
version or a proof for every possible formula. Two moderate/two high locked development-tool
vulnerabilities, transitive deprecations/install-script notices, and Node26/tsx DEP0205 remain
visible; source build/lint checks are clean and runtime-only audit is zero. No dependency upgrade
or warning suppression was made. Benchmarks are **single-shot only**, not incremental/enumeration
performance, default-reduction, scalability, or total-memory evidence. **objv-b2ca remains
independent and unachieved.** Parent phase commit is approved; subsequent committed fresh-checkout
confirmation is still required before claiming the release gate complete.

## Current Repair Checkpoint

**Historical repair-checkpoint status: exact regression repaired; implementation checkpoint
PASS; independent Phase-4 re-verification was pending.** Task-2c7f was `in_progress` when this
checkpoint was written. This repair-agent record did not itself authorize a commit; the resumed
original verifier's current independent approval is recorded above.

The independent verifier `ses_f89bbba71ffeI401gV2M5BmKR9` correctly returned **FAILURE** at
2026-09-06T10:40:08Z: task-4d06 required the original v1 enumeration ports to be retained under
`describe('getAllSolutions')`, but the worked-UNSAT case was missing. The earlier ad hoc installed
probe did not satisfy that regular-suite requirement. No solver correctness defect was found.
That failure remains historical evidence; the omission itself is now fixed, not waived.

### Exact Retained Regression

`test/index.spec.ts:463-480` now registers an `it` under `getAllSolutions` / `unsolvable`, with
both `assert.deepStrictEqual(referenceModels(formula), [])` and
`assert.deepStrictEqual(getAllSolutions(formula), [])`. It retains the complete original expression:

```ts
and(not('b'), or('a', 'b'), xor('b', 'c'), implies('c', and('d', 'e')), not('d'), xor('b', 'e'))
```

Provenance: `7037f82^:test/index.spec.ts:269-280`, original expression at line 271, commit
`49a71b81c65f42b0ac01a061a6977da7aa594e54`, test blob
`b29fa571014e8449e0f1df90d4945a9cd934c1b5`, source blob
`0179071e1e88c3ebdde42018a720c2c64540c199`. The updated spec blob is
`73ae795a1e99126be808f7bc75d08043f78a3611` (SHA-256
`fe24929d46a08cb02621f6812f27cddb71e488cdbc3cd00da1c4127fddb2ae58`).

Independent justification: `not(b)` forces `b=FALSE`; `xor(b,c)` forces `c=TRUE`; then
`implies(c,and(d,e))` forces `d=TRUE`, contradicting `not(d)`. The separate scratch proof parses
the actual old and retained test expressions, compares their constructor-call trees, and invokes
the actual historical/current constructors to compare desugared ASTs. A local Boolean evaluator
and a separate direct Boolean-algebra expression agree on all **32 distinct assignments over
a,b,c,d,e**, with **zero satisfying assignments**. Successive conjunct prefixes retain
**16,8,4,1,0,0** assignments, so the evaluator is not a constant-false substitute. The expanded
AST SHA-256 is `ac85086cbb28e44bdd8fba6edd9d1cdef65d462585132d50947da84428a5452b`.
Historical v1, current fresh build, and the newly installed package all return `[]` / `null` as
appropriate; repeated incremental calls also return `null`. The retained test is not replaced
by these supplemental probes.

### Reproduced Candidate Evidence

New scratch root `R` (not either older validation directory):

```text
/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-2c7f-repair-20260906
```

The repaired **46-file execution-input tree** is `0ef5b93de519281ad0a5beaae05a3d4eacb2f33b`.
It includes the new regular test and all three then-existing review/manifest records, including
this acceptance review. `R/candidate-source.tar` SHA-256 is
`c7d055c6cdda47db7060191ab73f6ebcbc15d0f3d27b5d91f824790349d60d3f`;
`R/candidate-inputs.json` SHA-256 is
`5ae7f22c337fa5ced979b7f1c25aaaefcf9349bf8d0e0768e14acd415755117d`.

This is a NEW full-history `--no-local` clone at `53a059c`, with a 23-path allowlisted private-index
overlay, no Git alternates, and no `node_modules`, `dist`, or `.janus` before fresh `npm ci`.
It contains all three required phase commits and passes `git fsck --full --strict --no-reflogs`.
It is **not Git-status-clean**. The workspace index was never used for staging; the unowned
baseline was excluded in favor of its committed bytes. Older trees `0372336...` and `cb1e9f9...`
are pre-repair evidence, not identities for the changed test.

| Checkpoint execution | Actual result |
| --- | --- |
| Workspace and new candidate build/check/strict source-test types/diff check | PASS |
| Workspace and new candidate `npm test` | **669 tests / 78 suites**, zero failed/cancelled/skipped/todo |
| Explicit reporter line coverage, both locations | **compile.ts 99.50%; solver.ts 98.65%**, both >=90% |
| Unchanged stress | **59,049 models; peak live 103 < 256; 922 deleting rounds; 29,437 deletions** |
| Unchanged normal/forced property batteries | **1,024 formulas / 3,824 assumption samples per variant** |
| Unchanged three incremental configurations | **256 formulas / 2,048 calls each**; actual compiler delta 1 across 256 public calls |
| Workspace and new candidate real `npm run bench`, twice each | PASS; each actual JSON/Markdown pair separately retained and hashed |
| Fresh build/pack/offline installed plain-Node and strict NodeNext consumer | PASS; 10 runtime probe groups, 39 negative type checks, all 6 installed README examples |
| Installed runtime with NODE_ENV unset, plus smoke's production mode | PASS; results identical |
| Runtime-only dependency audit | Zero vulnerabilities; existing dev-tree warnings remain |

Raw `.json` command records and full `.stdout.log`/`.stderr.log` streams are in R. The validated
25-command summary `R/checkpoint-results.json` has SHA-256
`f3b4c80ec5b59517c11c0e5e1ac7dfd356630cc784aeac2a705e001f442cfe82`.
The suite log SHA-256 values are `7b8e7d33040ba891acb5ea87b25ae1920a1fc3a329c2af516d6d80dbedb68483`
(workspace) and `5b0ecedc3d847d407354a63a0b2eda78459ff4a8caaf26d90080c9f7b2f25584` (candidate).
The new installed truth proof is `R/installed-v1-proof.stdout.log`, SHA-256
`0b666c7fbbe2d97d52805673a9739f1040a8ba2293c461d93c3f28dc42323766`.

The genuinely new `R/divmain-sat-2.0.0.tgz` is **41,105 bytes**, SHA-256
`6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41`.
Its equality to the older tarball was checked byte-for-byte, not assumed from the test-only edit.
All 10 installed files also match the fresh build and workspace build. New consumer evidence:
`R/consumer/release-evidence.json`, SHA-256
`68d47b0535f7d4308b8262c82c8626e571f3fda1fe445453ca6db736e3ac9c4c`.

The four new benchmark report pairs (`workspace-bench-{1,2}.report.{json,md}` and
`candidate-bench-{1,2}.report.{json,md}`) reproduce the existing Phase-4 report hashes below.
All 48 counters still equal Phase 3; all nine count regressions against Phase 2 remain explicit;
large PHP conflicts remain **834/5,946**, within unchanged **7,230/36,270** caps. The historical
task-aa07 four-run JSON-retention limitation is not retroactively repaired or concealed. These
newly retained copies address evidence hygiene for this attempt only. No incremental/enumeration
benchmark, total-memory bound, or future-performance-objective claim is made.

### Annotation and Approval Boundary

Only `test/index.spec.ts` and the three Phase-4 review/manifest files are repaired in the workspace.
No production source, consumer tooling, fixture, seed, stress size, stats/model contract, conflict
cap, package metadata, or dependency was changed. Phase-4 reports were regenerated only by the
real current benchmark and remain byte-identical; frozen Phase-2/3 JSON/Markdown/reviews are intact.

These three evidence annotations are written after the checkpoint above. Their final tree cannot
self-identify inside this manifest/review. The **post-annotation** 46-file source identity and
fresh-clone execution results are recorded externally in `R/final-candidate-inputs.json`,
`R/final-results.json`, and the task-2c7f repair-results note. That second clone uses a new install,
build, pack, and installed consumer; do not call the checkpoint input tree the final annotation
tree or substitute the earlier 668-test results. The only input differences are these three
non-packaged records; all executable/configuration/test/package bytes remain frozen.

Workspace HEAD/index and the unowned baseline remain unchanged; baseline blob is
`db759f95c491e685f27ed12039897dcb10c8e4a1`, unstaged. No active-index staging, commits, amends,
tags, pushes, PRs, publication, new tickets/objectives, or objective completion occurred.
Existing two-moderate/two-high dev-tool audit warnings and Node26/tsx DEP0205 remain disclosed.
**Pending at this repair checkpoint:** the original independent verifier's re-review, any later
user-approved parent commit, and committed Git-clean confirmation. Re-review has now passed as
recorded above; the commit and post-commit confirmation remain parent work. objv-b2ca is independent
and not achieved. This repair checkpoint did not itself grant phase approval.

## Historical Pre-Repair Record (Superseded)

The following records the earlier read-only pass and its original measurements. Its acceptance
conclusion was superseded by the independent FAILURE above, not silently promoted to approval.
References to a missing dedicated test below describe that earlier state only.

**Historical finding: PASS for the authorized pre-commit release candidate.** All nine criteria were
checked against the implementation, independent probes, actual command results, and a newly
installed package. Plan: **plan-7748**, Phase 4, Incremental Solving and Release.

This is a verification record, not an implementation repair, publication approval, the parent's
subsequent independent Phase-4 approval, or the still-pending post-commit clean-checkout check.
No algorithm, test expectation, fixture, budget, dependency, public API, or README was changed.
This file and Janus verification notes are the only additions made to the workspace by this task.
Objective **objv-b2ca** remains independent and is not satisfied by this verification.

## Controlling Requirements

The full current ticket, plan (including owner notes), AGENTS.md, implementation tickets, source,
relevant test/reference/consumer code, package configuration, and release evidence were reviewed.
Read-only independent audits additionally examined incremental soundness and benchmark provenance.
Prior ticket status alone was not treated as proof.

- The task's 2026-09-06 owner note supersedes copied criterion 3's old zero-decision wording:
  require **2 decisions, 16 propagations, 0 conflicts** under `h=TRUE`, preserving global batch
  PLE and ordinary named-don't-care completion. No PLE or counter semantics were changed.
- Current comparative acceptance requires authenticated, honest comparisons, PHP learning,
  hypergraph parity, and fixed PHP conflict caps **7,230 / 36,270**. It does not require invented
  Phase-1 infeasibility or orders-of-magnitude gains. Those future goals belong to objv-b2ca.
- Fresh intended-source isolation is the authorized pre-commit gate. It must not be described
  as a Git-status-clean committed v2 checkout. The parent retains the later committed check.

## Exact Candidate and New Isolation

All new raw evidence is under:

```text
/var/folders/w4/8_bbh5gn5ds4766m6bbkz8b40000gn/T/opencode/sat-2c7f-verification-20260906
```

Below, `S` means that directory. Darwin's `/private/var/...` spelling resolves to the same place.

| Identity | Verified value |
| --- | --- |
| Workspace/base HEAD | `53a059c761e9b3591b8513a03309699ecef0c889` |
| Reconstructed 45-file candidate tree | `0372336fd18a1af3ea6c07c0ed4162ad5090fabd` |
| `S/candidate-source.tar` SHA-256 | `db4300177c63ce213bf69183e8f8eaf71ac6f12a4ba4cafe196be131f908ddee` |
| Candidate baseline Git blob | `489af8c72ed9c37befa806ccef03404d0a818e61` |
| Excluded, preserved workspace baseline Git blob | `db759f95c491e685f27ed12039897dcb10c8e4a1` |

A new private `GIT_INDEX_FILE` was seeded from HEAD and given only the existing release manifest's
20 overlay paths plus its two post-validation review records. Its computed tree exactly matched
the supplied final 45-file candidate, rather than assuming that the older snapshot was current.
The real workspace index was never used for staging.

`git clone --no-local --no-checkout` created **S/candidate**, followed by a detached checkout of
the base and `checkout-index` from the allowlisted private index into that scratch worktree.
The archive above records the same tree; the overlay itself used Git's checkout-index operation.
Before installation, executable checks confirmed absence of `node_modules`, `dist`, `.janus`,
and Git object alternates. The new clone was non-shallow, contained all three required phase
commits, and passed `git fsck --full --strict --no-reflogs`. Installation and build were fresh;
no existing install/build directory was copied or linked.

**The candidate is an uncommitted overlay, not Git-status-clean.** Its actual changed/untracked
paths are recorded in `candidate-overlay.stdout.log`. All 45 scratch source files matched the
tree before and after execution. All 44 corresponding workspace files also matched; the only
intentional difference was the excluded unowned baseline. This new acceptance record was
written after that validation, is not one of those 45 input files, and is not packaged.

## Required Gates and Actual Results

Environment: Node **v26.8.1**, fresh locked TypeScript **5.4.5**, consumer npm **11.19.0**.
Full suites and benchmarks used `NODE_ENV` unset, no Node loaders inherited through the
environment, and `TSX_DISABLE_CACHE=1`. Long commands had a 900-second external allowance;
no unit-test timer, corpus size, or budget was changed.

| Execution | Result | Raw record stem in S |
| --- | --- | --- |
| Workspace `npm run build`, `npm run check`, strict source/test types, `git diff --check` | PASS; lint and format needed no fixes | `workspace-tooling` |
| Workspace `npm test` | **668 tests / 77 suites**, 0 failures/cancellations/skips/todos | `workspace-test` |
| Fresh candidate `npm ci` | PASS, with existing development-tool warnings below | `candidate-ci` |
| Candidate build/check/strict types/diff check | PASS | `candidate-tooling` |
| Candidate `npm test` | **668 tests / 77 suites**, 0 failures/cancellations/skips/todos | `candidate-test` |
| Candidate `npm run bench`, twice | PASS; both written report hashes asserted immediately after each real run | `candidate-bench-1`, `candidate-bench-2` |
| Candidate `npm pack --json --pack-destination S` | PASS; 10 package files | `candidate-pack` |
| `node test/release-smoke.mjs S/divmain-sat-2.0.0.tgz S/consumer` | PASS; new offline installed consumer, runtime/types/README | `candidate-smoke` |
| Installed runtime probe with `NODE_ENV` unset | PASS, in addition to the smoke's production-mode probe | `consumer-runtime-unset` |
| `npm audit --omit=dev --json` | PASS; zero runtime vulnerabilities | `candidate-runtime-audit` |
| Workspace build vs fresh build vs installed package, README/package comparisons | PASS; all 10 package files match | `artifact-identity` |

The strict source/test command was run in both source locations:

```bash
npx --no-install tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strict --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck src/*.ts test/*.ts
```

Each raw command has `.json`, `.stdout.log`, and `.stderr.log` files. The inspected existing
scratch `record-command.mjs` captures the real executable/arguments/cwd/environment, child
status/signal/error, and full stream hashes, using exclusive-new output files. Its success
status is not a hand-entered summary. Supplemental inline probe bodies are retained verbatim
in their command records, so they can be reproduced without modifying repository tests.

### Explicit Coverage Gate

Read from each new reporter's **line %** column, not inferred from exit status:

| File | Workspace lines | Fresh candidate lines | Required |
| --- | --- | --- | --- |
| `src/compile.ts` | **99.50%** | **99.50%** | >=90% |
| `src/solver.ts` | **98.65%** | **98.65%** | >=90% |

Both reports show 100% function coverage for these files; their branch percentages are 98.28%
and 92.13%. The unmodified reports are at lines 890–910 of the two `*-test.stdout.log` files.

## Criterion-to-Evidence Map

1. **PASS — modern iterative CDCL.** Source review of `solver.ts` confirmed partial-assignment
   watched propagation, startup batch PLE, first-UIP resolution, asserting backjumps, named-only
   VSIDS/phase saving, Luby restarts, and learning-time LBD/reason-protected reduction.
   `solver.spec.ts`, `learning.spec.ts`, `heuristics.spec.ts`, `luby.spec.ts`, `restarts.spec.ts`,
   and `reduction.spec.ts` passed. Their operation-local graphs are not misrepresented as eager
   search traces. A new independent **real search** learned `(not mid OR not guard)` at an
   implied UIP and jumped **4→1**, leaving the trigger's activity untouched; all 36 base models
   entailed the clause. A separate SAT family observed 30 conflicts, 14 actual restarts,
   10 automatic reductions, and 18 actual deletions, with 360 local entailment checks. Exact
   Luby boundaries began `1,2,4,5,6,8,12`; assertions were still queued at restart. See
   `independent-core.json` and its output.

2. **PASS — exact API/version/contracts.** The v1 frontend source was inspected in Git and
   compared with `expr.ts`; constructor shapes, signatures, and numeric Value are unchanged.
   `index.ts` selectively exports the exact **9 runtime + 7 type-only** symbols, including
   `createSolver`/`SatSolver`, without internal or legacy additions. Installed TypeScript's
   actual symbol table confirmed that surface (`Value` alone occupies both namespaces).
   All three solving entry points, empty formulas, option forwarding, numeric assumptions,
   validation before known/cached UNSAT, defensive hooks, and detached named-only models passed
   source tests and installed probes. Package/root lock versions are 2.0.0; runtime dependencies
   are empty; `files: ["dist"]` and the deliberately absent engines field are preserved.

3. **PASS — eliminated upfront-search pathologies.** `compile.ts:105–110` collects/indexes once;
   the public APIs construct one core per instance and search mutates/undoes trail storage.
   Actual compiler instrumentation remained **1 across 256 distinct public assumption calls**
   (180 SAT / 76 UNSAT), with two expression reads during creation and none afterward.
   Independent 40-variable enumeration produced **41 distinct valid models**, one compilation,
   and two root-expression reads. The exact hypergraph default oracle was **2/16/0**; a hook
   saw only `['e','n']`, then `['n']`. A fresh compiled plain-Node core completed two searches
   of 12,000 ordinary decision levels (24,000 decisions total) with one compilation and stable
   arrays/trail through undo. No up-front `2^n` allocation was found in library search or
   enumeration. Optional hook snapshots and debug audits still allocate; this is not a claim
   of allocation-free execution or bounded total enumeration memory.

4. **Historical PASS, rejected for the missing retained test — promised v1 behavior/model shape.** The original `7037f82^:test/index.spec.ts` was
   inspected, not inferred from current test names. The and/not/xor/unique-worked/UNSAT exact
   dispositions remain; OR/implies and hypergraph use the approved PLE-aware validity/forced
   values instead of treating an incidental v1 choice as mandatory. All **seven original
   enumeration cases** were independently checked against a separate truth table through the
   installed package, plus both empty cases. Counts were **1,3,1,3,2,1,0**; numeric values,
   exact own data-property keys, uniqueness, and auxiliary exclusion passed. One placement
   caveat was explicit at this pre-repair checkpoint: the exact historical worked-UNSAT enumeration
   was not a dedicated spec case; this verification executed that exact expression and obtained
   `[]`, rather than pretending a generic empty-clause test was the old case. That was insufficient
   for task-4d06; the independent verifier rejected this PASS and the retained test is now added
   above. No regression test was rewritten during the earlier read-only pass.
   See `independent-installed-v1-dispositions` and the unchanged public/property suites.

5. **PASS — sound incremental lifecycle.** Source `solver.ts:628–784,851–882` validates and
   snapshots before cached UNSAT, replays the assumption prefix before decisions **and SAT**,
   makes already-true dummy levels, propagates each new assumption, and cancels in `finally`.
   Falsified assumptions do not set permanent UNSAT; genuine root proofs do, including before
   internal budget exceptions. Retained clauses keep conditional antecedents. Original focused
   and three-configuration property tests passed, as did independent sequential truth tables,
   non-vacuous base entailment, prefix/root/heap/watch audits, and 14 lifecycle checks below.
   Stats were reconciled against observed events: per-invocation work/new admissions, absolute
   live population, separate lifetime cadence, constructor units excluded, and cleanup before
   output-setter errors. Lost assumptions, backjump replay, cached validation, local UNSAT
   recovery, throwing getters/hooks, and caught/uncaught reentry all passed.

6. **PASS — continuous correctness batteries and bounded DIMACS.** Both unchanged main variants
   executed **1,024 formulas / 3,824 assumption samples each**, three repeated single solves,
   exact enumeration comparisons, all five constructors, and strict models in both name pools.
   Each pool reported 509 distinct ASTs. The three incremental variants each executed
   **256 formulas / 2,048 sequential calls**. Fixed DIMACS parser/structure/chain/PHP tests passed;
   the large PHP verdicts remain below their original 7,230/36,270 caps and a budget exception
   is not UNSAT. Historical phase-boundary review records and authenticated committed artifacts
   were inspected; this task does not claim to have rerun every historical checkout.
   A new independent truth-vector harness additionally checked 512 seeded formulas (510 distinct
   ASTs), all constructors, and 1,536 extra assumption samples through public and forced
   restart/reduction paths: **2,048 queries and 30,124 enumerated models per variant**, no mismatch.

7. **PASS — constraints/determinism.** No runtime dependency or public DIMACS API was introduced.
   Source inspection and a new AST check found an acyclic internal call graph across all
   **32 solver functions/methods**; compiler/frontend nesting recursion remains documented.
   All **15 spec files** were checked for timing/unseeded-random calls, and the fixed-seed
   reproducibility suites passed. No wall-clock assertion or fixture/cap weakening was added.
   The current checkpoint and new isolated checkpoint are green. See `independent-static-contracts`
   and `independent-iterative-depth`; benchmark timings are not unit-test gates.

8. **PASS — tooling and actual packaging.** NodeNext configuration and all **13 source module
   import/export edges** use relative `.js` specifiers. Build, strict source/test types, and
   Biome lint/format passed unchanged. A fresh build was packed and genuinely installed into
   a separate consumer with an empty local cache, offline installation, and scripts disabled.
   Plain Node, strict installed declarations, 39 meaningful negative contract checks, all four
   JS/declaration modules, and the real README examples passed without source-path or ambient
   @types leakage. The installed tree contains only this package plus npm lock metadata.

9. **PASS — accurate README and authorized fresh-source gate.** README was checked against the
   actual signatures, validation, model shape, PLE scope, incremental replay/cache/cleanup,
   stats scopes, hook cadence, enumeration ordering/output growth, and recursion limits.
   Migration covers positional arguments, initialAssignments, selectNextVar, both old callback
   types, bruteForceAllSolutions, getInitialAssignments, and removed/internal helper paths.
   All six executable snippets were extracted byte-for-byte from the newly installed README
   and their actual outputs checked; the hypergraph printed **2 16 0**. All four required npm
   commands passed in the new intended-source isolation. **The parent post-commit Git-clean
   confirmation is still pending**, as explicitly required by the controlling owner note.

## Additional Independent Incremental Evidence

These are additional probes, not replacements for or reduced versions of the checked-in tests.
Their own evaluators/variable discovery do not use `test/helpers.ts` or solver verdicts as truth.

| Probe | Actual result | Raw stem |
| --- | --- | --- |
| All 256 three-variable truth functions, every partial assignment and reordered calls | 13,824 calls; 10,046 SAT / 3,778 UNSAT; 2,061 immediate recoveries | `incremental-audit-truth-functions` |
| 128 distinct separately generated formulas | 4,096 calls; 3,094 SAT / 1,002 UNSAT; 316 immediate recoveries | same original grouped command |
| SAT-base full-CNF/AST entailment and event audit | 70 formulas / 1,599 calls; 338 analyzed clauses, including 4 with auxiliaries; 1,906 clause/model and 8,786 retained-root consequence checks | `incremental-audit-entailment` |
| Dummy/replayed prefix and retained database activity in that audit | 722 dummy levels; 2,545 prefix checks; 221 restarts; 150 reductions; 28 deletions, 27 after earlier calls | same command |
| Compile-once, validation, stats, cleanup, errors, reentry | 14 checks / 322 invocations, including the 256-call compiler check | `incremental-audit-lifecycle` |

The lost-assumption call reported `0/2/1/0/1/1` in the six-field stats order. Later compatible
calls succeeded while admissions reset and the retained live gauge stayed one. Known base UNSAT
performed zero subsequent work but still rejected 14 invalid-value cases and an unknown UNSET
name and read a getter. No premise was manufactured by writing a reason, assignment, activity,
or learned clause into the production search.

The unchanged **59,049-model** full-suite stress also passed in both locations: peak live learned
population **103 < 256**, **922** deleting rounds, **29,437** actual deletions, final live **87**,
and 59,049 permanent blockers. This is not a bound on total memory or default-policy performance.

## Artifact Provenance and Consumer Results

The newly produced tarball is byte-identical to the supplied task-aa07 tarball:

```text
S/divmain-sat-2.0.0.tgz
bytes: 41105
SHA-256: 6a2384999c4b14f00699ea36d1c118c4a736c40d39537a918a1f5a202b6ada41
npm shasum: 637b5664066645dacaa7cb6b7b9d8cec08bfd61f
```

The fresh installed evidence is **S/consumer/release-evidence.json**, SHA-256
`1bb9924d6bf47ebca0bc145fa2c0fe4c1dfe69f157d7af72db7f6b71dc1caf45`.
It records the actual offline install, dependency tree, file hashes/import closures, strict
TypeScript resolution/export sets/39 negative checks, ten runtime probe groups, and six README
outputs. The strict consumer uses `types: []`, `skipLibCheck: false`, `strict`, exact optional
properties, no-unused checks, and NodeNext; its declarations resolve inside the installation.

The ten files are README, package.json, and four JS/four declaration modules. Fresh candidate
build, workspace build, and installed package matched directly; no legacy module, tests, Janus
data, symlinked dependency tree, or scratch file entered the tarball. Plain-Node runtime probes
passed in production and with NODE_ENV unset. No registry publication occurred.

## Honest Comparative Findings

The independent provenance audit authenticated Phase 1/2/3 commit/blob/SHA-256 identities,
all 22 historical source hashes, and all eight independently reconstructed fixture fingerprints.
The actual current runner validates SAT models independently, preserves assumptions, fails on
budgets/verdict/source changes, and writes only the two Phase-4 reports. PHP-stubbed unit tests
exercise infrastructure only; the two new CLI runs measured real solves on all eight fixtures.

All **48 counters equal Phase 3**. PHP(7,6)/(8,7) finished at **834 / 5,946 conflicts**, below
**7,230 / 36,270**. The four PHP learning counts are **27 / 151 / 833 / 5,945**. The nine retained
decision/propagation/conflict regressions against Phase 2 are not hidden; PHP conflicts increased
147→152, 723→834, and 3,627→5,946. Small-PHP Phase-1 decision/conflict ratios are 1.34x/1.86x and
1.82x/2.47x, not orders of magnitude. Missing large-PHP Phase-1 rows remain missing measurements.

Both new runs immediately verified the written files against these existing identities:

| Report | Git blob | SHA-256 |
| --- | --- | --- |
| Phase-4 JSON | `3f75b8d819a6b2e0fed45bed662b3bb575ca2868` | `4e0bf82088935537737a2e61e011875988a66b703b105c5f6c61c1b5b61ab795` |
| Phase-4 Markdown | `669dee20a621d3575a3efe0518739cbc5b54d733` | `9c42e40e47158d0fb7f47a5a59cbe61b7d02d8ec06f862cf2b5fb3f15a15bc24` |

An older evidence-retention limitation is not concealed: task-aa07 retained four CLI logs and
the surviving reports, not four separately preserved JSON outputs; its summary flags alone are
not four independent byte comparisons. The four logged Markdown bodies and surviving JSON were
authenticated, and **this task's two new per-run hash assertions** directly re-established
reproducibility. No historical report was rewritten to improve that claim.

These are **single-shot-only** comparisons. No createSolver/enumeration speedup, total-memory
bound, default reduction engagement, broad scalability, or future objective completion follows.

## Preservation, Warnings, and Remaining Parent Work

- All incoming Phase-4 implementation/test/docs/package bytes and existing release reports,
  review, and manifest were preserved. Frozen Phase-2/3 JSON/Markdown/reviews matched their
  artifact commits. No workspace benchmark writer was run by this task; the scratch reports
  reproduced the existing workspace bytes.
- The unowned workspace baseline remains `db759f95c491e685f27ed12039897dcb10c8e4a1`, unstaged.
  Workspace HEAD remains `53a059c761e9b3591b8513a03309699ecef0c889`. The real index remains Git
  blob `bfd376204b766cee0d0bfbb9a91caecbf26d2222`, raw SHA-256
  `d59661cdc556269ed1e997312297a7c3122c11d26b255a91e14e587e6a924f73`, with an empty staged diff.
- Fresh `npm ci` again disclosed **two moderate/two high development-tree vulnerabilities**,
  old transitive-tool deprecations, and install-script notices. The runtime-only audit returned
  zero vulnerabilities. Node26/tsx's DEP0205 notice remains visible. No dependency upgrade,
  warning suppression, waiver, or claim of vulnerability-free development tooling was made.
- The earlier pass reported no unresolved implementation or pre-commit acceptance blocker. The
  independent FAILURE superseded that conclusion because a required retained test was missing;
  the current repair and pending re-verification are recorded above. Evidence remains bounded by
  the recorded environment and exercised cases, not a formal proof for all possible inputs.
- **Still required from the parent:** the separate independent Phase-4 review after this ticket;
  only then any explicitly authorized phase commit; then a genuinely committed Git-clean,
  full-history fresh-install/build/test/check/bench/type/coverage/pack/README confirmation. That
  post-commit step has not happened. Future benchmark HEAD-context changes must not be confused
  with source identity, and frozen historical evidence must remain intact.
- No active-index staging, commit/amend/tag/push/PR/publication, new ticket/objective, or change
  to objv-b2ca was performed. This verification grants none of those permissions.
