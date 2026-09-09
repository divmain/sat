# v3 Benchmark Review

Committed prose narrative for the machine-generated `test/v3-benchmark.json` /
`test/v3-benchmark.md` (mirroring the `phase*-benchmark-review.md` convention).
**Harness runs never rewrite this file.** Every disclosed-delta analysis,
regression discussion, and interpretation is edited by hand in the task that
causes it.

## Reference set (sealed before any counter-changing work)

- v2 baseline corpus: `cd44ed11d0e6abf1bf2b61d94dd995d4d6a04438:test/v3-baseline.json`
  (blob `6fc09b5e01d1f2851a1a643a93b61278f372b2a1`), measured by the frozen
  recorder overlay sealed at `2ba0a394b534fb64449a832ce95da4e81ee50ba6` against
  pristine v2 `ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2` in an intentionally
  overlaid worktree (`overlay: true`), with fresh installs in both audit
  environments (NODE_ENV unset and `production`; identical deterministic rows).
- Legacy complete compiled snapshots:
  `cd44ed11d0e6abf1bf2b61d94dd995d4d6a04438:test/legacy-compiled-cnf.json`
  (blob `876115a1994d75d6afc3bf9e26f249e8d3a7f94b`), captured from the same
  pristine v2 compiler before any compiler-changing work. `bench:legacy`
  compares the current compiler's full canonical snapshot — normalized clauses,
  `numVars`, the named index/name universe, and `levelZeroUnsat` — per fixture.
  A clause-only comparison would miss a lost named universe; this one cannot.

Both harnesses authenticate references exclusively from those pinned Git bytes
and re-verify every embedded historical source/tool/overlay fingerprint against
`ae1a4fe` / `2ba0a39`. Mutable working-tree reference files are never read, and
no fallback to them exists.

## Initial candidate checkpoint (task-8172)

The first candidate is the resumable-search parity refactor (task-62ea) on top
of the Phase-1 hygiene work: compilation unchanged, search counters and models
intended identical to v2. The harness confirms this with the strongest
available evidence:

- **Cross-implementation behavioral parity is exact.** All 23 rows complete
  within their sealed caps with identical outcomes, identical six-counter
  totals (scenario, construction, and every incremental per-call delta),
  identical model digests (including all 6,561 `pairs8` enumeration digests
  and the model-set digest), and identical compiled-snapshot hashes. No
  exhausted rows exist in the sealed baseline; every row was measured at its
  calibrated final cap.
- **Provenance truthfully differs.** The candidate records its own working-tree
  source hashes and Node/audit environment metadata in `test/v3-benchmark.json`;
  nothing is copied from the baseline's v2 provenance to manufacture equality.
- **Same-implementation replay is byte-identical.** Repeated harness runs of
  one implementation/environment produce byte-identical replay projections
  (and byte-identical JSON artifacts when HEAD is unchanged); wall times are
  informational only and never enter the JSON.
- **`bench:legacy` stays green** in parity mode (all 48 counters) with the new
  complete compiled-snapshot gate comparing all 8 legacy fixtures against the
  pristine-v2 reference.

The recorded baseline environments are audit-state matched (candidate
`SAT_DEBUG=1` maps to the baseline's audits-on/NODE_ENV-unset environment);
because both sealed environments recorded byte-identical rows, this selection
is a truthful label, not evidence selection.

## Disclosure conventions for later tasks

Parity mode was the default through the initial parity window. The first
counter-changing task (learned-clause minimization, task-d236) flipped
`bench:legacy` to gates mode permanently and ended the v3 counter/model-parity
window; both harnesses now default to gates, and `--parity` remains as an
explicit experiment on both. Gates-mode `npm run bench` keeps enforcing
immutable inputs, completed-baseline outcomes, caps, per-call verdicts, and
enumeration model sets, while counter/model-order/compiler-output changes
appear as disclosed deltas in `test/v3-benchmark.md` and are analyzed here.
Rules that never relax:

- Input/scenario identities and calibrated caps are compared before any result
  comparison; drift is a failure in every mode.
- A candidate must complete every completed baseline row within its cap; a
  recorded-exhausted baseline row may remain exhausted at that cap or complete
  as a disclosed improvement, with its completed prefix always compared.
  Budget exhaustion is never UNSAT evidence.
- Counters absent from the v2-measured baseline (e.g. the Phase-2
  `learnedLiterals`/`minimizedLiterals` additions) stay unrecorded, never zero.
- Supplemental corpus rows (e.g. larger XOR chains, once the memoized compiler
  lands) are append-only: measured at their then-current checkpoint, never
  back-computed against older sources.
- Frozen artifacts and the sealed recorder overlay are never edited or
  regenerated; harness runs write only `test/v3-benchmark.json` and
  `test/v3-benchmark.md`.

## Learned-clause minimization checkpoint (task-d236)

The candidate now performs iterative recursive minimization
(`ccmin_mode=2` semantics, explicit stack) after first-UIP resolution, drops
only **base-derived** level-0 literals (`rootBasis === 0`), retains
assumption/PLE-tainted root literals as minimization poison, and computes LBD
over the distinct **non-zero** levels of the final minimized clause. Every
variable carries a `rootBasis` dependency bitmask: reason-null root
assumptions/PLE pins seed their bits, root implications (including learned
root assertions) union the masks of their reason's antecedents, and
unconditional units seed zero. Non-null reasons remain implications
regardless of taint — the invariant later core extraction relies on. This is
the intended counter/model-changing task; both harnesses disclosed the deltas
below in gates mode and `--parity` was verified to hard-fail on them
(`php_5_4: decisions broke Phase-4 parity (current 37, frozen 38)`).

**v3 corpus (23 rows, all completed within sealed caps, all verdicts and
per-call outcomes unchanged).** Conflicts fell on 9 of 11 non-trivial
single-shot rows — random3_n200_seed1 by 45% (33,881 → 18,772),
random3_n250_seed2 by 32%, random3_n250_seed3 by 18% — with
`minimizedLiterals` removing 20–40% of produced learned literals on the large
rows. Two honest regressions are disclosed, not tuned away:
**random3_n250_seed1** grew 2.87× in conflicts (20,328 → 58,438) and 2.77× in
decisions — minimization changes backjump targets and VSIDS trauma order,
and on this SAT row the shorter clauses guided the search worse; it still
completed at 29% of its sealed cap (203,280). **php_9_8** is essentially flat
(+0.8% conflicts). The five single-shot SAT rows with changed search
trajectories disclose first-model changes (every model independently
revalidated by the adapter's AST/assumption oracle); `pairs8` enumeration
produced the **identical** ordered model stream (6,561/6,561, same set digest
and same prefix digest), and `incremental32` kept every per-call verdict and
first model while cutting total conflicts 12% (6,319 → 5,563) and shrinking
the live learned database from 6,319 to 5,563. The new analysis-work
counters are reported candidate-side only — they are absent from the
v2-measured baseline and stay unrecorded, never zero.

**Legacy corpus (gates mode, all verdicts/oracles/caps green).** The
hypergraph oracle is unchanged at exactly 2 decisions / 16 propagations / 0
conflicts, and the three small SAT 3-SAT rows are counter-identical
(minimization never removed a literal there). PHP rows move both ways honestly:
php_5_4 −1 decision, php_6_5 +6 conflicts, php_7_6 −21 conflicts, and
php_8_7 −27% conflicts (5,946 → 4,331), −26% propagations, −28% decisions —
the frozen +64% PHP(8,7) regression context makes this direction worth noting.
PHP caps hold with wide margins (813 < 7,230 and 4,331 < 36,270).

**Harness classification fix in the same change:** the order-insensitive
`modelSetDigest` is semantic (hard in every mode) only for completed
enumerations; a single-shot row's "set" is the singleton first model and an
incremental row's set derives from per-call first models, so both are
disclosed as algorithmic deltas through the `modelDigest` lens instead of
failing. Per-counter stats comparison (never whole-bag) keeps schema
additions from manufacturing deltas and names the exact counter that moved.

## Learned-clause retention policy checkpoint (task-5cad)

The candidate now implements the pinned two-tier retention policy: the glue
tier (LBD≤2) is never a deletion candidate, the reducible tier (LBD>2) alone
is sorted by activity (stable, admission-order ties) and its worse half is
deleted per round, skipping reason-locked clauses without backfill; the
cadence knob is unchanged (10,000 admissions). Clause activity is now MiniSat's
decayed scheme — conflict-seed/resolution uses bump by the current `claInc`,
which grows by `1/0.999` after every round — with the rescale check inside the
bump, mirroring the variable-side scheme; `claInc` is lifetime accounting,
independent of the resettable per-call output stats. Learning-time scoring and
dynamic tightening share one `computeClauseLbd` helper (distinct **non-zero**
levels), so the metric cannot drift between them.

**Dynamic LBD tightening uses the literature's hysteresis, and this file is
where that is pinned down.** The plan prose says "tighten the stored LBD if
lower". Implemented literally (any single-step improvement), probing showed
29,516 tightenings over the enumeration stress trajectory, of which 263 were
single-step 3→2 promotions into the glue tier — glue accumulates
monotonically and the frozen stress gate fails (peak live 360 vs the pinned
bound 256). Glucose's actual "dynamic nblevel" rule tightens only when the
recomputation improves the score by **at least two** (`nblevels + 1 < lbd`,
guarded to `lbd > 2`): single-step drift carries no lasting signal and never
erodes the tier. Under that rule the same stress trajectory shows exactly 3
tightenings and the gate passes unchanged. The pinned properties survive:
the score never increases, and promotion into glue is still possible (a
genuine 4→2 witness is unit-tested). This is a disclosed interpretation of
the pinned policy against its own frozen gate, not open-ended tuning.

**Enumeration stress gate passes unchanged.** The full 59,049-model
`pairs(10)` run reproduces the *identical* 29,525-conflict trajectory as the
frozen calibration, with peak live 120 < 256 (v2-policy calibration observed
103; bound derivation untouched), 922 deleting rounds (> 1), 29,413
deletions, and first deletion after model 63. Live `learnedClausesCurrent`
finishes at 111 vs 87 under the v2 policy — the two-tier rule deliberately
never spends deletion effort on glue, so a somewhat larger protected
population accumulates; the bound holds with >2× headroom.

**v3 corpus (23 rows): 18 byte-identical, 5 disclosed deltas.** The policy
engages only where admissions reach the 10,000-admission cadence, so all
coloring, XOR-chain, `incremental32`, and `pairs8` rows — and both
model-set/oracle checks — are unchanged. Of the five single-shot rows that
fire reduction rounds: `random3_n250_seed1` recovers most of the d236
regression (conflicts 58,438 → 26,996, now 1.33× over the 20,328 baseline
instead of 2.87×); `random3_n250_seed2`/`seed3` improve modestly (−1.3% and
−3.1% conflicts, identical first models); `php_9_8` is +1.3% conflicts
(still far under its cap); and **`random3_n200_seed1` regresses 2.23× vs the
d236 checkpoint** (18,772 → 41,823 conflicts, first model changed and
revalidated) — against the v2 baseline (33,881) that is a 1.23× net
regression, disclosed rather than tuned away: per the pinned policy the
worse-half quantum is measured within the reducible tier only, and on this
row the different deletion order interacts badly with minimization's
trajectory. Live learned populations move both ways (e.g. `seed3` 13,086 →
22,336 — tiering never deletes glue — vs `seed1` 18,159 → 14,950).

**Legacy corpus: zero additional delta.** None of the 8 legacy fixtures reach
the 10,000-admission cadence, so reduction never engages and the
`bench:legacy` disclosure is byte-identical to the d236 checkpoint (the same
18 non-fatal counter deltas; hypergraph oracle 2/16/0 unchanged; PHP caps
intact).

**Suite migration (observation-only doctrine preserved).**
`test/reduction.spec.ts` was migrated to exact tier/invariant properties —
the audit now recomputes the policy-prescribed deletion set (reducible-only
ranking, stable admission ties, worse half, reason-locked skipped) and asserts
set equality on every round, plus the exact `claInc *= 1/0.999` decay per
round — and gained deterministic search-generated witnesses for decayed
selection ordering, 4→2 promotion into glue, single-step hysteresis,
never-increase monotonicity, and lifetime `claInc` continuity across per-call
stat resets. Two pre-existing oracle expectations encoded the v2 selection
rule and were migrated, not weakened: the restarted-enumeration deletion
witness moved from `pairs(4)` (which learns almost exclusively glue-tier
clauses — correctly never deleted by the pinned policy) to `pairs(5)` with a
combinatorial reference, and the seeded batteries' coarse per-path
"deletions > 0" counters became exact per-round tier-fidelity checks with
explained-zero accounting (a zero-deletion path is acceptable only when every
round's worse-half window was empty or fully locked; enumeration paths keep
hard deletion requirements in the thousands). Deterministic PLE-enabled
single-shot deletion coverage remains in `reduction.spec.ts`'s SAT-gadgets
acceptance test (10 rounds, 18 deletions).

## Deterministic EMA restart policy checkpoint (task-e7d5)

The default restart policy is now the pinned Glucose-style EMA scheme, and the
decision is an extracted policy unit (`EmaRestartPolicy` /
`LubyRestartPolicy` in `src/solver.ts`, exported from that internal module
only): state plus post-transaction inputs (`lbd`, `trailLength`, `atRoot`),
no solver coupling, verdict singletons so the hot conflict path never
allocates. Both EMAs (fast α=0.25, slow α=0.02) initialize to the first
learned clause's LBD and update on **every** conflict over the solver's
lifetime; the per-search epoch (conflicts-since counter, postponement
deadline, blocking snapshot) resets per search. A restart is eligible once
conflicts-since-epoch ≥ 32 and triggers when `emaFast > 1.25 × emaSlow`; the
trigger is **blocked** — the next check postponed by exactly 32 conflicts —
when the post-transaction, pre-cancellation trail exceeds 1.1× its length at
the previous *actual* restart (per-search history; each search's first
trigger is unblocked). A root-level no-op consumes the epoch without
incrementing `restarts` or recording a snapshot. The internal
`restartPolicy: 'luby'` selector (never exported; never implied by passing
`restartBaseConflicts` alone) retains the Luby schedule with its default base
100, and every forced-Luby interaction fixture in `restarts.spec.ts`,
`reduction.spec.ts`, `enumeration.spec.ts`, `incremental.spec.ts`,
`incremental-property.spec.ts`, `search-slice.spec.ts`, and the solver-level
knob tests in `luby.spec.ts` now selects it explicitly — fixture streams,
caps, and restart/deletion engagement assertions are byte-identical, not
weakened. New `test/restart-policy.spec.ts` pins the policy units directly on
scripted streams: constant-LBD initialization, the exact EMA recurrence, the
32-conflict eligibility gate and epoch re-arming, block deadlines with
snapshot timing (trail 11 restarts where 12 blocks against a snapshot of 10),
root no-ops, lifetime-EMA persistence across `resetSearch()`, the Luby
schedules at base 1/3/2³², and end-to-end wiring where the *same* PHP(7,6)
instance restarts 4 times under EMA versus 6 under Luby. The history-dependent
EMA timing (call N's restart timing may reflect earlier calls' LBD history)
is disclosed in the README's `SolverStats` scope notes.

**PHP(8,7) versus the v2-Phase-2 reference (3,627 conflicts), explicitly.**
Under the EMA default the `bench:legacy` PHP(8,7) row completes in **5,457
conflicts (12 restarts), +50.5% over the v2-Phase-2 measurement of 3,627** —
the regression this policy was motivated by is reduced but not eliminated:
against the frozen Phase-4 Luby record (5,946, the +64% context) EMA improves
by 8.2%, while against the d236/5cad candidate checkpoint under Luby (4,331)
it is a 26.0% regression, disclosed rather than tuned away per the pinned
constants. The cap holds with a wide margin (5,457 < 36,270; 15.0%). PHP(7,6)
moves the other way: 638 conflicts (4 restarts) — 23.5% under the frozen 834
and 11.8% under the 723 calibration; its cap holds at 8.8% (638 < 7,230).
Both dimacs spec gates keep asserting `restarts > 0` under the default, so the
EMA policy's restart engagement is integration-tested, not just unit-pinned.

**Legacy corpus (gates mode, all verdicts/oracles/caps green).** The
hypergraph oracle is unchanged at exactly 2 decisions / 16 propagations / 0
conflicts; the three small SAT 3-SAT rows are counter-identical; php_5_4 is
conflict-identical (28) with **zero** restarts (its 28 conflicts never reach
the 32-conflict interval) and keeps only the pre-existing d236
decision/propagation deltas. 19 of 48 counters differ from the frozen Phase-4
record (18 differed at the 5cad checkpoint): the two `restarts` rows newly
differ (php_7_6 6→4, php_8_7 29→12) and the PHP decision/propagation/conflict
values shifted as tabled in the harness output above.

**v3 corpus (23 rows, all completed within sealed caps, all verdicts,
per-call outcomes, and enumeration model sets unchanged).** 12 rows are
byte-identical (all XOR chains, all coloring rows, and `pairs8` — the
identical ordered 6,561-model stream at the identical 3,281 conflicts; these
searches never reach the EMA interval). The restart-heavy rows improve
sharply: `random3_n250_seed1` 20,328 → 1,332 conflicts (−93.4%, erasing the
d236 regression and going 15.3× under the v2 baseline), `random3_n250_seed3`
126,003 → 61,553 (−51.1%), `random3_n250_seed2` 80,466 → 48,693 (−39.5%),
`php_9_8` 38,370 → 20,010 (−47.8%), `random3_n200_seed1` 33,881 → 21,086
(−37.8%, also erasing its 5cad regression), `random3_n150_seed1` 2,017 →
1,353 (−32.9%), `random3_n150_seed3` −1.6%. Three SAT rows regress, disclosed
not tuned away: **`random3_n200_seed2` 2,162 → 11,584 conflicts (5.36×)** —
still only 53.6% of its sealed 21,620 cap — `random3_n200_seed3` 1,666 →
3,181 (1.91×), and `random3_n150_seed2` 320 → 454 (+41.9%); on these rows the
EMA trigger fires early in easy searches where Luby's longer first epochs were
already sufficient. Five single-shot SAT rows disclose first-model changes
(each independently revalidated by the adapter's AST/assumption oracle).
`incremental32` keeps every per-call verdict **and** every per-call first
model (zero modelDigest disclosures) while cutting total conflicts 6,319 →
5,841 (−7.6%) and restarts 42 → 30 — direct evidence that lifetime EMA
history across calls is sound; the 184 disclosed cells are per-call counter
deltas. The enumeration stress gate passes with the **identical**
29,525-conflict `pairs(10)` trajectory (peak live 120 < 256, 922 deleting
rounds, 0 restarts — per-model searches never accumulate 32 conflicts), so
the pinned bound and cadence evidence are untouched. Restart counts collapse
across the hard UNSAT rows (e.g. `random3_n250_seed3` 339 → 8): fewer, better
timed restarts are the mechanism behind the conflict reductions, consistent
with the policy's motivation.

## Propagation engineering checkpoint (task-9c11)

Two separately measured propagation experiments under the task's bounded
parity/keep-drop rule. **Parent measurements for both corpora were captured
from the same exact pre-edit tree** (HEAD `cd44ed1` plus the uncommitted
Phase-2 work through task-e7d5), not from an assumed committed predecessor:
the pre-existing uncommitted `test/v3-benchmark.json` was first verified
byte-identical to a fresh pre-edit run (it genuinely represented the tree),
and fresh parent captures were retained anyway (task-local, uncommitted:
v3 JSON SHA-256 `f7c0f71b…`, legacy stdout `7a7d725d…`; both measured with
audits OFF, `SAT_DEBUG` unset, matching the audit-state-matched baseline
environment). Parent probe/profiles were captured from the same tree.

**Experiment A — blocker-literal watch entries: KEPT, exact parity.** Watch
lists now hold `{ clause, blocker, twin }` entries instead of bare clause
references: the blocker caches the clause's current OTHER watched literal, so
a satisfied clause is skipped without dereferencing its literal array. The
parity invariant — each entry's blocker equals the clause's current other
watch in BOTH lists — is established at attach, rewritten on inspection
(refresh store), and kept in step on relocation by an O(1) cross-linked twin
update (no list scan; a stale-true blocker would otherwise skip a relocation
the pre-blocker loop performs, silently changing watch order and potentially
later counters — the plan's parity caveat). The invariant is audited per
propagation visit under debug assertions (`entry.blocker === otherWatch`
checked before the refresh store) and structurally in `checkInvariants`
(twin symmetry, opposite-direction blocker tracking), so the entire audited
suite verifies it continuously. The inner loop was tightened to ONE
`litValue` per visit: the blocker's value doubles as the other-watch value
(the pre-blocker loop's second lookup on the same literal is gone), and the
bounds guards remain. Parity versus the parent captures is EXACT: all 23 v3
rows counter- and model-evidence-identical (comparator: full per-row
construction/stats counters, per-call stats, verdicts, and every model
digest), all 48 legacy counters identical, and the n=400 probe reproduces
the identical 15,090,353-propagation trajectory. Wall time is
informationally better (probe § below).

**Experiment B — dedicated binary-clause watch lists with implicit
propagation: KEPT as a disclosed-delta variant.** Binary clauses moved to
`binaryWatches` entries (`{ clause, other }`; the other literal is the
unit/conflict payload, so the clause array is never dereferenced on those
paths; binary watches never relocate, so no blocker/twin tracking is
needed), drained BEFORE the long-clause lists on every falsified event.
Separating the lists inherently changes visitation order versus the combined
list, so the variant is counter-changing and falls under the keep/drop rule;
the keep conditions are met (this analysis + the informational wall-time
improvement below). Against the parent captures: **8 of 23 v3 rows move
counters** — `random3_n200_seed2` +9.5% conflicts (11,584 → 12,685; also the
only first-model change, revalidated by the adapter's AST/assumption
oracle), `random3_n250_seed3` +3.0%, `random3_n250_seed2` −0.1%,
`random3_n150_seed3` −2.6%, `php_9_8` −1.7% conflicts with live learned
population 7,582 → 14,684 (glue binaries now propagate before long clauses
and the reduction mix shifts), and four coloring rows at propagation-noise
scale (only `coloring_n60_k3_seed1` changes conflict count, 17 → 18);
`incremental32` is fully identical (every per-call verdict, first model, and
counter); all XOR-chain rows are counter-identical; `pairs8` enumerates the
**identical 6,561-model SET** in a different ORDER (both digests disclosed:
ordered prefix changed, order-insensitive set unchanged — the hard
enumeration gate passed). All 23 rows complete within sealed caps with
unchanged verdicts. **Legacy corpus:** hypergraph oracle unchanged at
exactly 2/16/0; php_5_4 and the three small SAT rows counter-identical;
php_6_5 +8.3% conflicts (144 → 156); **php_7_6 +24.6% conflicts (638 → 795,
11.0% of its 7,230 cap), an honest regression**, restarts 4 → 3 (the
restart-policy wiring test was re-pinned EMA 4→3, Luby 6 unchanged — the
comment there anticipated re-pinning as a benchmark-disclosed decision);
**php_8_7 −42.3% conflicts (5,457 → 3,152, 8.7% of its 36,270 cap),
propagations −48.9%, restarts 12 → 8** — better than even the pre-EMA
v2-Phase-2 reference (3,627), so the binary-first order incidentally
reverses the residual EMA regression on that row. Gates mode disclosures vs
the sealed v2 baseline: 265 (parent) → 279 cells.

**Informational wall-time (never a gate).** v3 harness heavy rows, parent →
final: php_9_8 2,774 → 2,151 ms (−22.5%), random3_n250_seed2 2,933 → 2,595
(−11.5%), random3_n250_seed3 4,013 → 3,728 (−7.1%), random3_n200_seed1
1,000 → 945 (−5.5%), pairs8 292 → 152 (−48%); honest regressions: xor16 440
→ 498 (+13.3% at identical counters — per-visit cost, not trajectory),
xor12 25 → 31, small rows flat. Legacy: php_8_7 172.6 → 61.0 ms (−64.6%),
php_7_6 8.6 → 11.0 ms (more conflicts). **n=400/seed-1 probe** (Phase-1
methodology: legacy-mulberry32-v1 random 3-SAT, m=1600, public single-shot
API on `dist/`, plain Node v26.8.1): the identical 15,090,353-propagation /
187,406-conflict trajectory on parent and final trees; propagations/sec
1.046–1.072M (parent, 3 runs) → **1.103–1.115M (final, 3 runs; +5–6%)**;
audits-on/off overhead contrast ~2.8× in both states (375–379K/s with
SAT_DEBUG=1 — dominated by the unchanged O(n) per-enqueue trail audit, which
the new per-visit blocker audit does not measurably worsen). `--cpu-prof`
self-time on the propagation cluster: parent `litValue` 47.97% +
`propagateSlice` 33.78% (81.8% combined) → final 48.98% + 30.28% (79.3%);
`propagateSlice` self-time −14.9% (4,885 → 4,159 ms) and `litValue` −3.0%
(6,938 → 6,728 ms) on a 4.9% smaller profiled wall (14,462 → 13,737 ms).
The remaining `litValue` share is the scan/candidate work itself; further
hot-path gains would need assignment-layout changes, not watch changes.

**Direct watch-entry observers migrated in the same change.** The
cancellation-survival snapshots (`incremental-helpers.ts`, `restarts.spec.ts`,
`learning.spec.ts`) now compare entry identity plus blocker/other payload per
position via `snapshotWatches`/`assertWatchListsSurvive` in `test/helpers.ts`
(a raw deep-equal over shared entry references would have degenerated);
`checkInvariants` audits both watch structures (membership, per-list
position, binary `other` accuracy, blocker/twin parity) with the corruption
battery extended to stale-blocker and broken-twin rejection; membership
helpers in `solver.spec.ts`/`restarts.spec.ts`/`learning.spec.ts` cover both
lists. Exact-trajectory pins that legitimately moved were re-recorded with
explanations, not weakened: the learning backjump 4→1 test (t's implied
polarity flips with binary-first propagation — same learned clause, same
backjump, same verdict; the saved-phase consequence is documented inline)
and the PHP(7,6) EMA restart pin (4→3). The property batteries
(`property.spec.ts`, `incremental-property.spec.ts`) are unchanged and pass
untouched.

## Compiler sharing, flattening, and folding checkpoint (task-7ca6)

The compiler now canonizes the caller AST into a compilation-scoped,
compiler-owned canonical DAG before emitting any clauses. Canonization is
identity-memoized per AST object (shared subtrees — xor's duplicated operands
above all — are visited once, ending the exponential re-traversal), and
structurally hash-conses nodes by kind + ordered flattened child interning
ids, with multiplicity and order preserved (`xor(a,b)`'s duplicated operands
share; a future `exactly(1,'a','a')` still counts two occurrences). Keys are
short id strings, not embedded child keys — embedding keys would double key
length per xor level and reintroduce exponential (memory) blowup on the very
fixtures sharing is meant to unblock. Same-kind nesting flattens in canon
space (`and` under `and`, `or` under `or`) and constants fold totally
(`and()` is true, `or()` is false, annihilators fold the parent, identity
constants drop, singletons collapse); folding is pure — a folded-away subtree
emits no clauses and allocates no auxiliaries — and runs **after** variable
collection, so folded-away variables stay in the named universe and in
complete models. Emission keeps the gratuitous-gate eliminations (free
negation; the conjunctive plain-clause carve-out) and allocates one aux per
distinct canonical gate, first occurrence allocating in the same
children-before-parent post-order as v2. All caches die with the `compile()`
call; caller ASTs are never mutated, mutation between compilations is
observed, and earlier `CompiledCnf` handles never change (all unit-tested,
including the ownership oracle the later `add()` ticket will extend).

**v3 corpus (23 rows, all completed within sealed caps, all verdicts, per-call
outcomes, and enumeration model sets unchanged): 20 rows byte-identical, 3
disclosed deltas.** Every plain-CNF row (all random3, php_9_8, all coloring,
`incremental32`, `pairs8`) reproduces the sealed compiled snapshot
byte-for-byte — they have zero aux variables, no same-kind nesting, and no
structural gate duplication, so canonization cannot alter them — and their
counters/models are untouched. The three aux-heavy xor rows disclose their
compiled-snapshot drift (expected, and pinned by bounded-shape assertions in
`bench-v3.spec.ts` instead of hashes): `xor16` propagations 98,302 → 46
(2137×), `xor12` 6,142 → 34, `xor8` 382 → 22, with decisions, conflicts
(zero), verdicts, and even first-model digests unchanged — the v2 encoding
allocated ~3·2^(n−1) aux gates for an n-chain; sharing allocates 3(n−1).
Wall time on `xor16` drops from ~0.5 s to ~15 ms (informational only). The
sealed caps were calibrated against the exponential encoding; the shared
encoding completes the rows with orders of magnitude of headroom, and larger
XOR chains are now unblocked as future append-only supplements. Disclosure
count vs the sealed baseline: 279 (parent) → 285 cells, exactly the three
compiled snapshots plus the three propagation counters.

**Legacy corpus: zero delta, strict gate green.** All 8 legacy fixtures are
plain CNF, so `bench:legacy`'s complete compiled-snapshot comparison
(normalized clauses, `numVars`, named index/name universe, `levelZeroUnsat`)
matches the authenticated pristine-v2 reference byte-for-byte in both digest
and deep structure — the gate was run before the first compiler edit and
re-run after — and the 19 non-fatal counter deltas are unchanged from the
task-9c11 checkpoint (hypergraph oracle still exactly 2/16/0).

**Suite migration (oracles strengthened, none weakened).** `compile.spec.ts`
keeps every consing-free structural carve-out and full-gate oracle untouched
and adds: bounded-shape sharing pins (linear aux bound on a left-deep
xor(12) chain, four-occurrence consing bounded by two-occurrence size —
never exact aux counts on consed inputs), order/multiplicity preservation
agreement cases, folded-universe pins (`or('x', and())` folds to true while
`x` stays in the named universe; `and('a', or())` folds to the empty clause
with `a` retained), negated-constant folds, caller-mutation/handle-immutability
across separate compilations, and all-assignment agreement on identity-shared
and structurally shared subtrees. The `or(and('a','b'),and('c','d'))` invalid
total named assignment (a=1,b=0,c=1,d=0) is retained as an ordinary
propagation-refutation regression — it neither relies on nor claims anything
about Plaisted-Greenbaum one-sided gates (the proposed PG clauses refute the
same assignment), and PG stays deferred. `bench-v3.spec.ts`'s sealed-snapshot
test now asserts byte-exact reproduction on the 20 plain-CNF rows and the
disclosed bounded-shape drift on the three xor rows; `index.spec.ts` gained a
comment correction for the folded `and(or(),'a')` shape (the levelZeroUnsat
short-circuit behavior itself is unchanged and still asserted). Extension
correctness and propagation refutation remain exercised per total named
assignment by the agreement harness, now documented as the named encoding
contract in `src/compile.ts`. `compile.ts` line coverage is 100%.
