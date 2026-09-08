# Frozen v2 recorder, schema/corpus version 1

This directory is an immutable, self-contained measurement overlay for
`ae1a4fe9459c525d1ae746c82eb8bdbd2a97b0b2`. It is not a candidate harness.
Never migrate its imports or algorithms to a later solver. It contains no specs;
nothing outside this directory may import it once sealed. npm scripts remain
the assert-only legacy verifier during the recorder ticket.

## Inputs and identities

`fixtures.ts` pins all 23 rows, generator versions, draw/AST order, parameters,
and the literal ordered 32-call history. Coloring uses one Mulberry32 draw per
undirected pair and edge probability 0.12, with all vertices constrained to
exactly one color by pairwise clauses. The incremental base is n=150, m=639,
seed=1; a separate seed 0x51a7 selects four distinct variables then four signs
per call. These previously unspecified details were chosen before measurement.
The eight legacy inputs reproduce their authenticated Phase-4 fingerprints.

Input SHA-256 hashes compact JSON of `inputIdentity`: version, ID, mode,
definition, AST content, ordered assumption entries and ordered call history.
Compiled SHA-256 separately hashes the complete canonical snapshot: numVars,
numNamedVars, explicit index/name pairs, numeric-lexicographically sorted copied
normalized clauses, and levelZeroUnsat. Snapshotting occurs before solver
construction, never changes solver clause order, and retains the named universe
even when all its clauses disappear. Legacy artifacts include full snapshots;
v3 rows include snapshot hashes (reconstructable using this frozen compiler).

Models are checked independently against AST semantics, total named assignments,
and assumptions before hashing sorted name/value pairs. Enumeration retains
ordered individual model digests, a count, a sorted-digest set hash, and an
ordered-prefix hash. Incremental records retain every executed call's verdict,
model digest and counters, including an interrupted call and the unexecuted
suffix length. SHA-256 is over UTF-8 compact JSON; artifact files themselves use
two-space JSON with a trailing newline. Absent measurements are not zeroes.

## Historical adapter and calibration

The adapter mirrors public v2 paths using its internal Solver: single-shot PLE;
one persistent solveAssuming core without PLE; and the permanent-blocker loop
without PLE for enumeration. This is NOT a claim that v2 had public budgets.
One positive lifetime conflict cap covers construction and the whole scenario.
Construction stats are separately captured; incremental work deltas sum with
construction to lifetime totals. learnedClausesCurrent is an absolute gauge,
never summed. The exact historical exception is exhaustion, including terminal
root conflicts: v2 throws after counting but before non-root conflict analysis.
Partial calls/models survive; the interrupted core is discarded immediately.

Every trial and final run compiles/constructs afresh and replays from call zero.
Calibration starts at 100,000; one exhausted retry uses 1,000,000. A completion
selects max(10 * conflicts, 1,000); double exhaustion selects 100,000 and means
only a lower bound. Two further fresh runs at the selected cap must agree
exactly. Calibration payloads are separate from the sealed final payload, whose
independent second run is authenticated by confirmationSha256. Replay repeats
calibration AND both final runs, not just stored verdicts. All rows are retained.

## Execution and provenance

Commit this directory before measuring. In a new detached worktree at the full
baseline commit, install ONLY this directory from its seal commit using
`git restore --source=<seal> --worktree -- test/v3-baseline-overlay`, then run a
fresh `npm ci`. Do not overlay candidate code, node_modules, dist, or debug
preloads. Run separate processes with NODE_OPTIONS unset, once with NODE_ENV
unset and once with NODE_ENV=production:

```sh
env -u NODE_ENV -u NODE_OPTIONS node --import tsx test/v3-baseline-overlay/recorder.ts measure <seal> <outside-output-unset.json>
env -u NODE_OPTIONS NODE_ENV=production node --import tsx test/v3-baseline-overlay/recorder.ts measure <seal> <outside-output-production.json>
```

Each output has baseline and legacy members. Assemble each reference as
`{schema: 1, environments: [unset.member, production.member]}` without editing
payloads. Commit test/v3-baseline.json and test/legacy-compiled-cnf.json once.
Then create ANOTHER fresh detached baseline worktree/install with the sealed
overlay and invoke `replay <seal> <full-artifact-commit>` in both environments.
Replay reads references from Git only, prints their blob/SHA identities, and
byte-compares canonical JSON environment payloads. Remove the worktrees after
success. No timing, timestamps, mutable HEAD context, or absolute worktree path
enters the deterministic projection; console timings are informational only.

Every run authenticates actual baseline source/config/package/lockfile bytes
and the entire overlay inventory against their commits, records file blobs and
SHA-256s, Node/platform/architecture/versions/audit state and installed tool
package metadata, the installed dependency-tree content hash (including symlink
targets), and rechecks bytes after execution. Unexpected source siblings and
launch flags other than `--import tsx` are rejected. `overlay: true` is
mandatory: these are intentionally overlaid worktrees, not Git-clean trees.
Fresh installs rely on the authenticated lockfile and npm integrity checking.

Before sealing, a temporary spec OUTSIDE this overlay tests public-mode parity,
cap boundaries, partial enumeration and incremental histories, construction and
call accounting, model validity, snapshot/input identities, exact corpus/legacy
generators, and fresh calibration retry contracts against the actual baseline
in both environments. It is deleted at seal time so future tests/typechecking
cannot accidentally import this historical adapter into the candidate tree.

Pre-seal contract validation: 20 tests / 4 suites passed against pristine
ae1a4fe in BOTH environments with a fresh npm ci, using
`node --import tsx --test test/v3-prefreeze.spec.ts`. Explicit strict tsc and the
pinned Biome check passed there too. Temporary spec SHA-256:
`59ffd96ac735a9e8a043765cedb6e7df8c018b0424888cf24c4fd35f1848c792`.
The spec is intentionally removed rather than shipped as an executable future
test. Corpus inputs were generated and authenticated in these tests but NOT
solved or measured before the seal. npm reported four locked-development-tool
advisories (two moderate, two high), deprecations and blocked install scripts;
the installed tools worked without changing the historical lockfile/policies.
