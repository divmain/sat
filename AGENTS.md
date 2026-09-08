# AGENTS.md

`@divmain/sat` — a zero-dependency SAT solver library (TypeScript, ESM, Node).

## v2 release: read the plan first

The v2 MiniSat-style CDCL core and all three public solving APIs are implemented. Release/final acceptance is tracked by **Janus plan `plan-7748`** — the full design doc lives at `.janus/plans/plan-7748.md`. Code comments referencing "Design § ..." point into that file. Work items are Janus tickets (`.janus/items/`); check plan status before picking up work, and keep every task checkpoint green. The quarantined v1 solver (`src/legacy.ts`) was deleted at the API-rewire task (task-e476); do not resurrect v1 entry points.

Module layout:

- `src/expr.ts` — frozen formula frontend (`and`/`or`/`not`/`implies`/`xor`, `Value`, `getVariables`)
- `src/compile.ts` — Tseitin compiler, `BooleanExpr → CompiledCnf`; literal helpers (MiniSat-style `lit = 2*v + isNeg`) live here; `solver.ts` imports them, never the reverse
- `src/solver.ts` — iterative CDCL core: watched propagation, first-UIP learning/backjumping, VSIDS/phase saving, Luby restarts, LBD-protected reduction, persistent enumeration, and replayable per-call assumption prefixes
- `src/index.ts` — exact public API: selective formula/type exports, `SolverStats`/`VariablePriority` (defined in `solver.ts`), `SolveOptions`/`SatSolver`, `getSolution`, `getAllSolutions`, and `createSolver`. `Solver`, `getVariables`, `isVariable`, and compiler instrumentation such as `compileCount` stay internal

## Platform neutrality and debug audits

- **`src/` stays platform-neutral**: no bare `process` reference and no `node:` import anywhere under `src/`. `test/platform-guard.spec.ts` enforces both rules and allows exactly one platform reference by exact string — the guarded `globalThis.process?.env?.SAT_DEBUG === '1'` initialization in `src/solver.ts`. Do not add a second one; use a platform-neutral API instead.
- **Debug audits are opt-in.** The audit flag initializes from `SAT_DEBUG=1` (read once at module load through the guarded access above); `setDebugAssertions(enabled)` — exported from the internal `src/solver.ts` only, never re-exported from `index.ts` — flips it at runtime, and audits read the flag at call time.
- **The test suite runs audits globally** via `--import ./test/debug.ts`, wired into every npm test script (Node propagates `--import` to `node:test` workers). Never import `test/debug.ts` from a spec file: the preload sets a `globalThis` load-proof marker that the guard test asserts, so the marker must be attributable to the preload alone.

## Commands

- `npm ci` — install the locked development tools in a fresh checkout
- `npm test` — full suite (`node:test` via tsx, discovers `./test/**/*.spec.ts`, prints coverage); allow several minutes for the unchanged 59,049-model enumeration stress, not a 120-second tool timeout
- `npx tsx --test './test/compile.spec.ts'` — single test file; put `--test-name-pattern '<name>'` before the file argument for one test
- `npm run check` — biome lint + format check; `npm run fix` — auto-apply
- `npm run build` — `tsc` (compiles `src/` only; tests are tsx-run, not compiled)
- `npm run bench` / `npm run bench:legacy` — assert-only legacy benchmark verifier; **writes nothing** (no artifact-writing path is reachable from npm scripts). Authenticates the frozen Phase-1/2/3 references plus the Phase-4 record, markdown, and manifest at the release commit, including every embedded Phase-4 source fingerprint against those Git bytes; re-runs all 8 fixtures. Two modes: **parity** (default until the Phase-2 minimization task flips `bench:legacy` to gates mode permanently) hard-fails unless all 48 counters exactly equal the frozen Phase-4 record; **gates** (`--gates`) keeps the same authentication/verdict/oracle/cap checks and prints non-fatal counter deltas. `bench` is verify-only until Phase 2 retargets it at the v3 harness; `bench:legacy` stays assert-only. Source/fixture hashes identify measurements; recorded HEAD is context only. Does not benchmark incremental solving or enumeration
- `npm run typecheck` — strict source/test typecheck (`tsc --noEmit --module ESNext --moduleResolution Bundler --target es2022 --strict --exactOptionalPropertyTypes --noUnusedLocals --noUnusedParameters --skipLibCheck src/*.ts test/*.ts`; the ordinary build compiles source only)

Checkpoint gate after any task: `npm run build`, `npm run check`, `npm run typecheck`, `npm test` all green.
Release gates additionally include `npm run bench`, `git diff --check`, explicit **≥90% line coverage for each of compile.ts and solver.ts** from the test reporter, and an installed `npm pack` tarball exercised under plain Node ESM plus strict TypeScript, including README examples. `npm pack` does not build automatically; use fresh install/build state so stale ignored `dist/` cannot mask packaging failures. Keep tarballs outside the repository (and ignored).

Both the full test suite and the benchmark authenticate Git history. Use a full checkout containing `7037f823d192dc3cf2dc9119c8063781e143113c`, `ade64e558ee47c60ae7b4b2cc29f861ccfb245cf`, and `53a059c761e9b3591b8513a03309699ecef0c889`; a shallow clone/source archive is insufficient. Never add a fallback to mutable baseline files or invent missing historical measurements. Fresh candidate validation must include intended uncommitted source changes, exclude unowned changes/secrets, and isolate `node_modules`/`dist`; report any overlay honestly rather than claiming it is Git-clean.

## Packaging and CI

- `package.json` consumer contract (pinned by `test/release-smoke.mjs`): pure-ESM `exports` mapping only `"."` (no deep imports), `types`, `sideEffects: false`, `files: ["dist"]`, real `description`/`keywords`/`repository`/`homepage`/`bugs`, empty `dependencies`, and intentionally no `engines` (not a claim of testing every Node version). Any task changing a smoke-pinned contract — metadata, the `dist/` inventory (`.js`/`.d.ts`/`.js.map`, never `.d.ts.map`), result shapes, the README fence inventory, or version — updates the smoke tooling in the same change.
- `tsconfig.json`: `strict: true`, emitting `sourceMap` + `inlineSources` (self-contained `.js.map` files) and deliberately **no `declarationMap`** — under `files: ["dist"]` its `../src` references would dangle.
- `.github/workflows/ci.yml` checks out with `fetch-depth: 0` (tests and benchmarks authenticate Git history), then runs `npm ci`, build, check, typecheck, the full test suite, and `bench:legacy`.

## Conventions that differ from defaults

- **`.js` extensions on relative imports in `src/`** (e.g. `from './expr.js'`) — tsconfig uses `module: NodeNext`; extensionless imports emit broken ESM into `dist/`.
- **`exactOptionalPropertyTypes: true`** — declare optional options properties as `foo?: T | undefined` or forwarding `opts?.foo` fails to typecheck.
- **Biome gates** (`npm run check`): no non-null assertions without a per-line `// biome-ignore ... : <reason>`; optional chaining required; no `any`; builtins imported as `node:assert`/`node:test`; `import type` for type-only imports. Bitwise ops, classes, and parameter reassignment are allowed.
- Machine-written JSON under `test/` must be `JSON.stringify(data, null, 2) + '\n'` or biome format-check fails.
- Test helper/tooling files must **not** match `*.spec.ts` (test discovery pattern) — see `test/helpers.ts`, `test/debug.ts`.
- `noUnusedLocals`/`noUnusedParameters` are on: defer fields to the phase that uses them, or `_`-prefix intentionally unused params.

## Hard constraints (from the plan — verify there before deviating)

- **Zero runtime dependencies, permanently** — PRNG, DIMACS parsing, benchmarking are hand-rolled in `test/`.
- **No recursion in `solver.ts`** (search depth must not hit the JS stack); compiler recursion over expression nesting is accepted.
- **No wall-clock assertions in unit tests** — performance is proven via `SolverStats` oracles (e.g. `decisions === 0`, `learnedClauses > 0`), never timers.
- Keep fixed fixtures/property batteries/stress sizes/conflict caps; the hypergraph oracle is **2 decisions, 16 propagations, 0 conflicts** (batch PLE leaves two ordinary named don't-cares), not zero decisions. PHP(7,6)/(8,7) benchmark caps remain **7230/36270**; a budget exception is a failure, never UNSAT evidence. Preserve frozen Phase-2/3 artifacts and expose regressions honestly.
- Determinism: sorted variable indexing, index-ordered tie-breaking, fixed default polarities.
- Pure-literal elimination is scoped to single-shot `getSolution` only — enabling it for enumeration or incremental solving is unsound (worked counterexamples in Design § Solver Core).
- Incremental assumptions are validated/snapshotted before cached UNSAT, replayed before decisions **and SAT**, and cancelled in `finally`. Call-local UNSAT must never poison the permanent base-UNSAT cache. Stats outputs reset before validation: per-call work/new learned admissions plus the absolute live learned count; retained lifetime core accounting/reduction cadence is separate. Initial units are enqueued during creation, outside incremental per-call measurements.
