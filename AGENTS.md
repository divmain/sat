# AGENTS.md

`@divmain/sat` — a zero-dependency SAT solver library (TypeScript, ESM, Node).

## Active rewrite: read the plan first

The repo is mid-migration from v1 (brute-force "DPLL") to v2 (MiniSat-style CDCL), tracked as **Janus plan `plan-7748`** — the full design doc lives at `.janus/plans/plan-7748.md`. Code comments referencing "Design § ..." point into that file. Work items are Janus tickets (`.janus/items/`); check plan status before picking up work, and keep every task checkpoint green. Do not "fix" or improve `src/legacy.ts` — it is the quarantined v1 solver, deleted at the API-rewire task.

Current module layout (transitional):

- `src/expr.ts` — frozen formula frontend (`and`/`or`/`not`/`implies`/`xor`, `Value`, `getVariables`)
- `src/compile.ts` — Tseitin compiler, `BooleanExpr → CompiledCnf`; literal helpers (MiniSat-style `lit = 2*v + isNeg`) live here; `solver.ts` imports them, never the reverse
- `src/solver.ts` — CDCL core under construction (occurrence-list propagation done; search/learning added per phase)
- `src/legacy.ts` — quarantined v1 solver (do not touch)
- `src/index.ts` — public API; today re-exports `expr.ts` + `legacy.ts` only; v2 entry points land at the rewire task

## Commands

- `npm test` — full suite (`node:test` via tsx, discovers `./test/**/*.spec.ts`, prints coverage)
- `npx tsx --test './test/compile.spec.ts'` — single test file; add `--test-name-pattern '<name>'` for one test
- `npm run check` — biome lint + format check; `npm run fix` — auto-apply
- `npm run build` — `tsc` (compiles `src/` only; tests are tsx-run, not compiled)
- `npm run bench` — **not yet implemented** (`test/bench.ts` arrives in a later Phase-1 task); don't expect it to run

Checkpoint gate after any task: `npm run build`, `npm run check`, `npm test` all green.

## Conventions that differ from defaults

- **`.js` extensions on relative imports in `src/`** (e.g. `from './expr.js'`) — tsconfig uses `module: NodeNext`; extensionless imports emit broken ESM into `dist/`.
- **`exactOptionalPropertyTypes: true`** — declare optional options properties as `foo?: T | undefined` or forwarding `opts?.foo` fails to typecheck.
- **Biome gates** (`npm run check`): no non-null assertions without a per-line `// biome-ignore ... : <reason>`; optional chaining required; no `any`; builtins imported as `node:assert`/`node:test`; `import type` for type-only imports. Bitwise ops, classes, and parameter reassignment are allowed.
- Machine-written JSON under `test/` must be `JSON.stringify(data, null, 2) + '\n'` or biome format-check fails.
- Test helper/tooling files must **not** match `*.spec.ts` (test discovery pattern) — see `test/helpers.ts`.
- `noUnusedLocals`/`noUnusedParameters` are on: defer fields to the phase that uses them, or `_`-prefix intentionally unused params.

## Hard constraints (from the plan — verify there before deviating)

- **Zero runtime dependencies, permanently** — PRNG, DIMACS parsing, benchmarking are hand-rolled in `test/`.
- **No recursion in `solver.ts`** (search depth must not hit the JS stack); compiler recursion over expression nesting is accepted.
- **No wall-clock assertions in unit tests** — performance is proven via `SolverStats` oracles (e.g. `decisions === 0`, `learnedClauses > 0`), never timers.
- Determinism: sorted variable indexing, index-ordered tie-breaking, fixed default polarities.
- Pure-literal elimination is scoped to single-shot `getSolution` only — enabling it for enumeration or incremental solving is unsound (worked counterexamples in Design § Solver Core).
