// Shared test tooling. Deliberately does not match `*.spec.ts`, so `npm test`
// never discovers this file directly; the assertions live in the spec files
// that import these helpers.

import assert from 'node:assert';
import { isDeepStrictEqual } from 'node:util';
import { and, getVariables, implies, isVariable, not, or, Value, xor } from '../src/expr.js';
import type { BooleanExpr, Variable, VariableAssignments } from '../src/expr.js';

// Reference evaluator over the BooleanExpr AST, independent of the CNF solver.
// Requires total numeric assignments; invalid variable reads fail loudly.
export function expressionValue(
  expr: BooleanExpr | Variable,
  assignment: VariableAssignments,
): Value {
  if (isVariable(expr)) {
    const value = assignment[expr];
    assert.ok(
      Object.hasOwn(assignment, expr) && (value === Value.TRUE || value === Value.FALSE),
      `reference evaluation requires an own TRUE/FALSE assignment for ${JSON.stringify(expr)}`,
    );
    return value;
  }
  if ('and' in expr) {
    return expr.and.every((subExpr) => expressionValue(subExpr, assignment) === Value.TRUE)
      ? Value.TRUE
      : Value.FALSE;
  }
  if ('or' in expr) {
    return expr.or.some((subExpr) => expressionValue(subExpr, assignment) === Value.TRUE)
      ? Value.TRUE
      : Value.FALSE;
  }
  if ('not' in expr) {
    return expressionValue(expr.not, assignment) === Value.FALSE ? Value.TRUE : Value.FALSE;
  }
  throw new Error('Invalid BooleanExpr');
}

// Unambiguous even when names contain delimiters, quotes, or control characters.
export function modelKey(model: VariableAssignments): string {
  return JSON.stringify(
    Object.keys(model)
      .sort()
      .map((variableName) => [variableName, model[variableName]]),
  );
}

// Return a copy of `models` sorted by `modelKey` so that enumeration order
// cannot affect comparisons.
export function sortModels(models: VariableAssignments[]): VariableAssignments[] {
  return [...models].sort((a, b) => {
    const aKey = modelKey(a);
    const bKey = modelKey(b);
    return aKey === bKey ? 0 : aKey < bKey ? -1 : 1;
  });
}

// Strict model equality, including values and prototypes, independent of key order.
export function modelsEqual(a: VariableAssignments, b: VariableAssignments): boolean {
  return isDeepStrictEqual(a, b);
}

// Assert that two collections of models are equal ignoring order.
export function assertModelListsEqual(
  actual: VariableAssignments[],
  expected: VariableAssignments[],
): void {
  assert.deepStrictEqual(sortModels(actual), sortModels(expected));
}

// Assert that `model` is a complete, well-shaped model of `expr`: its key set
// is exactly the sorted named-variable set of `expr`, and every value is
// Value.TRUE or Value.FALSE (no UNSET, no aux variables). Public models retain
// the ordinary object prototype and contain only enumerable own string keys.
export function assertModelShape(model: VariableAssignments, expr: BooleanExpr): void {
  assert.strictEqual(Object.getPrototypeOf(model), Object.prototype, 'ordinary model prototype');
  const expectedVariables = [...getVariables(expr)].sort();
  const actualVariables = Object.keys(model).sort();
  assert.deepStrictEqual(
    actualVariables,
    expectedVariables,
    'model key set must equal the sorted named-variable set',
  );
  assert.strictEqual(
    Reflect.ownKeys(model).length,
    expectedVariables.length,
    'model must have no hidden or symbol keys',
  );
  for (const variableName of expectedVariables) {
    const value = model[variableName];
    assert.ok(
      value === Value.TRUE || value === Value.FALSE,
      `every model value must be TRUE or FALSE (saw ${value} for ${variableName})`,
    );
  }
}

// ---------------------------------------------------------------------------
// Deterministic randomness
// ---------------------------------------------------------------------------

// Seeded pseudorandom-number-generator interface. Implementations must be
// pure functions of the seed: the same seed must produce the same stream in
// every process and on every platform (no Math.random, no Date, no state
// outside the instance).
export interface PRNG {
  // Uniform float in [0, 1).
  next(): number;
  // Uniform integer in [0, maxExclusive).
  nextInt(maxExclusive: number): number;
  // Uniform boolean.
  boolean(): boolean;
  // Uniform pick from a non-empty collection.
  pick<T>(items: readonly T[]): T;
}

// Zero-dependency mulberry32: a small, fast, well-scattered 32-bit PRNG.
// Deterministic under a fixed seed — the backbone of every seeded test.
export function mulberry32(seed: number): PRNG {
  let state = seed >>> 0;
  const next = (): number => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const nextInt = (maxExclusive: number): number => {
    if (!Number.isInteger(maxExclusive) || maxExclusive < 1) {
      throw new RangeError(`nextInt requires an integer >= 1 (got ${maxExclusive})`);
    }
    return Math.floor(next() * maxExclusive);
  };
  const randomBoolean = (): boolean => next() < 0.5;
  const pick = <T>(items: readonly T[]): T => {
    if (items.length === 0) {
      throw new Error('pick requires a non-empty collection');
    }
    return items[nextInt(items.length)];
  };
  return { next, nextInt, boolean: randomBoolean, pick };
}

// ---------------------------------------------------------------------------
// Random formula generation
// ---------------------------------------------------------------------------

// The five BooleanExpr constructors. The generator chooses among these at
// every interior node, so a sufficiently long seeded stream exercises all of
// the formula shapes the compiler must handle.
export type ConstructorKind = 'and' | 'or' | 'not' | 'implies' | 'xor';

const CONSTRUCTOR_KINDS: readonly ConstructorKind[] = ['and', 'or', 'not', 'implies', 'xor'];

// Default pool for generated formulas: the first `maxVariables` names.
const DEFAULT_VARIABLE_ALPHABET: readonly Variable[] = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];

export interface RandomFormulaOptions {
  // Bounds the number of nested constructor decisions. The expanded AST's
  // depth (counting and/or/not nodes along the longest path) is at most
  // 3 x maxDepth, because implies and xor each expand to at most three
  // junction levels. Must be an integer >= 1.
  maxDepth: number;
  // Bounds the fan-in of every and/or node in the generated AST (including
  // the binary junctions introduced by implies/xor). Must be >= 2.
  maxWidth: number;
  // Cap on distinct named variables when `variables` is not given; defaults
  // to 8 so the output always fits the reference enumerator's k <= 8 limit.
  maxVariables?: number;
  // Explicit variable pool (overrides maxVariables).
  variables?: readonly Variable[];
}

export interface RandomFormula {
  // The generated formula.
  expr: BooleanExpr;
  // Constructor choices, in the order the generator made them. Deterministic
  // under a fixed seed, like `expr` itself.
  kinds: ConstructorKind[];
}

// Internally a node may degenerate to a bare variable (at the depth limit);
// the entry point always returns a BooleanExpr.
function generateNode(
  rng: PRNG,
  pool: readonly Variable[],
  maxDepth: number,
  maxWidth: number,
  depth: number,
  kinds: ConstructorKind[],
): Variable | BooleanExpr {
  if (depth >= maxDepth) {
    return rng.pick(pool);
  }
  const child = (): Variable | BooleanExpr =>
    generateNode(rng, pool, maxDepth, maxWidth, depth + 1, kinds);
  const kind = CONSTRUCTOR_KINDS[rng.nextInt(CONSTRUCTOR_KINDS.length)];
  kinds.push(kind);
  if (kind === 'and') {
    const width = 1 + rng.nextInt(maxWidth);
    return and(...Array.from({ length: width }, child));
  }
  if (kind === 'or') {
    const width = 1 + rng.nextInt(maxWidth);
    return or(...Array.from({ length: width }, child));
  }
  if (kind === 'not') {
    return not(child());
  }
  if (kind === 'implies') {
    return implies(child(), child());
  }
  return xor(child(), child());
}

// Generate one random formula with bounded depth, width, and variable count.
// Pure function of `rng` (and hence of its seed): identical seeds produce
// identical formula streams, run to run.
export function randomFormula(rng: PRNG, options: RandomFormulaOptions): RandomFormula {
  const { maxDepth, maxWidth, maxVariables, variables } = options;
  if (!Number.isInteger(maxDepth) || maxDepth < 1) {
    throw new RangeError(`randomFormula requires maxDepth to be an integer >= 1 (got ${maxDepth})`);
  }
  if (!Number.isInteger(maxWidth) || maxWidth < 2) {
    throw new RangeError(
      'randomFormula requires maxWidth to be an integer >= 2, because implies/xor introduce binary junction nodes',
    );
  }
  let pool: readonly Variable[] = variables ?? [];
  if (variables === undefined) {
    const span = maxVariables ?? DEFAULT_VARIABLE_ALPHABET.length;
    if (!Number.isInteger(span) || span < 1) {
      throw new RangeError(
        `randomFormula requires maxVariables to be an integer >= 1 (got ${span})`,
      );
    }
    pool = DEFAULT_VARIABLE_ALPHABET.slice(0, span);
  }
  if (pool.length === 0) {
    throw new RangeError('randomFormula requires at least one variable in the pool');
  }
  const kinds: ConstructorKind[] = [];
  const generated = generateNode(rng, pool, maxDepth, maxWidth, 0, kinds);
  return { expr: isVariable(generated) ? and(generated) : generated, kinds };
}

// ---------------------------------------------------------------------------
// Naive reference enumeration
// ---------------------------------------------------------------------------

// Enumerate all 2^k assignments over the given variables (sorted for a
// canonical order). Bit `i` of the integer pattern drives variable `i`
// (least significant bit first), so the ordering is fixed for any input.
export function enumerateAssignments(variables: readonly Variable[]): VariableAssignments[] {
  const sorted = [...variables].sort();
  if (sorted.length > 8) {
    throw new Error(
      `the naive reference enumerator supports at most 8 variables (got ${sorted.length})`,
    );
  }
  const count = 2 ** sorted.length;
  // Define own data properties without invoking inherited setters such as __proto__.
  return Array.from({ length: count }, (_, pattern) =>
    Object.fromEntries(
      sorted.map((variable, bit) => [variable, (pattern >> bit) & 1 ? Value.TRUE : Value.FALSE]),
    ),
  );
}

// Ground truth for cross-validation: every assignment over the formula's
// named variables that the naive reference evaluator judges satisfying.
export function referenceModels(expr: BooleanExpr): VariableAssignments[] {
  return enumerateAssignments([...getVariables(expr)]).filter(
    (assignment) => expressionValue(expr, assignment) === Value.TRUE,
  );
}

// ---------------------------------------------------------------------------
// Assumption-subset generation
// ---------------------------------------------------------------------------

// What "consistent"/"contradictory" means for a generated partial assignment.
export type AssumptionKind = 'consistent' | 'contradictory';

export interface RandomAssumptionsOptions {
  // consistent: the returned partial assignment is extendable to a model of
  //   `expr` (drawn by trimming a random model).
  // contradictory: the returned partial assignment is not extendable to any
  //   model of `expr` (drawn by shrinking a random falsifying assignment).
  kind: AssumptionKind;
  // Cap on the number of assigned variables; honored for `consistent` only
  // (a contradiction cannot always be expressed under a smaller cap).
  maxAssumptions?: number;
}

// Fisher-Yates over a fresh copy, driven by the PRNG.
function shuffled<T>(rng: PRNG, items: readonly T[]): T[] {
  const result = [...items];
  for (let i = result.length - 1; i > 0; i -= 1) {
    const j = rng.nextInt(i + 1);
    [result[i], result[j]] = [result[j], result[i]];
  }
  return result;
}

// True when every total extension of `base` over the `unassigned` variables
// falsifies `expr` — i.e. the partial assignment is contradictory.
function allExtensionsFalsify(
  expr: BooleanExpr,
  base: VariableAssignments,
  unassigned: readonly Variable[],
): boolean {
  return enumerateAssignments(unassigned).every(
    (extension) => expressionValue(expr, { ...base, ...extension }) === Value.FALSE,
  );
}

// Shrink a falsifying total assignment to a (usually smaller) contradictory
// partial assignment, unassigning one variable at a time when doing so keeps
// every extension falsifying.
function shrinkContradiction(
  rng: PRNG,
  expr: BooleanExpr,
  variables: readonly Variable[],
  falsifier: VariableAssignments,
): VariableAssignments {
  const unassigned = new Set<Variable>();
  for (const variable of shuffled(rng, variables)) {
    const candidateFree = [...unassigned, variable];
    if (allExtensionsFalsify(expr, falsifier, candidateFree)) {
      unassigned.add(variable);
    }
  }
  return Object.fromEntries(
    variables
      .filter((variable) => !unassigned.has(variable))
      .map((variable) => [variable, falsifier[variable]]),
  );
}

// Draw a random partial assignment over the named variables of `expr`.
// Deterministic under a fixed seed. `kind: 'consistent'` guarantees the
// result extends to a model (throws if `expr` is unsatisfiable);
// `kind: 'contradictory'` guarantees no model extends it (throws if `expr`
// is a tautology). Assigned values are always Value.TRUE or Value.FALSE.
export function randomAssumptions(
  rng: PRNG,
  expr: BooleanExpr,
  options: RandomAssumptionsOptions,
): VariableAssignments {
  const variables = [...getVariables(expr)].sort();
  if (options.kind === 'consistent') {
    const models = referenceModels(expr);
    if (models.length === 0) {
      throw new Error('randomAssumptions(kind: "consistent") requires a satisfiable formula');
    }
    const model = rng.pick(models);
    const maxCover = Math.min(options.maxAssumptions ?? variables.length, variables.length);
    const coverSize = rng.nextInt(maxCover + 1);
    return Object.fromEntries(
      shuffled(rng, variables)
        .slice(0, coverSize)
        .map((variable) => [variable, model[variable]]),
    );
  }
  const falsifiers = enumerateAssignments(variables).filter(
    (assignment) => expressionValue(expr, assignment) === Value.FALSE,
  );
  if (falsifiers.length === 0) {
    throw new Error(
      'randomAssumptions(kind: "contradictory") requires a formula that is not a tautology',
    );
  }
  return shrinkContradiction(rng, expr, variables, rng.pick(falsifiers));
}

// ---------------------------------------------------------------------------
// Test-internal DIMACS: mini-parser, serializer, and programmatic generators
// ---------------------------------------------------------------------------

// A CNF in DIMACS terms: `numVars` variables numbered 1..numVars; each clause
// is a non-empty array of nonzero literals (±variable numbers), terminated by
// 0 in the text form. Test-internal only — never part of the public API.
export interface DimacsCnf {
  numVars: number;
  clauses: number[][];
}

// Minimal, dependency-free DIMACS CNF parser (~40 lines). Handles comments
// (`c ...` lines), one `p cnf <vars> <clauses>` header, clauses spanning
// multiple lines, arbitrary whitespace, and CRLF line endings. Malformed
// inputs throw a descriptive Error — the parser is verified by asserting
// exact parsed clause contents on hand-checkable strings.
export function parseDimacs(text: string): DimacsCnf {
  let numVars = -1;
  let expectedClauses = -1;
  let headerSeen = false;
  let current: number[] | null = null;
  const clauses: number[][] = [];

  for (const rawLine of text.split('\n')) {
    const line = rawLine.trim();
    if (line.length === 0 || line.startsWith('c')) {
      continue;
    }
    if (line.startsWith('p')) {
      if (headerSeen) {
        throw new Error('DIMACS file has more than one header line');
      }
      const [kind, format, varsToken, clausesToken] = line.split(/\s+/);
      if (
        kind !== 'p' ||
        format !== 'cnf' ||
        varsToken === undefined ||
        clausesToken === undefined
      ) {
        throw new Error(`malformed DIMACS header: ${line}`);
      }
      numVars = Number(varsToken);
      expectedClauses = Number(clausesToken);
      if (
        !Number.isInteger(numVars) ||
        numVars < 0 ||
        !Number.isInteger(expectedClauses) ||
        expectedClauses < 0
      ) {
        throw new Error(`invalid DIMACS header counts: ${line}`);
      }
      headerSeen = true;
      continue;
    }
    if (!headerSeen) {
      throw new Error(`DIMACS clause data appears before the header: ${line}`);
    }
    for (const token of line.split(/\s+/)) {
      if (token.length === 0) {
        continue;
      }
      const value = Number(token);
      if (!Number.isInteger(value)) {
        throw new Error(`non-integer DIMACS token: ${token}`);
      }
      if (value === 0) {
        if (current === null) {
          throw new Error('DIMACS clause terminator 0 with no preceding literal');
        }
        clauses.push(current);
        current = null;
        continue;
      }
      if (Math.abs(value) > numVars) {
        throw new Error(`DIMACS literal out of range (${value} for ${numVars} variables)`);
      }
      current ??= [];
      current.push(value);
    }
  }

  if (!headerSeen) {
    throw new Error('DIMACS file is missing the header line');
  }
  if (current !== null) {
    throw new Error('DIMACS file ends inside a clause');
  }
  if (clauses.length !== expectedClauses) {
    throw new Error(
      `DIMACS clause count mismatch: found ${clauses.length}, expected ${expectedClauses}`,
    );
  }
  return { numVars, clauses };
}

// Serialize a DimacsCnf back to canonical DIMACS text (quote-comment-free:
// header line, then one clause per line, then 0). Deterministic and
// round-trips through `parseDimacs`.
export function serializeDimacs(cnf: DimacsCnf): string {
  const lines = [`p cnf ${cnf.numVars} ${cnf.clauses.length}`];
  for (const clause of cnf.clauses) {
    lines.push(`${clause.join(' ')} 0`);
  }
  return `${lines.join('\n')}\n`;
}

// Pigeon-hole PHP(n, m): n pigeons, m holes, satisfiable iff n <= m. Every
// pigeon is in at least one hole (a disjunctive clause over that pigeon's m
// literals) and no two pigeons share a hole (a binary clause per (pigeon,
// pigeon) pair per hole). Variable (pigeon i, hole j) has index
// i*m + j + 1, so variables are grouped by pigeon — the deterministic
// ordering the DPLL benchmark depends on.
export function phpCnf(numPigeons: number, numHoles: number): DimacsCnf {
  if (!Number.isInteger(numPigeons) || numPigeons < 1) {
    throw new RangeError(`phpCnf requires an integer numPigeons >= 1 (got ${numPigeons})`);
  }
  if (!Number.isInteger(numHoles) || numHoles < 1) {
    throw new RangeError(`phpCnf requires an integer numHoles >= 1 (got ${numHoles})`);
  }
  const variableIndex = (pigeon: number, hole: number): number => pigeon * numHoles + hole + 1;
  const clauses: number[][] = [];
  for (let pigeon = 0; pigeon < numPigeons; pigeon += 1) {
    const pigeonClause: number[] = [];
    for (let hole = 0; hole < numHoles; hole += 1) {
      pigeonClause.push(variableIndex(pigeon, hole));
    }
    clauses.push(pigeonClause);
  }
  for (let pigeonA = 0; pigeonA < numPigeons; pigeonA += 1) {
    for (let pigeonB = pigeonA + 1; pigeonB < numPigeons; pigeonB += 1) {
      for (let hole = 0; hole < numHoles; hole += 1) {
        clauses.push([-variableIndex(pigeonA, hole), -variableIndex(pigeonB, hole)]);
      }
    }
  }
  return { numVars: numPigeons * numHoles, clauses };
}

// Prereq chain: implies(v[i], v[i-1]) for i = 2..numVars, i.e. (¬v_i ∨ v_{i-1}).
// Always satisfiable — exactly numVars + 1 models (the set of TRUE variables
// is a prefix of the chain).
export function prereqChainCnf(numVars: number): DimacsCnf {
  if (!Number.isInteger(numVars) || numVars < 1) {
    throw new RangeError(`prereqChainCnf requires an integer numVars >= 1 (got ${numVars})`);
  }
  const clauses: number[][] = [];
  for (let variable = 2; variable <= numVars; variable += 1) {
    clauses.push([-variable, variable - 1]);
  }
  return { numVars, clauses };
}

// Seeded random fixed-width 3-CNF: `numClauses` clauses, each over three
// distinct variables (no tautologies and no duplicates by construction) with
// uniformly random sign. Pure function of `rng`, hence deterministic under a
// fixed seed.
export function random3Cnf(rng: PRNG, numVars: number, numClauses: number): DimacsCnf {
  if (!Number.isInteger(numVars) || numVars < 1) {
    throw new RangeError(`random3Cnf requires an integer numVars >= 1 (got ${numVars})`);
  }
  if (!Number.isInteger(numClauses) || numClauses < 0) {
    throw new RangeError(`random3Cnf requires an integer numClauses >= 0 (got ${numClauses})`);
  }
  if (numVars < 3) {
    throw new RangeError(`random3Cnf requires at least 3 variables (got ${numVars})`);
  }
  const clauses: number[][] = [];
  for (let clauseIndex = 0; clauseIndex < numClauses; clauseIndex += 1) {
    const picked: number[] = [];
    while (picked.length < 3) {
      const variable = rng.nextInt(numVars);
      if (!picked.includes(variable)) {
        picked.push(variable);
      }
    }
    clauses.push(picked.map((variable) => (rng.boolean() ? 1 : -1) * (variable + 1)));
  }
  return { numVars, clauses };
}

// Convert a DimacsCnf into a BooleanExpr over named variables `v01`..`vNN`
// (zero-padded so lexicographic sorting equals numeric order, keeping solver
// variable ordering deterministic and grouped). An all-literal `or` in
// conjunctive position compiles to exactly the single plain clause, so
// `and(...or(...))` round-trips to the same clause database.
export function cnfToExpr(cnf: DimacsCnf): BooleanExpr {
  const width = String(cnf.numVars).length;
  const nameOf = (index: number): Variable => `v${String(index + 1).padStart(width, '0')}`;
  return and(
    ...cnf.clauses.map((clause) =>
      or(
        ...clause.map((literal) => (literal > 0 ? nameOf(literal - 1) : not(nameOf(-literal - 1)))),
      ),
    ),
  );
}

// ---------------------------------------------------------------------------
// Shared instance builders
// ---------------------------------------------------------------------------

// The 19-variable / 18-prereq hypergraph instance from the v1 spec: each
// pair [target, prereq] means `implies(target, prereq)` = (¬target ∨ prereq).
// Shared by index.spec.ts, solver.spec.ts, and bench.ts so all three fixtures
// come from one source.
export const hypergraphPrereqs: ReadonlyArray<readonly [Variable, Variable]> = [
  // for b to be true/visited, a must be true/visited
  ['b', 'a'],
  ['c', 'a'],
  ['e', 'd'],
  ['g', 'c'],
  ['f', 'c'],
  ['f', 'e'],
  ['h', 'b'],
  ['h', 'g'],
  // including the disjoint subgraph
  ['j', 'i'],
  ['k', 'j'],
  ['l', 'k'],
  ['m', 'l'],
  ['n', 'm'],
  ['o', 'n'],
  ['p', 'o'],
  ['q', 'p'],
  ['r', 'q'],
  ['s', 'r'],
];

// The compiled BooleanExpr for the shared hypergraph instance.
export function hypergraphFormula(): BooleanExpr {
  return and(...hypergraphPrereqs.map(([target, prereq]) => implies(target, prereq)));
}
