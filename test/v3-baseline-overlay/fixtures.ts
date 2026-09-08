import { and, implies, not, or, Value, xor } from '../../src/expr.js';
import type { BooleanExpr, Variable, VariableAssignments } from '../../src/expr.js';

export interface Scenario {
  id: string;
  mode: 'single' | 'incremental' | 'enumeration';
  definition: Record<string, unknown>;
  expr: BooleanExpr;
  assumptions: VariableAssignments;
  calls: VariableAssignments[];
}

export interface PRNG {
  next(): number;
  nextInt(maxExclusive: number): number;
  boolean(): boolean;
  pick<T>(items: readonly T[]): T;
}

export interface DimacsCnf {
  numVars: number;
  clauses: number[][];
}

// These four generators retain the v2 test/helpers.ts implementations verbatim.
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

export function coloringCnf(numNodes: number, numColors: number, seed: number): DimacsCnf {
  if (!Number.isInteger(numNodes) || numNodes < 1) {
    throw new RangeError('coloringCnf requires an integer numNodes >= 1');
  }
  if (!Number.isInteger(numColors) || numColors < 1) {
    throw new RangeError('coloringCnf requires an integer numColors >= 1');
  }
  const rng = mulberry32(seed);
  const variableIndex = (node: number, color: number): number => node * numColors + color + 1;
  const clauses: number[][] = [];
  // All vertices, including isolated ones, receive exactly-one-color constraints.
  for (let node = 0; node < numNodes; node += 1) {
    clauses.push(Array.from({ length: numColors }, (_, color) => variableIndex(node, color)));
    for (let colorA = 0; colorA < numColors; colorA += 1) {
      for (let colorB = colorA + 1; colorB < numColors; colorB += 1) {
        clauses.push([-variableIndex(node, colorA), -variableIndex(node, colorB)]);
      }
    }
  }
  for (let nodeA = 0; nodeA < numNodes; nodeA += 1) {
    for (let nodeB = nodeA + 1; nodeB < numNodes; nodeB += 1) {
      if (rng.next() < 0.12) {
        for (let color = 0; color < numColors; color += 1) {
          clauses.push([-variableIndex(nodeA, color), -variableIndex(nodeB, color)]);
        }
      }
    }
  }
  return { numVars: numNodes * numColors, clauses };
}

export function xorChain(length: number): BooleanExpr {
  if (!Number.isInteger(length) || length < 2) {
    throw new RangeError('xorChain requires an integer length >= 2');
  }
  const width = String(length).length;
  const nameOf = (index: number): string => `v${String(index).padStart(width, '0')}`;
  let expr = xor(nameOf(1), nameOf(2));
  for (let index = 3; index <= length; index += 1) {
    expr = xor(expr, nameOf(index));
  }
  return expr;
}

export const pairs = (count: number): BooleanExpr =>
  and(...Array.from({ length: count }, (_, i) => or(`a${i + 1}`, `b${i + 1}`)));

// Literal history: one RNG for all calls; reject duplicate indices before drawing
// any signs. Property insertion order is selection order, not sorted name order.
export const INCREMENTAL_HISTORY: readonly Readonly<VariableAssignments>[] = Object.freeze(
  (
    [
      { v121: Value.FALSE, v097: Value.FALSE, v137: Value.TRUE, v036: Value.FALSE },
      { v131: Value.TRUE, v075: Value.FALSE, v118: Value.TRUE, v122: Value.FALSE },
      { v015: Value.TRUE, v099: Value.TRUE, v119: Value.FALSE, v105: Value.TRUE },
      { v090: Value.TRUE, v019: Value.FALSE, v030: Value.FALSE, v061: Value.FALSE },
      { v039: Value.TRUE, v003: Value.FALSE, v110: Value.FALSE, v021: Value.FALSE },
      { v080: Value.FALSE, v018: Value.TRUE, v014: Value.TRUE, v134: Value.FALSE },
      { v038: Value.TRUE, v075: Value.TRUE, v147: Value.TRUE, v106: Value.FALSE },
      { v135: Value.TRUE, v079: Value.TRUE, v142: Value.TRUE, v145: Value.TRUE },
      { v038: Value.FALSE, v139: Value.FALSE, v138: Value.TRUE, v049: Value.TRUE },
      { v135: Value.FALSE, v125: Value.FALSE, v101: Value.TRUE, v029: Value.FALSE },
      { v055: Value.TRUE, v057: Value.FALSE, v010: Value.FALSE, v004: Value.FALSE },
      { v140: Value.FALSE, v021: Value.FALSE, v064: Value.FALSE, v142: Value.TRUE },
      { v030: Value.FALSE, v024: Value.TRUE, v048: Value.TRUE, v136: Value.FALSE },
      { v066: Value.TRUE, v027: Value.FALSE, v146: Value.FALSE, v007: Value.FALSE },
      { v047: Value.TRUE, v016: Value.TRUE, v115: Value.FALSE, v014: Value.FALSE },
      { v145: Value.FALSE, v049: Value.TRUE, v139: Value.TRUE, v053: Value.TRUE },
      { v018: Value.FALSE, v139: Value.FALSE, v082: Value.TRUE, v074: Value.FALSE },
      { v069: Value.TRUE, v042: Value.FALSE, v045: Value.TRUE, v029: Value.FALSE },
      { v036: Value.FALSE, v008: Value.TRUE, v125: Value.TRUE, v030: Value.FALSE },
      { v027: Value.TRUE, v004: Value.FALSE, v147: Value.FALSE, v130: Value.TRUE },
      { v093: Value.TRUE, v032: Value.FALSE, v095: Value.FALSE, v039: Value.TRUE },
      { v019: Value.TRUE, v051: Value.FALSE, v092: Value.TRUE, v067: Value.FALSE },
      { v121: Value.FALSE, v074: Value.FALSE, v134: Value.FALSE, v072: Value.FALSE },
      { v013: Value.FALSE, v004: Value.TRUE, v076: Value.FALSE, v018: Value.TRUE },
      { v109: Value.TRUE, v064: Value.FALSE, v107: Value.FALSE, v038: Value.TRUE },
      { v062: Value.FALSE, v093: Value.TRUE, v105: Value.FALSE, v126: Value.TRUE },
      { v013: Value.FALSE, v110: Value.TRUE, v129: Value.FALSE, v014: Value.TRUE },
      { v126: Value.TRUE, v072: Value.FALSE, v007: Value.TRUE, v143: Value.FALSE },
      { v056: Value.FALSE, v092: Value.FALSE, v129: Value.TRUE, v039: Value.FALSE },
      { v149: Value.TRUE, v006: Value.FALSE, v031: Value.FALSE, v087: Value.TRUE },
      { v032: Value.FALSE, v074: Value.TRUE, v042: Value.TRUE, v031: Value.TRUE },
      { v140: Value.FALSE, v084: Value.FALSE, v071: Value.TRUE, v090: Value.FALSE },
    ] as VariableAssignments[]
  ).map((call) => Object.freeze(call)),
);

const CNF_DEFINITION = {
  version: 1,
  encoding: 'legacy-cnfToExpr-v1: and of ordered or clauses; negative literals use not',
  variableNames: 'v + 1-based DIMACS index padded to String(numVars).length',
};

function random3Definition(numVars: number, seed: number): Record<string, unknown> {
  return {
    ...CNF_DEFINITION,
    algorithm: 'legacy-random3Cnf-v1',
    rng: 'legacy-mulberry32-v1',
    numVars,
    numClauses: Math.round(4.26 * numVars),
    ratio: 4.26,
    clauseCountRule: 'Math.round(ratio * numVars)',
    seed,
    selection: '3 distinct nextInt(numVars) indices via rejection, in draw order',
    signs: 'after selection, one boolean() draw per index; next() < 0.5 means positive',
    clauseOrder: 'generation order; no cross-clause deduplication',
  };
}

// Order is part of the version-1 corpus identity. No solver or compiler runs here.
export function corpus(): Scenario[] {
  const rows: Scenario[] = [];
  for (const numVars of [150, 200, 250]) {
    for (const seed of [1, 2, 3]) {
      rows.push({
        id: `random3_n${numVars}_seed${seed}`,
        mode: 'single',
        definition: random3Definition(numVars, seed),
        expr: cnfToExpr(random3Cnf(mulberry32(seed), numVars, Math.round(4.26 * numVars))),
        assumptions: {},
        calls: [],
      });
    }
  }
  rows.push({
    id: 'php_9_8',
    mode: 'single',
    definition: {
      ...CNF_DEFINITION,
      algorithm: 'legacy-phpCnf-v1',
      pigeons: 9,
      holes: 8,
      variableIndex: 'pigeon * holes + hole + 1; zero-based pigeon and hole',
      clauseOrder: 'all pigeon at-least-one clauses, then pigeonA < pigeonB, then hole',
      encodingRule: 'at least one hole per pigeon; no two pigeons share a hole',
    },
    expr: cnfToExpr(phpCnf(9, 8)),
    assumptions: {},
    calls: [],
  });
  for (const length of [8, 12, 16]) {
    rows.push({
      id: `xor${length}`,
      mode: 'single',
      definition: {
        version: 1,
        algorithm: 'left-deep-xor-v1',
        length,
        variableNames: 'v + 1-based index padded to String(length).length',
        construction: 'xor(v1,v2), then xor(previous,vi) for i=3..length; assert odd parity',
        xorExpansion: 'or(and(a,not(b)),and(not(a),b)); retain shared operand identities',
      },
      expr: xorChain(length),
      assumptions: {},
      calls: [],
    });
  }
  for (const numNodes of [40, 60]) {
    for (const numColors of [3, 4]) {
      for (const seed of [1, 2]) {
        rows.push({
          id: `coloring_n${numNodes}_k${numColors}_seed${seed}`,
          mode: 'single',
          definition: {
            ...CNF_DEFINITION,
            algorithm: 'undirected-erdos-renyi-coloring-v1',
            rng: 'legacy-mulberry32-v1',
            numNodes,
            numColors,
            seed,
            edgeProbability: 0.12,
            edgeDraws: 'one next() per nodeA < nodeB in ascending nested order; edge iff < 0.12',
            variableIndex: 'node * numColors + color + 1; zero-based node and color',
            vertexClauses:
              'every node: positive colors clause, then negative colorA < colorB pairs',
            edgeClauses:
              'after all vertex clauses: each edge, then each color, exclude both endpoints',
            includeIsolatedNodes: true,
          },
          expr: cnfToExpr(coloringCnf(numNodes, numColors, seed)),
          assumptions: {},
          calls: [],
        });
      }
    }
  }
  rows.push({
    id: 'incremental32',
    mode: 'incremental',
    definition: {
      version: 1,
      algorithm: 'persistent-random3-assumptions-v1',
      base: random3Definition(150, 1),
      callCount: 32,
      assumptionRng: 'legacy-mulberry32-v1',
      assumptionSeed: 0x51a7,
      assumptionsPerCall: 4,
      selection: '4 distinct nextInt(150) indices via rejection; retain selection order',
      signs: 'after all 4 indices, boolean() per index; next() < 0.5 means Value.TRUE',
      rngLifetime: 'one separate assumption RNG across all 32 calls, never reset',
      history: 'INCREMENTAL_HISTORY-v1; literal records in call and property insertion order',
      execution: 'one persistent solver; no PLE; calls are per-call assumptions, not base clauses',
    },
    expr: cnfToExpr(random3Cnf(mulberry32(1), 150, 639)),
    assumptions: {},
    calls: INCREMENTAL_HISTORY.map((call) => ({ ...call })),
  });
  rows.push({
    id: 'pairs8',
    mode: 'enumeration',
    definition: {
      version: 1,
      algorithm: 'legacy-pairs-v1',
      count: 8,
      construction: 'and(...or(a_i,b_i)) for i=1..count in ascending order',
      variableNames: 'a and b prefixes with unpadded 1-based indices',
      expectedModels: 6561,
      execution: 'persistent blocking-clause enumeration through terminal search; no PLE',
    },
    expr: pairs(8),
    assumptions: {},
    calls: [],
  });
  return rows;
}

export function legacyFixtures(): {
  id: string;
  expr: BooleanExpr;
  assumptions: VariableAssignments;
  maxConflicts: number;
}[] {
  const prereqs: [Variable, Variable][] = [
    ['b', 'a'],
    ['c', 'a'],
    ['e', 'd'],
    ['g', 'c'],
    ['f', 'c'],
    ['f', 'e'],
    ['h', 'b'],
    ['h', 'g'],
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
  // ae1a4fe Phase-4 record order, not an order regrouped by fixture family.
  return [
    {
      id: 'hypergraph',
      expr: and(...prereqs.map(([target, prereq]) => implies(target, prereq))),
      assumptions: { h: Value.TRUE },
      maxConflicts: 200_000,
    },
    ...[5, 6].map((pigeons) => ({
      id: `php_${pigeons}_${pigeons - 1}`,
      expr: cnfToExpr(phpCnf(pigeons, pigeons - 1)),
      assumptions: {},
      maxConflicts: 200_000,
    })),
    ...[42, 43, 44].map((seed) => ({
      id: `sat3_seed${seed}`,
      expr: cnfToExpr(random3Cnf(mulberry32(seed), 20, 85)),
      assumptions: {},
      maxConflicts: 200_000,
    })),
    ...[
      { pigeons: 7, holes: 6, maxConflicts: 7_230 },
      { pigeons: 8, holes: 7, maxConflicts: 36_270 },
    ].map(({ pigeons, holes, maxConflicts }) => ({
      id: `php_${pigeons}_${holes}`,
      expr: cnfToExpr(phpCnf(pigeons, holes)),
      assumptions: {},
      maxConflicts,
    })),
  ];
}
