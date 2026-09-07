// Tseitin compiler: BooleanExpr AST → CompiledCnf. Runs exactly once per
// solver instance, so variable collection and gate allocation are paid once
// per formula, never per search node. Literal encoding is MiniSat-style
// (lit = 2*v + isNeg), so negation is free and `not` nodes allocate nothing.
// The compiler produces literals; solver.ts imports these helpers — never the
// other way around. See Design § Formula Frontend and Tseitin Compilation.

import { getVariables, isVariable, Value } from './expr.js';
import type { BooleanExpr, Variable } from './expr.js';

// ---------------------------------------------------------------------------
// Literal helpers
// ---------------------------------------------------------------------------

// literal = 2*variableIndex + (isNegated ? 1 : 0)
export const posLit = (v: number): number => v * 2;
export const negLit = (v: number): number => v * 2 + 1;
export const varOf = (lit: number): number => lit >> 1;
export const isNeg = (lit: number): boolean => (lit & 1) === 1;
export const neg = (lit: number): number => lit ^ 1;

// Three-valued lookup of a literal against the solver's assignment array.
export const litValue = (lit: number, assigns: Int8Array): Value => {
  const value = assigns[varOf(lit)];
  if (value === Value.UNSET) {
    return Value.UNSET;
  }
  return value === (isNeg(lit) ? Value.FALSE : Value.TRUE) ? Value.TRUE : Value.FALSE;
};

// ---------------------------------------------------------------------------
// Clause database types
// ---------------------------------------------------------------------------

// One clause. Object identity is meaningful: watch lists and `reason` hold
// clause references (never indices), so clause deletion can never invalidate
// them. Units are detected structurally (`lits.length === 1`); they are
// enqueued at level 0 at solver construction and never enter watch lists.
// Compiled clauses are born with solver-side defaults (`learned: false`,
// `activity: 0`, `lbd: 0`); only learning/reduction bookkeeping writes them.
export interface Clause {
  lits: number[];
  learned: boolean;
  activity: number;
  lbd: number;
}

export interface CompiledCnf {
  // Total variable count: named (0..numNamedVars-1) + aux (numNamedVars..numVars-1).
  numVars: number;
  numNamedVars: number;
  clauses: Clause[];
  // Names → indices translate assumptions into literals; indices → names
  // project models back onto variable names.
  nameToIndex: Map<string, number>;
  indexToName: string[];
  // Set when compilation produces (or normalization reduces to) the empty
  // clause: the formula is UNSAT before search begins.
  levelZeroUnsat: boolean;
}

// ---------------------------------------------------------------------------
// Clause normalization
// ---------------------------------------------------------------------------

// Sort and deduplicate a raw literal list, detecting tautologies (a clause
// containing both `l` and `¬l` is always satisfied and must be dropped —
// returns null). Applied to every clause entering the database: compiled,
// learned, or blocking.
export function normalizeClauseLits(rawLits: readonly number[]): number[] | null {
  const seen = new Set<number>();
  for (const lit of rawLits) {
    if (seen.has(neg(lit))) {
      return null;
    }
    seen.add(lit);
  }
  return [...seen].sort((a, b) => a - b);
}

// ---------------------------------------------------------------------------
// Compilation
// ---------------------------------------------------------------------------

// Internal deterministic instrumentation of real compiler invocations,
// consumed by compile-once tests. Never re-exported by index.ts; recursive
// node compilation does not increment it.
export const compileCount = { value: 0 };

// A node that is itself a literal: a variable or a negated variable.
const isLiteralNode = (node: Variable | BooleanExpr): boolean =>
  isVariable(node) || ('not' in node && isVariable(node.not));

// Compile `expr` to CNF via the Tseitin transformation. Two rules eliminate
// gratuitous gates (see Design § Formula Frontend):
//
//   1. Free negation: compile(not(e)) = neg(compile(e)) — no aux variable
//      and no clauses are ever allocated for `not`.
//   2. Plain clauses in conjunctive position: an `and` in conjunctive
//      position distributes (each child is a separate conjunct, no gate), and
//      an `or` in conjunctive position whose inputs are all literals emits a
//      single plain clause. Every other compound node allocates one aux
//      variable `o` and emits the gate clauses from the Design table:
//        o ↔ AND(x₁..xₖ):  (¬o ∨ xᵢ) per input, plus (o ∨ ¬x₁ ∨ … ∨ ¬xₖ)
//        o ↔ OR(x₁..xₖ):   (o ∨ ¬xᵢ) per input, plus (¬o ∨ x₁ ∨ … ∨ xₖ)
//
// Each top-level conjunct that reduces to a literal is asserted with a unit
// clause. Clauses are normalized at creation; exact duplicates are dropped.
export function compile(expr: BooleanExpr): CompiledCnf {
  compileCount.value += 1;
  // Named variables are collected once, sorted for determinism, and indexed
  // 0..k-1; aux variables take indices k upward.
  const indexToName = [...getVariables(expr)].sort();
  const nameToIndex = new Map<string, number>(indexToName.map((name, index) => [name, index]));
  const numNamedVars = indexToName.length;

  const clauses: Clause[] = [];
  const clauseKeys = new Set<string>();
  let levelZeroUnsat = false;
  let nextAux = numNamedVars;

  // Cannot miss: every name reaching here came from the same getVariables(expr)
  // collection that built nameToIndex. The guard replaces what would otherwise
  // be a non-null assertion (forbidden by the project's lint rules).
  const indexOfName = (name: Variable): number => {
    const index = nameToIndex.get(name);
    if (index === undefined) {
      throw new Error(`variable missing from nameToIndex: ${name}`);
    }
    return index;
  };

  // Normalize and append one clause, dropping tautologies and exact
  // duplicates. The empty clause is kept and marks the formula UNSAT.
  const addClause = (rawLits: number[]): void => {
    const lits = normalizeClauseLits(rawLits);
    if (lits === null) {
      return;
    }
    if (lits.length === 0) {
      levelZeroUnsat = true;
    }
    const key = lits.join(',');
    if (clauseKeys.has(key)) {
      return;
    }
    clauseKeys.add(key);
    clauses.push({ lits, learned: false, activity: 0, lbd: 0 });
  };

  // Compile a node in any position, returning the literal that represents it.
  // Compound nodes allocate one aux variable and emit their gate clauses;
  // variables and `not` allocate nothing.
  const compileNode = (node: Variable | BooleanExpr): number => {
    if (isVariable(node)) {
      return posLit(indexOfName(node));
    }
    if ('not' in node) {
      return neg(compileNode(node.not));
    }
    const inputs = ('and' in node ? node.and : node.or).map(compileNode);
    const out = posLit(nextAux);
    nextAux += 1;
    if ('and' in node) {
      // out ↔ AND(inputs)
      for (const input of inputs) {
        addClause([neg(out), input]);
      }
      addClause([out, ...inputs.map(neg)]);
    } else {
      // out ↔ OR(inputs)
      for (const input of inputs) {
        addClause([out, neg(input)]);
      }
      addClause([neg(out), ...inputs]);
    }
    return out;
  };

  // Compile one conjunct: `and` distributes, an all-literal `or` emits a
  // single plain clause, and anything else is asserted as a unit clause over
  // its (possibly freshly gated) literal.
  const compileConjunct = (node: Variable | BooleanExpr): void => {
    if (!isVariable(node) && 'and' in node) {
      for (const child of node.and) {
        compileConjunct(child);
      }
      return;
    }
    if (!isVariable(node) && 'or' in node && node.or.every(isLiteralNode)) {
      addClause(node.or.map(compileNode));
      return;
    }
    addClause([compileNode(node)]);
  };

  compileConjunct(expr);

  return {
    numVars: nextAux,
    numNamedVars,
    clauses,
    nameToIndex,
    indexToName,
    levelZeroUnsat,
  };
}
