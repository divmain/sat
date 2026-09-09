// Tseitin compiler: BooleanExpr AST → CompiledCnf. Runs exactly once per
// solver instance, so variable collection and gate allocation are paid once
// per formula, never per search node. Literal encoding is MiniSat-style
// (lit = 2*v + isNeg), so negation is free and `not` nodes allocate nothing.
// The compiler produces literals; solver.ts imports these helpers — never the
// other way around. See Design § Formula Frontend and Tseitin Compilation.
//
// Compilation runs in two passes over a compilation-scoped canonical form
// (Design § Compiler and Encodings End-State):
//
//   1. Canonization maps the caller's AST to a compiler-owned canonical DAG.
//      Identity memoization visits each AST object once, eliminating the
//      exponential re-traversal of xor's duplicated operands. Structural
//      hash-consing (key = node kind + ordered child keys, with multiplicity
//      and order preserved) interns structurally identical subtrees to one
//      canonical object, so they share one gate at emission — xor(a,b)'s
//      duplicated operands share, while a future exactly(1,'a','a') still
//      counts two occurrences. Same-kind nesting is flattened (and under
//      and, or under or) and constants are folded totally: and() is true,
//      or() is false, an annihilating operand (false under and, true under
//      or) folds the whole node, identity constants drop out, and a single
//      surviving operand collapses to it. Folding is pure: no clauses or
//      aux variables are ever created for folded-away subtrees.
//   2. Emission walks the canonical DAG, keeping the two gratuitous-gate
//      eliminations (free negation; plain clauses in conjunctive position)
//      and allocating one aux gate per distinct canonical compound node,
//      shared by every occurrence.
//
// Correctness invariants, exercised per named assignment in compile.spec.ts:
// extension correctness (every satisfying total named assignment has a
// satisfying auxiliary extension — indeed unit propagation derives it by
// gate evaluation) and propagation refutation (every invalid total named
// assignment leaves a falsified clause at the propagation fixpoint). Full
// bidirectional gate clauses are the established encoding satisfying both;
// Plaisted-Greenbaum one-sided gates remain a deferred scope decision, and
// nothing here claims the refuted or(and(a,b),and(c,d)) named assignment
// discriminates PG (it is an ordinary invalid-model regression).
//
// All caches are scoped to a single compile() call and the canonical form is
// compiler-owned: caller ASTs are never mutated, mutating an AST between two
// compilations is observed by the second, and previously returned CompiledCnf
// handles never change.

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

// ---------------------------------------------------------------------------
// Canonical form
// ---------------------------------------------------------------------------

// A canonical node that can appear as a child of a compound node (never a
// constant — folding is total). `id` is a compilation-scoped dense interning
// id assigned when the node is interned: structural hash-consing keys are
// short strings of child ids rather than embedded child key strings, which
// would make key materialization exponential on shared DAGs (a left-deep xor
// chain's key would double in size per level).
type CanonChild =
  | { readonly kind: 'variable'; readonly name: Variable; readonly id: number }
  | { readonly kind: 'not'; readonly child: CanonChild; readonly id: number }
  | { readonly kind: 'and' | 'or'; readonly children: readonly CanonChild[]; readonly id: number };

// Compiler-owned canonical node: the output of canonization. `and`/`or`
// children are same-kind-flattened and constant-free (folding is total: no
// child is ever a constant, and compound nodes always have at least two
// children — empties fold to the identity constant, singletons collapse).
// Variables are named leaves; `not` wraps any non-constant child (negation
// stays free: it allocates nothing at emission).
type CanonExpr = CanonChild | { readonly kind: 'constant'; readonly value: boolean };

// A canonical node that is itself a literal: a variable or a negated
// variable. Mirrors the plain-clause carve-out's operand check.
const isLiteralCanon = (node: CanonExpr): boolean =>
  node.kind === 'variable' || (node.kind === 'not' && node.child.kind === 'variable');

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
  // 0..k-1; aux variables take indices k upward. Collection runs on the
  // original AST BEFORE any folding, so variables that constant folding
  // removes (e.g. every operand of or('a', and()), which folds to true)
  // remain in the named universe and appear in complete models.
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

  // -----------------------------------------------------------------------
  // Pass 1: canonization. Every cache is scoped to this one compilation.
  // -----------------------------------------------------------------------

  const canonLeafByName = new Map<Variable, CanonChild>();
  // Identity memo: each caller AST object is canonized exactly once, so a
  // subtree shared by k parents is traversed once, not k times.
  const canonByIdentity = new Map<BooleanExpr, CanonExpr>();
  // Structural hash-consing: key = node kind + ordered child interning ids.
  // Multiplicity and order are preserved (and(a,a) and and(a) differ;
  // or(a,b) and or(b,a) differ), which the future cardinality encoding
  // relies on. Children are interned before their parents (canonization is
  // bottom-up), so child ids always exist when a parent key is computed.
  const canonByKey = new Map<string, CanonChild>();
  let nextCanonId = 0;

  // Intern a compound canonical node: structurally identical nodes (same
  // kind, same ordered children) share one object — and hence one gate at
  // emission. Keys embed the FLATTENED, ordered child ids, so
  // and(a, and(b, c)) and and(a, b, c) intern to the same object.
  const internCanon = (key: string, node: CanonChild): CanonChild => {
    const existing = canonByKey.get(key);
    if (existing !== undefined) {
      return existing;
    }
    canonByKey.set(key, node);
    return node;
  };

  const canonize = (node: Variable | BooleanExpr): CanonExpr => {
    if (isVariable(node)) {
      const existing = canonLeafByName.get(node);
      if (existing !== undefined) {
        return existing;
      }
      const leaf: CanonChild = { kind: 'variable', name: node, id: nextCanonId };
      nextCanonId += 1;
      canonLeafByName.set(node, leaf);
      return leaf;
    }
    const cached = canonByIdentity.get(node);
    if (cached !== undefined) {
      return cached;
    }
    let result: CanonExpr;
    if ('not' in node) {
      const child = canonize(node.not);
      result =
        child.kind === 'constant'
          ? { kind: 'constant', value: !child.value }
          : internCanon(`not,${child.id}`, { kind: 'not', child, id: nextCanonId++ });
    } else {
      const isAnd = 'and' in node;
      // Flatten same-kind children and fold constants into a fresh
      // compiler-owned list; the caller's node and arrays are never mutated.
      const children: CanonChild[] = [];
      let annihilated = false;
      for (const childNode of isAnd ? node.and : node.or) {
        const child = canonize(childNode);
        if (child.kind === 'constant') {
          // false annihilates and; true annihilates or. Identity constants
          // (true under and, false under or) drop out.
          if (child.value !== isAnd) {
            annihilated = true;
            break;
          }
          continue;
        }
        if (child.kind === (isAnd ? 'and' : 'or')) {
          // Same-kind flattening, multiplicity- and order-preserving.
          children.push(...child.children);
        } else {
          children.push(child);
        }
      }
      if (annihilated) {
        result = { kind: 'constant', value: !isAnd };
      } else if (children.length === 0) {
        result = { kind: 'constant', value: isAnd };
      } else if (children.length === 1) {
        const only = children[0];
        if (only === undefined) {
          throw new Error('single-operand collapse lost its operand');
        }
        result = only;
      } else {
        const kind = isAnd ? 'and' : 'or';
        result = internCanon(`${kind},${children.map((child) => child.id).join(',')}`, {
          kind,
          children,
          id: nextCanonId++,
        });
      }
    }
    canonByIdentity.set(node, result);
    return result;
  };

  // -----------------------------------------------------------------------
  // Pass 2: emission over the canonical DAG.
  // -----------------------------------------------------------------------

  // One aux variable per distinct canonical gate node, allocated at the
  // node's first occurrence (children before parent, matching traversal
  // order); later occurrences of an identical structure reuse it.
  const gateLitByCanon = new Map<CanonExpr, number>();

  // Compile a canonical node in any position, returning the literal that
  // represents it. Compound nodes allocate one aux variable and emit their
  // gate clauses; variables and `not` allocate nothing. Constants never
  // reach here: folding is total, so no gate operand or conjunct is a
  // constant.
  const litOfCanon = (node: CanonExpr): number => {
    if (node.kind === 'variable') {
      return posLit(indexOfName(node.name));
    }
    if (node.kind === 'not') {
      return neg(litOfCanon(node.child));
    }
    if (node.kind === 'constant') {
      throw new Error('constants never appear as literals (folding is total)');
    }
    const cached = gateLitByCanon.get(node);
    if (cached !== undefined) {
      return cached;
    }
    const inputs = node.children.map(litOfCanon);
    const out = posLit(nextAux);
    nextAux += 1;
    if (node.kind === 'and') {
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
    gateLitByCanon.set(node, out);
    return out;
  };

  // Compile one conjunct: `and` distributes (canonization already flattened
  // same-kind nesting, so this is one flat pass), an all-literal `or` emits
  // a single plain clause, a constant folds away (a root-false fold is the
  // empty clause — UNSAT before search; a root-true fold emits nothing), and
  // anything else is asserted as a unit clause over its literal.
  const compileConjunct = (node: CanonExpr): void => {
    if (node.kind === 'and') {
      for (const child of node.children) {
        compileConjunct(child);
      }
      return;
    }
    if (node.kind === 'constant') {
      if (!node.value) {
        addClause([]);
      }
      return;
    }
    if (node.kind === 'or' && node.children.every(isLiteralCanon)) {
      addClause(node.children.map(litOfCanon));
      return;
    }
    addClause([litOfCanon(node)]);
  };

  compileConjunct(canonize(expr));

  return {
    numVars: nextAux,
    numNamedVars,
    clauses,
    nameToIndex,
    indexToName,
    levelZeroUnsat,
  };
}
