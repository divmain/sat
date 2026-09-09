// Tseitin compiler: BooleanExpr AST → CompiledCnf. compile() runs once per
// solver instance at construction, and the incremental entry point
// (compileIncremental) runs once per SatSolver.add() against the solver's
// shared symbol table, so variable collection and gate allocation are paid
// once per formula or staged delta, never per search node. Literal encoding
// is MiniSat-style (lit = 2*v + isNeg), so negation is free and `not` nodes
// allocate nothing. The compiler produces literals; solver.ts imports these
// helpers — never the other way around. See Design § Compiler and
// Encodings End-State.
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
//      shared by every occurrence. Cardinality nodes dispatch on position
//      (Design § Compiler): conjunctive atMost compiles to the pairwise
//      encoding (k = 1, n <= 6) or the Sinz sequential counter, conjunctive
//      atLeast(k, L) to atMost(n-k, ¬L), and nested (non-conjunctive)
//      occurrences reify their threshold through a fully bidirectional
//      Bailleux–Boufkhad totalizer.
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
// All caches are scoped to a single compile()/compileIncremental() call and
// the canonical form is compiler-owned: caller ASTs are never mutated,
// mutating an AST between two compilations is observed by the second, and
// previously returned CompiledCnf handles never change. Each staged add()
// delta owns its own caches and output, so an edited caller AST is read anew
// on re-addition while previously admitted constraints stay untouched.

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
// node compilation does not increment it. Each SatSolver.add() stages one
// compileIncremental() call, so it ticks exactly once per addition.
export const compileCount = { value: 0 };

// ---------------------------------------------------------------------------
// Node validation
// ---------------------------------------------------------------------------

// A readable one-liner for a node that failed validation.
const describeNode = (node: unknown): string => {
  if (node === null) {
    return 'null';
  }
  if (Array.isArray(node)) {
    return 'an array';
  }
  const kind = typeof node;
  if (kind === 'object') {
    return `object ${JSON.stringify(Object.keys(node as object))}`;
  }
  // String() — never a template literal — so a symbol payload cannot throw.
  return `${kind} ${String(node)}`;
};

// Full structural validation for hand-built ASTs (Design § Compiler and
// Encodings End-State): the constructors build valid nodes by construction,
// but consumers may hand-build objects, so the compiler validates every node
// before variable collection reads it. A node is a variable string or an
// object carrying EXACTLY one operator key — 'and'/'or' with an array of
// operands, 'not' with one operand, or 'atMost'/'atLeast' with a
// `{ k, exprs }` payload whose `k` is a non-negative safe integer. Validation
// rejects anything else with a descriptive Error: non-object non-string
// nodes, arrays as nodes, missing operator keys, MULTIPLE operator keys
// (variable collection dispatches on 'and' first while canonization
// dispatches on 'not' first, so a multi-key node would silently diverge
// between the named universe and the emitted clauses), non-array operands,
// malformed cardinality payloads or out-of-domain `k` (the constructors
// reject those too, but hand-built nodes bypass them), and cyclic graphs.
// Identity memoization keeps sharing (xor's duplicated operands) linear; a
// re-visit on the active path is a cycle, never a finite expression.
// Operator keys are probed with `in`, matching the dispatch semantics of the
// traversals this guards. A bare variable string is a valid OPERAND at any
// nested position but never a valid top-level formula: BooleanExpr is an
// operator object, and variable collection dispatches with `'and' in expr`,
// which a primitive string cannot even be probed by (a raw engine TypeError,
// not a descriptive validation Error).
function validateExpression(expr: BooleanExpr): void {
  if (typeof expr === 'string') {
    throw new Error(
      `invalid BooleanExpr at $: expected an and/or/not/atMost/atLeast object, got ${describeNode(
        expr,
      )}`,
    );
  }
  const visiting = new Set<object>();
  const visited = new Set<unknown>();
  const visit = (node: unknown, path: string): void => {
    if (typeof node === 'string') {
      return;
    }
    if (node === null || typeof node !== 'object' || Array.isArray(node)) {
      throw new Error(
        `invalid BooleanExpr at ${path}: expected a variable string or an and/or/not/atMost/atLeast object, got ${describeNode(
          node,
        )}`,
      );
    }
    if (visiting.has(node)) {
      throw new Error(`invalid BooleanExpr at ${path}: cyclic expression graph`);
    }
    if (visited.has(node)) {
      return;
    }
    visiting.add(node);
    const operators = ['and', 'or', 'not', 'atMost', 'atLeast'].filter((key) => key in node);
    if (operators.length !== 1) {
      throw new Error(
        `invalid BooleanExpr at ${path}: a node must carry exactly one of 'and', 'or', 'not', 'atMost', 'atLeast' (found ${
          operators.length === 0 ? 'none' : operators.join(', ')
        })`,
      );
    }
    const operator = operators[0];
    if (operator === 'not') {
      visit((node as { not: unknown }).not, `${path}.not`);
    } else if (operator === 'and' || operator === 'or') {
      const operands = (node as Record<string, unknown>)[operator];
      if (!Array.isArray(operands)) {
        throw new Error(`invalid BooleanExpr at ${path}.${operator}: operands must be an array`);
      }
      for (const [index, child] of operands.entries()) {
        visit(child, `${path}.${operator}[${index}]`);
      }
    } else {
      // atMost/atLeast: a { k, exprs } payload with a non-negative
      // safe-integer bound and an operand array.
      const payload = (node as Record<string, unknown>)[operator];
      if (payload === null || typeof payload !== 'object' || Array.isArray(payload)) {
        throw new Error(
          `invalid BooleanExpr at ${path}.${operator}: expected a { k, exprs } payload object, got ${describeNode(
            payload,
          )}`,
        );
      }
      const { k, exprs } = payload as { k: unknown; exprs: unknown };
      if (typeof k !== 'number' || !Number.isSafeInteger(k) || k < 0) {
        throw new Error(
          `invalid BooleanExpr at ${path}.${operator}: k must be a non-negative safe integer (got ${describeNode(
            k,
          )})`,
        );
      }
      if (!Array.isArray(exprs)) {
        throw new Error(`invalid BooleanExpr at ${path}.${operator}: exprs must be an array`);
      }
      for (const [index, child] of exprs.entries()) {
        visit(child, `${path}.${operator}.exprs[${index}]`);
      }
    }
    visiting.delete(node);
    visited.add(node);
  };
  visit(expr, '$');
}

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
  | { readonly kind: 'and' | 'or'; readonly children: readonly CanonChild[]; readonly id: number }
  | {
      readonly kind: 'atMost' | 'atLeast';
      readonly k: number;
      readonly children: readonly CanonChild[];
      readonly id: number;
    };

// Compiler-owned canonical node: the output of canonization. `and`/`or`
// children are same-kind-flattened and constant-free (folding is total: no
// child is ever a constant, and compound nodes always have at least two
// children — empties fold to the identity constant, singletons collapse).
// Variables are named leaves; `not` wraps any non-constant child (negation
// stays free: it allocates nothing at emission). Cardinality children are a
// MULTISET — never flattened, sorted, or deduplicated — with constants folded
// out against the bound (true operands decrement k, false operands drop) and
// the four pinned edge folds applied (Design § Compiler: atLeast(k<=0) →
// true, atMost(k>=n) → true, atLeast(k>n) → false, atMost(0) → a conjunction
// of negated operands; an atMost folded negative by true constants is false).
// Surviving canonical cardinality nodes therefore satisfy 1 <= k < n for
// atMost and 1 <= k <= n for atLeast, with n >= 1 non-constant operands.
type CanonExpr = CanonChild | { readonly kind: 'constant'; readonly value: boolean };

// A canonical node that is itself a literal: a variable or a negated
// variable. Mirrors the plain-clause carve-out's operand check.
const isLiteralCanon = (node: CanonExpr): boolean =>
  node.kind === 'variable' || (node.kind === 'not' && node.child.kind === 'variable');

// ---------------------------------------------------------------------------
// The shared compilation engine
// ---------------------------------------------------------------------------

// The symbol-table base a staged delta compiles against: the solver's current
// name → index map and total variable count (named + aux). Read-only to the
// compiler — a delta never mutates it, so a failed add() leaves the solver's
// table byte-for-byte unchanged.
export interface IncrementalCompileBase {
  readonly nameToIndex: ReadonlyMap<Variable, number>;
  readonly numVars: number;
}

// A staged compilation delta (Design § Incremental Clause Addition). New
// named variables are sorted within the batch and appended after ALL existing
// indices (including auxiliaries), occupying
// base.numVars .. base.numVars + newNames.length - 1; new auxiliaries
// continue from there, so aux allocation keeps growing monotonically. The
// delta owns its clauses and name list outright; nothing here aliases or
// mutates caller ASTs or the base table, and committing it is the solver's
// job (failure-atomic: a throw during compilation stages nothing).
export interface CompiledDelta {
  readonly newNames: Variable[];
  readonly clauses: Clause[];
  // Total variable count once the delta is committed: base + new named + new aux.
  readonly numVars: number;
  readonly levelZeroUnsat: boolean;
}

// Compile `expr` to CNF via the Tseitin transformation. Two rules eliminate
// gratuitous gates (see Design § Compiler and Encodings End-State):
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
// `base` carries the existing symbol table (empty for a fresh compile): known
// names keep their indices, and new names are sorted within the batch and
// appended after every existing index.
function compileDelta(expr: BooleanExpr, base: IncrementalCompileBase): CompiledDelta {
  // Full node validation for hand-built ASTs runs BEFORE variable collection,
  // so no malformed node can reach any traversal.
  validateExpression(expr);
  // Named variables are collected once and indexed deterministically; aux
  // variables take indices past the named batch. Collection runs on the
  // original AST BEFORE any folding, so variables that constant folding
  // removes (e.g. every operand of or('a', and()), which folds to true)
  // remain in the named universe and appear in complete models. A fresh
  // compile sorts ALL names into 0..k-1; an incremental delta keeps existing
  // indices and appends its new names sorted, after all existing indices.
  const newNames: Variable[] = [];
  for (const name of getVariables(expr)) {
    if (!base.nameToIndex.has(name)) {
      newNames.push(name);
    }
  }
  newNames.sort();
  const batchIndex = new Map<Variable, number>(
    newNames.map((name, offset) => [name, base.numVars + offset]),
  );

  const clauses: Clause[] = [];
  const clauseKeys = new Set<string>();
  let levelZeroUnsat = false;
  let nextAux = base.numVars + newNames.length;

  // Cannot miss: every name reaching here came from the same getVariables(expr)
  // collection that built the base table / batch index. The guard replaces
  // what would otherwise be a non-null assertion (forbidden by the project's
  // lint rules).
  const indexOfName = (name: Variable): number => {
    const existing = base.nameToIndex.get(name);
    if (existing !== undefined) {
      return existing;
    }
    const assigned = batchIndex.get(name);
    if (assigned === undefined) {
      throw new Error(`variable missing from the symbol table: ${name}`);
    }
    return assigned;
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
    } else if ('and' in node || 'or' in node) {
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
    } else {
      // Cardinality node (validation guarantees exactly one operator key).
      // The operand multiset is preserved — never flattened, sorted, or
      // deduplicated — so exactly(1,'a','a') counts two occurrences of 'a'.
      // Constant folding is total: a true operand consumes one unit of the
      // bound, a false operand drops out, and the edge folds then fire on the
      // adjusted bound.
      const payload = 'atMost' in node ? node.atMost : node.atLeast;
      const isAtMost = 'atMost' in node;
      let trueCount = 0;
      const children: CanonChild[] = [];
      for (const operand of payload.exprs) {
        const child = canonize(operand);
        if (child.kind === 'constant') {
          if (child.value) {
            trueCount += 1;
          }
          continue;
        }
        children.push(child);
      }
      const k = payload.k - trueCount;
      const n = children.length;
      if (isAtMost) {
        if (k < 0) {
          // True constants alone already exceed the bound.
          result = { kind: 'constant', value: false };
        } else if (k === 0) {
          // atMost(0, L) asserts every operand false: fold to a conjunction
          // of negations (which collapses/distributes like any and-node).
          const negated = children.map((child) =>
            internCanon(`not,${child.id}`, { kind: 'not', child, id: nextCanonId++ }),
          );
          if (negated.length === 0) {
            result = { kind: 'constant', value: true };
          } else if (negated.length === 1) {
            const only = negated[0];
            if (only === undefined) {
              throw new Error('atMost(0) fold lost its operand');
            }
            result = only;
          } else {
            result = internCanon(`and,${negated.map((child) => child.id).join(',')}`, {
              kind: 'and',
              children: negated,
              id: nextCanonId++,
            });
          }
        } else if (k >= n) {
          result = { kind: 'constant', value: true };
        } else {
          result = internCanon(`atMost,${k},${children.map((child) => child.id).join(',')}`, {
            kind: 'atMost',
            k,
            children,
            id: nextCanonId++,
          });
        }
      } else {
        if (k <= 0) {
          result = { kind: 'constant', value: true };
        } else if (k > n) {
          result = { kind: 'constant', value: false };
        } else {
          result = internCanon(`atLeast,${k},${children.map((child) => child.id).join(',')}`, {
            kind: 'atLeast',
            k,
            children,
            id: nextCanonId++,
          });
        }
      }
    }
    canonByIdentity.set(node, result);
    return result;
  };

  // -----------------------------------------------------------------------
  // Pass 2: emission over the canonical DAG.
  // -----------------------------------------------------------------------

  // Bounds-checked access: every index reaching here comes from the encoding
  // loops' own ranges, so a miss is a compiler bug, not bad input. The guard
  // replaces what would otherwise be a non-null assertion (forbidden by the
  // project's lint rules).
  const litAt = <Item>(items: readonly Item[], index: number): Item => {
    const item = items[index];
    if (item === undefined) {
      throw new Error('encoding index out of range');
    }
    return item;
  };

  // One aux variable per distinct canonical gate node, allocated at the
  // node's first occurrence (children before parent, matching traversal
  // order); later occurrences of an identical structure reuse it.
  const gateLitByCanon = new Map<CanonExpr, number>();

  // Bailleux–Boufkhad totalizer over the input literals (Design § Compiler),
  // FULLY reified in both directions because a nested cardinality output must
  // be equivalent to its threshold in both polarities. Returns the unary
  // count outputs u_1..u_n with u_s ⟺ (at least s inputs are true). A leaf
  // aliases its input literal (no aux, no clauses). An internal node whose
  // children cover p and q inputs allocates p + q auxiliaries o_1..o_{p+q}
  // and links them to the child outputs with, for every 0 <= a <= p and
  // 0 <= b <= q:
  //
  //   (¬l_a ∨ ¬r_b ∨ o_{a+b})        — countL ≥ a ∧ countR ≥ b ⇒ count ≥ a+b
  //   (l_{a+1} ∨ r_{b+1} ∨ ¬o_{a+b+1}) — count ≥ a+b+1 ⇒ countL > a ∨ countR > b
  //
  // where l_0/r_0 are true (their negations drop out of the first form) and
  // l_{p+1}/r_{q+1} are false (they drop out of the second). Unit propagation
  // from a total input assignment derives every output in both directions, so
  // the nested encoding satisfies the full-gate oracle: valid assignments
  // satisfy every clause and invalid ones are propagation-refuted.
  const totalizerOutputs = (lits: readonly number[]): number[] => {
    if (lits.length === 1) {
      return [litAt(lits, 0)];
    }
    const mid = lits.length >> 1;
    const left = totalizerOutputs(lits.slice(0, mid));
    const right = totalizerOutputs(lits.slice(mid));
    const p = left.length;
    const q = right.length;
    const outputs: number[] = [];
    for (let s = 1; s <= p + q; s += 1) {
      outputs.push(posLit(nextAux));
      nextAux += 1;
    }
    for (let a = 0; a <= p; a += 1) {
      for (let b = 0; b <= q; b += 1) {
        const sum = a + b;
        if (sum >= 1) {
          const clause = [litAt(outputs, sum - 1)];
          if (a >= 1) {
            clause.push(neg(litAt(left, a - 1)));
          }
          if (b >= 1) {
            clause.push(neg(litAt(right, b - 1)));
          }
          addClause(clause);
        }
        if (sum + 1 <= p + q) {
          const clause = [neg(litAt(outputs, sum))];
          if (a + 1 <= p) {
            clause.push(litAt(left, a));
          }
          if (b + 1 <= q) {
            clause.push(litAt(right, b));
          }
          addClause(clause);
        }
      }
    }
    return outputs;
  };

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
    if (node.kind === 'atMost' || node.kind === 'atLeast') {
      // Nested (non-conjunctive) cardinality: compound inputs are reified
      // first by the ordinary gate path, then the totalizer output gives the
      // threshold literal — atLeast(k) ⟺ u_k and atMost(k) ⟺ ¬u_{k+1}
      // (canonization's folds leave 1 <= k <= n for atLeast and
      // 1 <= k < n for atMost, so both outputs exist).
      const outputs = totalizerOutputs(inputs);
      const out =
        node.kind === 'atLeast' ? litAt(outputs, node.k - 1) : neg(litAt(outputs, node.k));
      gateLitByCanon.set(node, out);
      return out;
    }
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

  // Conjunctive cardinality nodes already asserted, by canonical identity:
  // and-flattening preserves multiplicity, so a repeated conjunct mentions
  // the same interned node twice — asserting it again would allocate a
  // second auxiliary population for an identical constraint.
  const assertedCardinality = new Set<CanonExpr>();

  // Assert `inputs sum to at most k` as a conjunct (Design § Compiler:
  // encodings dispatch on the NODE, never the constructor — atMostOne's AST
  // is atMost(1, …)). Canonization's edge folds fired first, so only
  // 0 <= k < n reaches here (k = 0 arises from the conjunctive atLeast
  // rewrite below, never from a surviving atMost node). k = 1 with n <= 6
  // uses the pairwise encoding — one binary clause per operand pair, no
  // auxiliaries; every other case uses the Sinz sequential counter. These
  // are ASSERTED counters, not reified ones: every satisfying named
  // valuation admits a satisfying auxiliary extension and every violating
  // total named valuation is refuted by unit propagation, but a valid
  // valuation need not determine the auxiliaries.
  const emitConjunctiveAtMost = (k: number, inputs: readonly number[]): void => {
    const n = inputs.length;
    if (k === 0) {
      // atMost(0, L): every input false, one unit clause per input.
      for (const input of inputs) {
        addClause([neg(input)]);
      }
      return;
    }
    if (k === 1 && n <= 6) {
      // Pairwise: no two inputs both true.
      for (let i = 0; i < n; i += 1) {
        for (let j = i + 1; j < n; j += 1) {
          addClause([neg(litAt(inputs, i)), neg(litAt(inputs, j))]);
        }
      }
      return;
    }
    // Sinz sequential counter: s(i, j) for 1 <= i <= n-1, 1 <= j <= k means
    // "at least j of the first i inputs are true" (auxiliaries allocated
    // row-major). The clause groups are, with x_i the i-th input:
    //   (1) (¬x_i ∨ s_{i,1})                    1 <= i <= n-1
    //   (2) (¬s_{i-1,j} ∨ s_{i,j})              2 <= i <= n-1, 1 <= j <= k
    //   (3) (¬x_i ∨ ¬s_{i-1,j-1} ∨ s_{i,j})     2 <= i <= n-1, 2 <= j <= k
    //   (4) (¬x_i ∨ ¬s_{i-1,k})                 2 <= i <= n
    // More than k true inputs propagate a conflict by (1)-(4); at most k
    // true inputs admit the extension s_{i,j} = (count of the first i >= j).
    const rows: number[][] = [];
    for (let i = 1; i <= n - 1; i += 1) {
      const row: number[] = [];
      for (let j = 1; j <= k; j += 1) {
        row.push(posLit(nextAux));
        nextAux += 1;
      }
      rows.push(row);
    }
    const s = (i: number, j: number): number => litAt(litAt(rows, i - 1), j - 1);
    for (let i = 1; i <= n - 1; i += 1) {
      addClause([neg(litAt(inputs, i - 1)), s(i, 1)]);
    }
    for (let i = 2; i <= n - 1; i += 1) {
      for (let j = 1; j <= k; j += 1) {
        addClause([neg(s(i - 1, j)), s(i, j)]);
      }
    }
    for (let i = 2; i <= n - 1; i += 1) {
      for (let j = 2; j <= k; j += 1) {
        addClause([neg(litAt(inputs, i - 1)), neg(s(i - 1, j - 1)), s(i, j)]);
      }
    }
    for (let i = 2; i <= n; i += 1) {
      addClause([neg(litAt(inputs, i - 1)), neg(s(i - 1, k))]);
    }
  };

  // Compile one conjunct: `and` distributes (canonization already flattened
  // same-kind nesting, so this is one flat pass), an all-literal `or` emits
  // a single plain clause, a constant folds away (a root-false fold is the
  // empty clause — UNSAT before search; a root-true fold emits nothing), a
  // cardinality node asserts its conjunctive encoding (atLeast(k, L) as
  // atMost(n-k, ¬L); the folds fired before this rewrite, so n-k never goes
  // negative), and anything else is asserted as a unit clause over its
  // literal.
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
    if (node.kind === 'atMost' || node.kind === 'atLeast') {
      if (assertedCardinality.has(node)) {
        return;
      }
      assertedCardinality.add(node);
      const inputs = node.children.map(litOfCanon);
      if (node.kind === 'atMost') {
        emitConjunctiveAtMost(node.k, inputs);
      } else {
        emitConjunctiveAtMost(
          node.children.length - node.k,
          inputs.map((input) => neg(input)),
        );
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

  return { newNames, clauses, numVars: nextAux, levelZeroUnsat };
}

// Compile a complete formula into a standalone CNF: every name is new, sorted
// into indices 0..k-1, with auxiliaries numbered k upward.
export function compile(expr: BooleanExpr): CompiledCnf {
  compileCount.value += 1;
  const delta = compileDelta(expr, { nameToIndex: new Map(), numVars: 0 });
  const indexToName = [...delta.newNames];
  const nameToIndex = new Map<string, number>(indexToName.map((name, index) => [name, index]));
  return {
    numVars: delta.numVars,
    numNamedVars: indexToName.length,
    clauses: delta.clauses,
    nameToIndex,
    indexToName,
    levelZeroUnsat: delta.levelZeroUnsat,
  };
}

// The incremental entry point behind SatSolver.add() (Design § Incremental
// Clause Addition): compile `expr` against the solver's existing symbol
// table, returning a staged delta. Known names keep their indices; new named
// variables are sorted within this batch and appended after all existing
// indices (auxiliaries included); new auxiliaries continue from there. The
// delta owns its compilation caches and output: an edited caller AST is read
// anew on a later addition, and previously returned CompiledCnf handles (and
// previously admitted deltas) never change. A throw stages nothing.
export function compileIncremental(expr: BooleanExpr, base: IncrementalCompileBase): CompiledDelta {
  compileCount.value += 1;
  return compileDelta(expr, base);
}
