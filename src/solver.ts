// Mutable solver state, MiniSat-style two-watched-literal unit propagation,
// scoped pure-literal elimination, and iterative first-UIP CDCL search with
// non-chronological backjumping, VSIDS branching, phase saving, Luby restarts,
// and periodic learned-clause reduction with learning-time LBD protection.
// propagate() keeps its original contract
// (returns the conflicting Clause | null); the public contract stays fixed.
// See Design § Solver Core State and Invariants and § Search: From DPLL to
// CDCL.

import { isNeg, litValue, neg, normalizeClauseLits, varOf } from './compile.js';
import type { Clause, CompiledCnf } from './compile.js';
import { Value } from './expr.js';
import type { Variable, VariableAssignments } from './expr.js';

export interface SolverStats {
  decisions: number;
  propagations: number;
  conflicts: number;
  restarts: number;
  learnedClauses: number;
  learnedClausesCurrent: number;
}

export type VariablePriority = (
  unassigned: Variable[],
  assignments: Partial<Record<Variable, Value>>,
) => [Variable, boolean] | null;

interface SolverOptions {
  assumptions?: VariableAssignments | undefined;
  variablePriority?: VariablePriority | undefined;
  enablePle?: boolean | undefined;
  stats?: SolverStats | undefined;
  maxConflicts?: number | undefined;
  // Internal conflict-budget calibration only; never forwarded by public options.
  restartBaseConflicts?: number | undefined;
  // New learned admissions per reduction round, not a cap on protected clauses.
  // Internal only: neither this knob nor Solver is exported by the public API.
  learnedClauseReductionThreshold?: number | undefined;
}

const DEBUG_ASSERTIONS = process.env.NODE_ENV !== 'production';

// One-based Luby sequence: S_k = S_(k-1), S_(k-1), 2^(k-1).
// Find the containing block, then descend iteratively into its two copies.
// Arithmetic, not bitwise shifts, keeps indices beyond 32 bits exact. This
// helper is exported only from the internal module, not the package API.
export function luby(index: number): number {
  if (!Number.isSafeInteger(index) || index < 1) {
    throw new Error('Luby index must be a positive safe integer');
  }
  let size = 1;
  let value = 1;
  while (size < index) {
    size = size * 2 + 1;
    value *= 2;
  }
  while (index !== size) {
    size = (size - 1) / 2;
    value /= 2;
    if (index > size) {
      index -= size;
    }
  }
  return value;
}

function emptyStats(): SolverStats {
  return {
    decisions: 0,
    propagations: 0,
    conflicts: 0,
    restarts: 0,
    learnedClauses: 0,
    learnedClausesCurrent: 0,
  };
}

export class Solver {
  readonly assigns: Int8Array;
  readonly level: Int32Array;
  readonly reason: Array<Clause | null>;
  readonly activity: Float64Array;
  readonly polarity: Int8Array;
  readonly trail: number[] = [];
  readonly trailLim: number[] = [];
  qhead = 0;

  readonly clauses: Clause[];
  // Two-watched-literal lists: `watches[l]` holds every clause currently
  // watching literal `l` — i.e. l is one of that clause's two watched
  // literals, kept at clause.lits[0] or clause.lits[1] (the MiniSat in-place
  // swap convention). Watch lists hold clause object references, never
  // indices, so Phase-3 clause deletion stays safe by construction. Clause
  // attachment and propagation's watch relocation preserve that identity.
  readonly watches: Clause[][];
  readonly stats: SolverStats;
  readonly variablePriority: VariablePriority | undefined;

  private readonly cnf: CompiledCnf;
  private readonly enablePle: boolean;
  private readonly maxConflicts: number | undefined;
  private readonly restartBaseConflicts: number;
  private readonly learnedClauseReductionThreshold: number;
  private learnedSinceReduction = 0;
  // Semantic clause identity must not depend on the mutable watch order.
  private readonly clauseByKey = new Map<string, Clause>();
  private readonly seen: Uint8Array;
  private varInc = 1;
  // Indexed binary max-heap, ordered by activity then LOWER variable index.
  // Only named variables have positions; -1 means absent. Assignments made
  // by propagation or the hook remain lazily in the heap until popped.
  private readonly decisionHeap: number[];
  private readonly heapPosition: Int32Array;
  // An O(1) termination check avoids scanning all named variables at every
  // decision, which would defeat the heap's logarithmic selection cost.
  private unassignedNamed: number;
  // The internal cap bounds this instance's work, including all enumeration
  // searches, independently of any pre-existing output-counter offsets.
  private conflictsSoFar = 0;
  private startupConflict: Clause | null = null;
  private startupConflictReported = false;
  private permanentUnsat = false;
  private incrementalCallActive = false;

  constructor(cnf: CompiledCnf, opts: SolverOptions = {}) {
    if (
      opts.maxConflicts !== undefined &&
      (!Number.isInteger(opts.maxConflicts) || opts.maxConflicts < 0)
    ) {
      throw new Error('maxConflicts must be a non-negative integer');
    }
    if (
      opts.restartBaseConflicts !== undefined &&
      (!Number.isSafeInteger(opts.restartBaseConflicts) || opts.restartBaseConflicts < 1)
    ) {
      throw new Error('restartBaseConflicts must be a positive safe integer');
    }
    if (
      opts.learnedClauseReductionThreshold !== undefined &&
      (!Number.isSafeInteger(opts.learnedClauseReductionThreshold) ||
        opts.learnedClauseReductionThreshold < 1)
    ) {
      throw new Error('learnedClauseReductionThreshold must be a positive safe integer');
    }

    this.cnf = cnf;
    this.assigns = new Int8Array(cnf.numVars).fill(Value.UNSET);
    this.level = new Int32Array(cnf.numVars);
    this.reason = Array<Clause | null>(cnf.numVars).fill(null);
    this.seen = new Uint8Array(cnf.numVars);
    this.activity = new Float64Array(cnf.numVars);
    this.polarity = new Int8Array(cnf.numVars).fill(Value.FALSE);
    this.decisionHeap = [];
    this.heapPosition = new Int32Array(cnf.numNamedVars);
    this.unassignedNamed = cnf.numNamedVars;
    // All initial activities tie, so index order is already a valid heap.
    for (let variable = 0; variable < cnf.numNamedVars; variable += 1) {
      this.decisionHeap.push(variable);
      this.heapPosition[variable] = variable;
    }
    this.clauses = [];
    this.watches = Array.from({ length: cnf.numVars * 2 }, () => []);
    this.stats = opts.stats ?? emptyStats();
    this.variablePriority = opts.variablePriority;
    this.enablePle = opts.enablePle ?? false;
    this.maxConflicts = opts.maxConflicts;
    this.restartBaseConflicts = opts.restartBaseConflicts ?? 100;
    this.learnedClauseReductionThreshold = opts.learnedClauseReductionThreshold ?? 10_000;

    // Add clauses before assumptions. Units are deliberately absent from
    // watch lists: they are asserted once at level zero instead. Every
    // clause of length >= 2 watches its first two literals (positions 0 and
    // 1); later propagation relocates a watch by swapping it into the
    // falsified literal's slot. The empty clause short-circuits UNSAT.
    for (const clause of cnf.clauses) {
      const normalized = normalizeClauseLits(clause.lits);
      if (normalized === null) {
        continue;
      }
      const key = normalized.join(',');
      if (this.clauseByKey.has(key)) {
        continue;
      }
      // Compiled clauses are already normalized. Preserve their order and
      // object identity; use a sorted COPY only for the canonical key.
      if (normalized.length !== clause.lits.length) {
        clause.lits = normalized;
      }
      this.clauseByKey.set(key, clause);
      this.clauses.push(clause);
      if (clause.lits.length === 0) {
        this.startupConflict ??= clause;
      } else if (clause.lits.length === 1) {
        const lit = clause.lits[0];
        const wasUnset = this.assigns[varOf(lit)] === Value.UNSET;
        if (!this.enqueue(lit, clause)) {
          this.startupConflict ??= clause;
        } else if (wasUnset) {
          this.stats.propagations += 1;
        }
      } else {
        this.attachClause(clause);
      }
    }

    this.enqueueAssumptions(opts.assumptions);
    this.assertTrailInvariant();
  }

  enqueue(lit: number, reason: Clause | null): boolean {
    const variable = varOf(lit);
    if (variable < 0 || variable >= this.assigns.length) {
      throw new Error(`cannot enqueue out-of-range literal: ${lit}`);
    }
    const wanted = isNeg(lit) ? Value.FALSE : Value.TRUE;
    const current = this.assigns[variable];
    if (current !== Value.UNSET) {
      this.assertTrailInvariant();
      return current === wanted;
    }

    this.assigns[variable] = wanted;
    // Save EVERY successful new assignment, including implications, root
    // units/assumptions, PLE and learned assertions — not just decisions or
    // cancelled assignments. A hook override becomes the latest phase too.
    this.polarity[variable] = wanted;
    if (variable < this.cnf.numNamedVars) {
      this.unassignedNamed -= 1;
    }
    this.level[variable] = this.trailLim.length;
    this.reason[variable] = reason;
    this.trail.push(lit);
    this.assertTrailInvariant();
    return true;
  }

  propagate(): Clause | null {
    if (this.startupConflict !== null) {
      if (!this.startupConflictReported) {
        this.recordConflict();
        this.startupConflictReported = true;
      }
      return this.startupConflict;
    }

    // Two-watched-literal propagation (MiniSat scheme). The trail is drained
    // from `qhead`; dequeuing the (now true) literal `assignedLit` falsifies
    // `neg(assignedLit)`, so only `watches[neg(assignedLit)]` — the clauses
    // whose watched literal just became false — must be examined. Per clause:
    //   1. Normalize the falsified watched literal into slot 1 (in-place
    //      swap), so slot 0 holds the other watch.
    //   2. Blocking-literal optimization: if the other watch is already
    //      true, the clause is satisfied — nothing to do.
    //   3. Scan slots 2.. for any literal that is not false; the first such
    //      literal becomes the replacement watch (in-place swap: slot 1 takes
    //      the candidate, the falsified literal moves into the vacated slot;
    //      the clause is removed from this list and appended to the
    //      candidate's list). If none exists, the clause is unit (enqueue the
    //      other watch) or conflicting (return it).
    // The list is mutated while iterated, so it is walked backwards: removing
    // a clause swaps the current slot with the last element and pops, and
    // every element above the current slot has already been examined, so no
    // unexamined clause can be displaced. Clauses that are unit or that stay
    // watching the falsified literal remain in the list.
    while (this.qhead < this.trail.length) {
      const assignedLit = this.trail[this.qhead];
      this.qhead += 1;
      const falseLit = neg(assignedLit);
      const watchList = this.watches[falseLit];
      if (watchList === undefined) {
        throw new Error(`missing watch list for literal: ${falseLit}`);
      }

      for (let index = watchList.length - 1; index >= 0; index -= 1) {
        const clause = watchList[index];
        if (clause.lits[0] === falseLit) {
          clause.lits[0] = clause.lits[1];
          clause.lits[1] = falseLit;
        }
        const otherWatch = clause.lits[0];

        if (litValue(otherWatch, this.assigns) === Value.TRUE) {
          continue;
        }

        let relocated = false;
        for (let k = 2; k < clause.lits.length; k += 1) {
          const candidate = clause.lits[k];
          if (litValue(candidate, this.assigns) !== Value.FALSE) {
            clause.lits[1] = candidate;
            clause.lits[k] = falseLit;
            const candidateWatchList = this.watches[candidate];
            if (candidateWatchList === undefined) {
              throw new Error(`missing watch list for literal: ${candidate}`);
            }
            candidateWatchList.push(clause);
            const lastIndex = watchList.length - 1;
            watchList[index] = watchList[lastIndex];
            watchList.pop();
            relocated = true;
            break;
          }
        }
        if (relocated) {
          continue;
        }

        if (litValue(otherWatch, this.assigns) === Value.FALSE) {
          this.recordConflict();
          return clause;
        }
        if (!this.enqueue(otherWatch, clause)) {
          this.recordConflict();
          return clause;
        }
        this.stats.propagations += 1;
      }
    }

    return null;
  }

  // Analyze before cancelling: reasons and levels describe an acyclic
  // implication graph whose conflict clause is falsified. Walk ALL enqueued
  // assignments backwards, including the tail not yet processed by propagate.
  // A count of one current-level literal is the first UIP, even if its reason
  // is non-null; resolving past it would instead learn a later/decision UIP.
  analyze(conflict: Clause): { learned: Clause; backjumpLevel: number } {
    const currentLevel = this.trailLim.length;
    if (currentLevel === 0) {
      throw new Error('conflict analysis requires a nonzero decision level');
    }
    if (!conflict.lits.every((lit) => litValue(lit, this.assigns) === Value.FALSE)) {
      throw new Error('conflict analysis requires a falsified clause');
    }

    this.seen.fill(0);
    const learnedLits: number[] = [];
    let currentCount = 0;
    let trailIndex = this.trail.length - 1;
    let resolvedVariable = -1;
    let clause = conflict;
    let assertingLit: number;
    while (true) {
      // Usage count, not decayed activity: the conflict seed and every reason
      // actually consumed get +1. The UIP's reason is NOT consumed or bumped.
      clause.activity += 1;
      for (const lit of clause.lits) {
        const variable = varOf(lit);
        // Reason watch slots can move, so skip the pivot by variable identity,
        // never by assuming it occupies a particular position in its reason.
        if (variable === resolvedVariable || this.seen[variable] !== 0) {
          continue;
        }
        if (litValue(lit, this.assigns) !== Value.FALSE) {
          throw new Error('conflict analysis reason antecedents must be falsified');
        }
        this.seen[variable] = 1;
        // Once per seen variable, including root antecedents, auxiliaries
        // and variables that disappear from the learned clause by resolution.
        this.bumpVariableActivity(variable);
        if (this.level[variable] === currentLevel) {
          currentCount += 1;
        } else {
          // Retain level-zero antecedents too. Assumptions and PLE pins need
          // not be base-formula consequences; dropping their literals would
          // silently make the learned clause depend on that root context.
          learnedLits.push(lit);
        }
      }
      if (currentCount === 0) {
        throw new Error('conflict must involve the current decision level');
      }

      let pivot: number | undefined;
      while (trailIndex >= 0) {
        const lit = this.trail[trailIndex--];
        const variable = varOf(lit);
        if (this.seen[variable] !== 0 && this.level[variable] === currentLevel) {
          pivot = lit;
          break;
        }
      }
      if (pivot === undefined) {
        throw new Error('conflict analysis could not find a current-level trail literal');
      }
      currentCount -= 1;
      if (currentCount === 0) {
        assertingLit = neg(pivot);
        learnedLits.push(assertingLit);
        break;
      }
      resolvedVariable = varOf(pivot);
      const reason = this.reason[resolvedVariable];
      if (reason === null) {
        throw new Error('conflict analysis reached a decision before the first UIP');
      }
      clause = reason;
    }

    const normalized = normalizeClauseLits(learnedLits);
    if (normalized === null || normalized.length === 0) {
      throw new Error('first-UIP analysis must produce a nonempty, non-tautological clause');
    }
    const lits = this.orderAssertingLits(normalized, assertingLit);
    // LBD is the number of DISTINCT assignment levels at learning time, not
    // clause length or depth. Include level zero (assumptions/PLE antecedents
    // are retained above). Backjumping/asserting can merge these levels, so
    // computing this later would incorrectly promote high-LBD clauses to glue.
    const lbd = new Set(lits.map((lit) => this.level[varOf(lit)])).size;
    // MiniSat's relative decay: future conflicts get a larger increment.
    // This must follow ALL bumps (and any rescaling) for this conflict.
    this.varInc *= 1 / 0.95;
    return {
      learned: { lits, learned: true, activity: 0, lbd },
      backjumpLevel: lits.length === 1 ? 0 : this.level[varOf(lits[1])],
    };
  }

  // Register a learned consequence, with its intended assertion in slot 0.
  // Search registers analyze()'s result BEFORE cancellation, while the other
  // literals' levels still identify the second watch. Return the canonical object:
  // reasons, the database and watches must never use separate equal clauses.
  // This does not enqueue, particularly not a learned unit at the OLD level.
  addLearnedClause(learned: Clause): Clause {
    const normalized = normalizeClauseLits(learned.lits);
    if (normalized === null || normalized.length === 0) {
      throw new Error('a learned clause must be nonempty and non-tautological');
    }
    const key = normalized.join(',');
    const lits = this.orderAssertingLits(normalized, learned.lits[0]);
    const existing = this.clauseByKey.get(key);
    if (existing !== undefined) {
      // An existing clause may watch different literals. Detach BEFORE
      // reordering, then reattach once; originals/blocking clauses stay
      // non-learned and retain their activity and object identity.
      this.detachClause(existing);
      existing.lits = lits;
      this.attachClause(existing);
      return existing;
    }

    learned.lits = lits;
    learned.learned = true;
    this.clauseByKey.set(key, learned);
    this.clauses.push(learned);
    this.attachClause(learned);
    // Count new learned database entries, not live duplicate rediscoveries
    // (units included). Re-deriving a deleted clause IS a new admission.
    this.stats.learnedClauses += 1;
    this.stats.learnedClausesCurrent += 1;
    this.learnedSinceReduction += 1;
    return learned;
  }

  // Permanently strengthen this instance (used for enumeration blockers, NOT
  // per-call assumptions). Register the full normalized clause, retaining its
  // canonical identity and promoting a learned duplicate to permanent role.
  // Then undo non-root assignments BEFORE interpreting its truth status: a
  // blocker is false at the just-returned model, but that is not root UNSAT.
  // Root facts may have been processed long ago, so choose live watches and
  // explicitly enqueue a root unit / remember a root conflict at admission.
  addPermanentClause(rawLits: readonly number[]): Clause | null {
    if (this.enablePle) {
      throw new Error('permanent clause insertion requires enablePle: false');
    }
    for (const lit of rawLits) {
      if (!Number.isInteger(lit) || lit < 0 || lit >= this.watches.length) {
        throw new Error(`permanent clause contains out-of-range literal: ${lit}`);
      }
    }
    const normalized = normalizeClauseLits(rawLits);
    if (normalized === null) {
      return null;
    }
    const key = normalized.join(',');
    let clause = this.clauseByKey.get(key);
    if (clause === undefined) {
      clause = { lits: normalized, learned: false, activity: 0, lbd: 0 };
      this.clauseByKey.set(key, clause);
      this.clauses.push(clause);
    } else {
      this.detachClause(clause);
      if (clause.learned) {
        clause.learned = false;
        this.stats.learnedClausesCurrent -= 1;
        // Historical admissions and the reduction cadence do not rewind.
      }
    }
    this.cancelUntil(0);

    // Root assignments never get undone. Two non-false watches suffice; if
    // only one exists, watch it and a root-false literal. Keep those false
    // antecedents in the clause, including constant assumptions. Structural
    // units alone are unwatched; a longer root-unit clause still has two watches.
    const available: number[] = [];
    const falsified: number[] = [];
    for (const lit of normalized) {
      (litValue(lit, this.assigns) === Value.FALSE ? falsified : available).push(lit);
    }
    clause.lits = [...available, ...falsified];
    this.attachClause(clause);
    if (available.length === 0) {
      // Includes the empty blocker over zero named variables. propagate()
      // reports this conflict once, even with an already-drained root queue.
      this.startupConflict ??= clause;
    } else if (available.length === 1 && litValue(available[0], this.assigns) === Value.UNSET) {
      if (!this.enqueue(available[0], clause)) {
        throw new Error('new permanent root unit must enqueue an unassigned literal');
      }
      this.stats.propagations += 1;
    }
    return clause;
  }

  // The shared production enumeration loop. Public getAllSolutions compiles
  // and constructs ONCE, with PLE disabled; internal stress tests use this
  // exact method with a smaller reduction threshold, not a second toy loop.
  // Assumptions were installed once by the constructor and remain at root.
  enumerateModels(): VariableAssignments[] {
    if (this.enablePle) {
      throw new Error('model enumeration requires enablePle: false');
    }
    const solutions: VariableAssignments[] = [];
    while (this.solve()) {
      solutions.push(this.model());
      const blocker: number[] = [];
      for (let variable = 0; variable < this.cnf.numNamedVars; variable += 1) {
        blocker.push(variable * 2 + (this.assigns[variable] === Value.TRUE ? 1 : 0));
      }
      // Capture the complete named assignment before admission cancels to
      // root. Auxiliaries are never blocked or exposed. Learned consequences
      // of the growing formula (including older blockers) stay sound forever.
      this.addPermanentClause(blocker);
    }
    return solutions;
  }

  // Internal operation, also directly exercised by invariant/protection tests.
  // Stable activity ranking considers the worse floor(n/2) of ALL live learned
  // clauses, skipping protected entries without backfilling from the better
  // half. Equal activities retain database/admission order (stable Array.sort).
  // The permanent originals/blocking clauses are never candidates by role.
  reduceLearnedClauses(): void {
    // Progress the cadence even if every candidate is protected. Testing the
    // live size alone would repeatedly scan/sort on EVERY subsequent conflict.
    this.learnedSinceReduction = 0;
    const learned = this.clauses.filter((clause) => clause.learned);
    learned.sort((left, right) => left.activity - right.activity);
    // Inspect the complete reason array: root and auxiliary implications, and
    // pending assertions, all lock their clauses regardless of watch position.
    const locked = new Set(this.reason);
    const removed = new Set<Clause>();
    for (let index = 0; index < Math.floor(learned.length / 2); index += 1) {
      const clause = learned[index];
      if (clause.lbd > 2 && !locked.has(clause)) {
        removed.add(clause);
      }
    }
    if (removed.size === 0) {
      return;
    }

    let retained = 0;
    for (const clause of this.clauses) {
      if (removed.has(clause)) {
        this.detachClause(clause);
        // Watches permute literals. Delete the semantic key using a sorted
        // COPY, never by changing a live clause's watched positions.
        this.clauseByKey.delete([...clause.lits].sort((a, b) => a - b).join(','));
      } else {
        // Compact in place; neither survivor objects nor the database array
        // are replaced. Reasons, phases, root facts and VSIDS stay untouched.
        this.clauses[retained++] = clause;
      }
    }
    this.clauses.length = retained;
    this.stats.learnedClausesCurrent -= removed.size;
    // learnedClauses is total admissions and must NEVER decrease on deletion.
  }

  newDecisionLevel(): void {
    this.trailLim.push(this.trail.length);
  }

  cancelUntil(targetLevel: number): void {
    if (!Number.isInteger(targetLevel) || targetLevel < 0) {
      throw new Error('target decision level must be a non-negative integer');
    }
    if (this.trailLim.length <= targetLevel) {
      return;
    }

    const cutoff = this.trailLim[targetLevel];
    if (cutoff === undefined) {
      throw new Error(`missing trail boundary for decision level ${targetLevel + 1}`);
    }
    for (let index = this.trail.length - 1; index >= cutoff; index -= 1) {
      const variable = varOf(this.trail[index]);
      this.assigns[variable] = Value.UNSET;
      this.level[variable] = 0;
      this.reason[variable] = null;
      if (variable < this.cnf.numNamedVars) {
        this.unassignedNamed += 1;
        this.insertDecisionVariable(variable);
      }
    }
    this.trail.length = cutoff;
    this.trailLim.length = targetLevel;
    // Backtrack-safe by construction (the scheme's main payoff): watch lists
    // are left untouched — a clause is only examined when one of its
    // watched literals becomes false, and every dequeue after this point
    // re-examines exactly the clauses whose watched literal (re-)becomes
    // false. qhead is clamped to the truncated trail: entries below the
    // cutoff that were never propagated before the backtracking are still
    // pending and must be drained on the next propagate() call, while
    // entries above the cutoff are gone (their watches need no bookkeeping
    // because they were only examined at their previous dequeue).
    this.qhead = Math.min(this.qhead, cutoff);
    this.assertTrailInvariant();
  }

  // Incremental call boundary, also used directly by internal-knob tests. Keep
  // the core's lifetime ledger separate from caller-owned per-call outputs:
  // resetting an output must not reset the live database or reduction cadence.
  // The ordinary solve()/model() lifecycle remains available for enumeration.
  solveAssuming(
    assumptions?: VariableAssignments,
    stats?: SolverStats,
  ): VariableAssignments | null {
    if (this.incrementalCallActive) {
      // A nested call must NOT cancel the outer call's active assumption prefix.
      throw new Error('incremental solve cannot be reentered');
    }
    if (stats === this.stats) {
      throw new Error('incremental output stats must be separate from the lifetime ledger');
    }
    this.incrementalCallActive = true;
    const before = { ...this.stats };
    let reportStats = false;
    try {
      if (stats !== undefined) {
        Object.assign(stats, emptyStats());
        reportStats = true;
      }
      if (this.enablePle) {
        throw new Error('incremental solving requires enablePle: false');
      }
      // Complete validation before touching the call's trail, even if solve()
      // will short-circuit permanent UNSAT. Values/order are read exactly once.
      const ordered = this.translateAssumptions(assumptions);
      return this.solve(ordered) ? this.model() : null;
    } finally {
      // Project BEFORE undoing the model; cleanup also runs on validation or
      // hook errors. Never publish into arbitrary setters before root cleanup.
      try {
        this.cancelUntil(0);
        if (stats !== undefined && reportStats) {
          Object.assign(stats, {
            decisions: this.stats.decisions - before.decisions,
            propagations: this.stats.propagations - before.propagations,
            conflicts: this.stats.conflicts - before.conflicts,
            restarts: this.stats.restarts - before.restarts,
            learnedClauses: this.stats.learnedClauses - before.learnedClauses,
            learnedClausesCurrent: this.stats.learnedClausesCurrent,
          });
        }
      } finally {
        this.incrementalCallActive = false;
      }
    }
  }

  solve(assumptions: readonly number[] = []): boolean {
    if (this.permanentUnsat || this.cnf.levelZeroUnsat) {
      this.permanentUnsat = true;
      return false;
    }

    if (this.propagate() !== null) {
      this.permanentUnsat = true;
      return false;
    }
    if (this.enablePle && !this.eliminatePureLiterals()) {
      this.permanentUnsat = true;
      return false;
    }

    // Iterative CDCL (Design § Search: From DPLL to CDCL). A conflict learns
    // an asserting first-UIP clause and jumps directly to its assertion
    // level, superseding chronological decision flipping. Aux variables are
    // never branched on; SAT requires every named variable to be assigned.
    // Count conflicts since the last budget boundary in base-sized blocks:
    // this implements base * luby(index) without an unsafe Number product or
    // a unit-increment counter that could stop advancing above 2^53. Ordinary
    // backjumps do NOT reset the budget. State is per search, not shared stats.
    let restartIndex = 1;
    let blocksUntilRestart = luby(restartIndex);
    let conflictsInBlock = 0;
    while (true) {
      const conflict = this.propagate();
      if (conflict !== null) {
        if (this.trailLim.length === 0) {
          this.permanentUnsat = true;
          return false;
        }
        const { learned, backjumpLevel } = this.analyze(conflict);
        const assertingLit = learned.lits[0];
        const registered = this.addLearnedClause(learned);
        this.cancelUntil(backjumpLevel);
        if (
          this.assigns[varOf(assertingLit)] !== Value.UNSET ||
          !this.enqueue(assertingLit, registered)
        ) {
          throw new Error(
            'learned clause must assert a newly unassigned literal after backjumping',
          );
        }
        this.stats.propagations += 1;
        conflictsInBlock += 1;
        if (conflictsInBlock === this.restartBaseConflicts) {
          conflictsInBlock = 0;
          blocksUntilRestart -= 1;
          if (blocksUntilRestart === 0) {
            // Finish learning/asserting BEFORE restarting, but do not propagate
            // the assertion first: that could exceed this epoch's conflict
            // budget. A root assertion stays queued (including unwatched units);
            // a conditional assertion above root is undone, never promoted.
            const restarted = this.trailLim.length > 0;
            this.cancelUntil(0);
            if (restarted) {
              this.stats.restarts += 1;
            }
            // Consume an exhausted epoch even if the normal backjump already
            // reached root. Do not count that no-op as an additional restart.
            restartIndex += 1;
            blocksUntilRestart = luby(restartIndex);
          }
        }
        // Do not reduce at registration: the learned clause must first become
        // the assertion's reason. After an optional restart, only reasons that
        // are still active are locked. This does not drain pending propagation.
        if (this.learnedSinceReduction >= this.learnedClauseReductionThreshold) {
          this.reduceLearnedClauses();
        }
      } else {
        // MiniSat assumption prefix (Design § Search). The CURRENT level is
        // the cursor, so backjumps and restarts automatically replay anything
        // they popped. Already-true assumptions still consume dummy levels.
        // A false assumption is call-local UNSAT, even if falsified at root;
        // it is NOT a base conflict and must never poison permanentUnsat.
        let assumptionEnqueued = false;
        while (this.trailLim.length < assumptions.length) {
          const lit = assumptions[this.trailLim.length];
          const value = litValue(lit, this.assigns);
          if (value === Value.FALSE) {
            return false;
          }
          this.newDecisionLevel();
          if (value === Value.UNSET) {
            this.enqueue(lit, null);
            assumptionEnqueued = true;
            break;
          }
        }
        if (assumptionEnqueued) {
          // Propagate this assumption before advancing the prefix, including
          // after the last assumption. Assumptions are not heuristic decisions
          // or propagations; their resulting implications ARE propagations.
          continue;
        }
        // Pending assumptions must be checked even on an already-total root
        // model, not just when the heuristic would otherwise need a decision.
        if (this.namedVariablesAssigned()) {
          return true;
        }
        const [variable, preferTrue] = this.pickDecision();
        const lit = variable * 2 + (preferTrue ? 0 : 1);
        this.newDecisionLevel();
        this.enqueue(lit, null);
        this.stats.decisions += 1;
      }
    }
  }

  model(): VariableAssignments {
    const entries: Array<[Variable, Value]> = [];
    for (let index = 0; index < this.cnf.numNamedVars; index += 1) {
      const value = this.assigns[index];
      if (value === Value.UNSET) {
        throw new Error('cannot build a model before every named variable is assigned');
      }
      const name = this.cnf.indexToName[index];
      if (name === undefined) {
        throw new Error(`missing name for variable index ${index}`);
      }
      entries.push([name, value]);
    }
    return Object.fromEntries(entries);
  }

  // The sorted canonical contents determine deterministic ties. The asserting
  // literal occupies slot 0, and a maximum-other-level literal occupies slot
  // 1, so undoing the assertion level later leaves two non-false watches.
  private orderAssertingLits(normalized: number[], assertingLit: number): number[] {
    const lits = [assertingLit, ...normalized.filter((lit) => lit !== assertingLit)];
    if (lits.length >= 2) {
      let otherWatch = 1;
      for (let index = 2; index < lits.length; index += 1) {
        if (this.level[varOf(lits[index])] > this.level[varOf(lits[otherWatch])]) {
          otherWatch = index;
        }
      }
      [lits[1], lits[otherWatch]] = [lits[otherWatch], lits[1]];
    }
    return lits;
  }

  private attachClause(clause: Clause): void {
    if (clause.lits.length < 2) {
      return;
    }
    const first = clause.lits[0];
    const second = clause.lits[1];
    const firstWatchList = this.watches[first];
    const secondWatchList = this.watches[second];
    if (firstWatchList === undefined || secondWatchList === undefined) {
      throw new Error(`clause contains out-of-range watched literal: ${first}, ${second}`);
    }
    firstWatchList.push(clause);
    secondWatchList.push(clause);
  }

  private detachClause(clause: Clause): void {
    if (clause.lits.length < 2) {
      return;
    }
    for (let slot = 0; slot < 2; slot += 1) {
      const lit = clause.lits[slot];
      const list = this.watches[lit];
      const index = list?.indexOf(clause) ?? -1;
      if (list === undefined || index < 0) {
        throw new Error(`clause is missing its watch on literal: ${lit}`);
      }
      list[index] = list[list.length - 1];
      list.pop();
    }
  }

  private translateAssumptions(assumptions: VariableAssignments | undefined): number[] {
    if (assumptions === undefined) {
      return [];
    }

    const translated: number[] = [];
    for (const [name, value] of Object.entries(assumptions)) {
      const variable = this.cnf.nameToIndex.get(name);
      if (variable === undefined) {
        throw new Error(`unknown assumption variable: ${JSON.stringify(name)}`);
      }
      if (value !== Value.UNSET && value !== Value.FALSE && value !== Value.TRUE) {
        throw new Error(`invalid assumption value for ${JSON.stringify(name)}: ${String(value)}`);
      }
      if (value !== Value.UNSET) {
        translated.push(variable * 2 + (value === Value.FALSE ? 1 : 0));
      }
    }
    return translated;
  }

  // Constructor-only assumptions are constant for this instance (single-shot
  // solving / enumeration), unlike solveAssuming's retractable level prefix.
  private enqueueAssumptions(assumptions: VariableAssignments | undefined): void {
    for (const lit of this.translateAssumptions(assumptions)) {
      if (!this.enqueue(lit, null)) {
        this.startupConflict ??= this.reason[varOf(lit)];
        if (this.startupConflict === null) {
          throw new Error('contradictory assumptions without an explaining clause');
        }
      }
    }
  }

  private eliminatePureLiterals(): boolean {
    while (true) {
      const polarities = new Uint8Array(this.assigns.length);

      for (const clause of this.clauses) {
        let satisfied = false;
        for (const lit of clause.lits) {
          if (litValue(lit, this.assigns) === Value.TRUE) {
            satisfied = true;
            break;
          }
        }
        if (satisfied) {
          continue;
        }
        for (const lit of clause.lits) {
          if (litValue(lit, this.assigns) === Value.UNSET) {
            polarities[varOf(lit)] |= isNeg(lit) ? 2 : 1;
          }
        }
      }

      let assignedPureLiteral = false;
      for (let variable = 0; variable < polarities.length; variable += 1) {
        const polarity = polarities[variable];
        if (polarity !== 1 && polarity !== 2) {
          continue;
        }
        const lit = variable * 2 + (polarity === 2 ? 1 : 0);
        if (!this.enqueue(lit, null)) {
          throw new Error(`pure-literal enqueue contradicted variable ${variable}`);
        }
        this.stats.propagations += 1;
        assignedPureLiteral = true;
      }

      if (!assignedPureLiteral) {
        return true;
      }
      if (this.propagate() !== null) {
        return false;
      }
    }
  }

  private namedVariablesAssigned(): boolean {
    return this.unassignedNamed === 0;
  }

  // Select the next decision: the `variablePriority` hook first (named,
  // unassigned, defensively revalidated), else VSIDS with the saved phase.
  // Initial activity ties and FALSE phases reproduce Phase 1's defaults.
  // Aux variables are never decided (Design § Branching Heuristics).
  private pickDecision(): [number, boolean] {
    if (this.variablePriority !== undefined) {
      const unassigned: Variable[] = [];
      const currentAssignments: Partial<Record<Variable, Value>> = {};
      for (let variable = 0; variable < this.cnf.numNamedVars; variable += 1) {
        const name = this.cnf.indexToName[variable];
        if (name === undefined) {
          throw new Error(`missing name for variable index ${variable}`);
        }
        const value = this.assigns[variable];
        if (value === Value.UNSET) {
          unassigned.push(name);
        } else {
          // Define an own data property even for names such as __proto__;
          // assignment through Object.prototype's setter would lose that key.
          Object.defineProperty(currentAssignments, name, {
            value,
            enumerable: true,
            writable: true,
            configurable: true,
          });
        }
      }

      const picked = this.variablePriority(unassigned, currentAssignments);
      if (Array.isArray(picked) && picked.length === 2) {
        const [name, preferTrue] = picked;
        const variable = this.cnf.nameToIndex.get(name);
        if (
          typeof preferTrue === 'boolean' &&
          variable !== undefined &&
          variable < this.cnf.numNamedVars &&
          this.assigns[variable] === Value.UNSET
        ) {
          return [variable, preferTrue];
        }
      }
    }

    // Do not pop a fallback before consulting the hook: an accepted override
    // must not accidentally discard some OTHER unassigned heap candidate.
    while (this.decisionHeap.length > 0) {
      const variable = this.popDecisionVariable();
      if (this.assigns[variable] === Value.UNSET) {
        return [variable, this.polarity[variable] === Value.TRUE];
      }
    }
    throw new Error('decision heap exhausted with unassigned named variables');
  }

  private bumpVariableActivity(variable: number): void {
    this.activity[variable] += this.varInc;
    // The threshold check belongs IN the bump, not after analyze or decay:
    // later bumps in this SAME conflict must use the rescaled increment.
    if (this.activity[variable] > 1e100) {
      for (let index = 0; index < this.activity.length; index += 1) {
        this.activity[index] *= 1e-100;
      }
      this.varInc *= 1e-100;
      // Positive scaling preserves score order mathematically, but floating
      // rounding/underflow can introduce new ties. Restore index tie-breaking
      // too; Floyd heapification is O(n), like the rescale itself.
      for (let index = (this.decisionHeap.length >> 1) - 1; index >= 0; index -= 1) {
        this.siftDecisionDown(index);
      }
    } else if (variable < this.heapPosition.length && this.heapPosition[variable] >= 0) {
      this.siftDecisionUp(this.heapPosition[variable]);
    }
  }

  private decisionPrecedes(left: number, right: number): boolean {
    return (
      this.activity[left] > this.activity[right] ||
      (this.activity[left] === this.activity[right] && left < right)
    );
  }

  private insertDecisionVariable(variable: number): void {
    // A propagated/hook-assigned variable may still be present lazily. Do not
    // duplicate it on cancellation; normal heap-selected decisions are absent.
    if (this.heapPosition[variable] >= 0) {
      return;
    }
    this.heapPosition[variable] = this.decisionHeap.length;
    this.decisionHeap.push(variable);
    this.siftDecisionUp(this.decisionHeap.length - 1);
  }

  private popDecisionVariable(): number {
    const variable = this.decisionHeap[0];
    const last = this.decisionHeap.pop();
    this.heapPosition[variable] = -1;
    if (last !== undefined && this.decisionHeap.length > 0) {
      this.decisionHeap[0] = last;
      this.heapPosition[last] = 0;
      this.siftDecisionDown(0);
    }
    return variable;
  }

  private siftDecisionUp(index: number): void {
    const variable = this.decisionHeap[index];
    while (index > 0) {
      const parent = (index - 1) >> 1;
      const parentVariable = this.decisionHeap[parent];
      if (!this.decisionPrecedes(variable, parentVariable)) {
        break;
      }
      this.decisionHeap[index] = parentVariable;
      this.heapPosition[parentVariable] = index;
      index = parent;
    }
    this.decisionHeap[index] = variable;
    this.heapPosition[variable] = index;
  }

  private siftDecisionDown(index: number): void {
    const variable = this.decisionHeap[index];
    while (index * 2 + 1 < this.decisionHeap.length) {
      let child = index * 2 + 1;
      if (
        child + 1 < this.decisionHeap.length &&
        this.decisionPrecedes(this.decisionHeap[child + 1], this.decisionHeap[child])
      ) {
        child += 1;
      }
      const childVariable = this.decisionHeap[child];
      if (!this.decisionPrecedes(childVariable, variable)) {
        break;
      }
      this.decisionHeap[index] = childVariable;
      this.heapPosition[childVariable] = index;
      index = child;
    }
    this.decisionHeap[index] = variable;
    this.heapPosition[variable] = index;
  }

  private recordConflict(): void {
    this.stats.conflicts += 1;
    this.conflictsSoFar += 1;
    // Non-root conflicts decay at the END of analyze, after bumping. A
    // terminal root conflict has no analysis/bump but still gets its decay.
    if (this.trailLim.length === 0) {
      this.varInc *= 1 / 0.95;
      // Remember the proof BEFORE the optional budget exception escapes.
      // propagate() may already have advanced qhead past a falsified clause;
      // a later call must not overlook it and report SAT on that drained queue.
      // Per-call falsified assumptions never enter recordConflict().
      this.permanentUnsat = true;
    }
    if (this.maxConflicts !== undefined && this.conflictsSoFar >= this.maxConflicts) {
      throw new Error(`maximum conflict budget exhausted (${this.maxConflicts})`);
    }
  }

  // Explicit debug audit, not a database-wide scan on every enqueue. Safe at
  // reduction boundaries with queued assertions: no propagation fixpoint is
  // required. This method is internal to Solver, not a public package export.
  checkInvariants(): void {
    this.assertTrailInvariant();
    const live = new Set(this.clauses);
    if (live.size !== this.clauses.length || this.clauseByKey.size !== live.size) {
      throw new Error('clause database invariant violated: duplicate or stale registry entries');
    }
    for (const clause of this.clauses) {
      const normalized = normalizeClauseLits(clause.lits);
      if (
        normalized === null ||
        normalized.length !== clause.lits.length ||
        clause.lits.some((lit) => !Number.isInteger(lit) || lit < 0 || lit >= this.watches.length)
      ) {
        throw new Error('clause database invariant violated: invalid clause literals');
      }
      if (this.clauseByKey.get(normalized.join(',')) !== clause) {
        throw new Error('clause database invariant violated: non-canonical clause identity');
      }
    }

    const watchCounts = new Map<Clause, number>();
    for (let lit = 0; lit < this.watches.length; lit += 1) {
      const members = new Set<Clause>();
      for (const clause of this.watches[lit]) {
        if (!live.has(clause)) {
          throw new Error('watch invariant violated: clause is not live');
        }
        if (
          clause.lits.length < 2 ||
          (clause.lits[0] !== lit && clause.lits[1] !== lit) ||
          members.has(clause)
        ) {
          throw new Error('watch invariant violated: incorrect or duplicate membership');
        }
        members.add(clause);
        watchCounts.set(clause, (watchCounts.get(clause) ?? 0) + 1);
      }
    }
    for (const clause of this.clauses) {
      if ((watchCounts.get(clause) ?? 0) !== (clause.lits.length < 2 ? 0 : 2)) {
        throw new Error('watch invariant violated: missing clause watch');
      }
    }
    for (let variable = 0; variable < this.reason.length; variable += 1) {
      const reason = this.reason[variable];
      if (reason !== null) {
        if (!live.has(reason)) {
          throw new Error('reason invariant violated: clause is not live');
        }
        const lit = variable * 2 + (this.assigns[variable] === Value.FALSE ? 1 : 0);
        if (this.assigns[variable] === Value.UNSET || !reason.lits.includes(lit)) {
          throw new Error('reason invariant violated: clause does not explain its assignment');
        }
      }
    }
  }

  private assertTrailInvariant(): void {
    if (!DEBUG_ASSERTIONS) {
      return;
    }

    const seen = new Uint8Array(this.assigns.length);
    for (const lit of this.trail) {
      const variable = varOf(lit);
      if (variable < 0 || variable >= this.assigns.length || seen[variable] !== 0) {
        throw new Error('trail invariant violated: assigned variables must appear exactly once');
      }
      seen[variable] = 1;
      const trailValue = isNeg(lit) ? Value.FALSE : Value.TRUE;
      if (this.assigns[variable] !== trailValue) {
        throw new Error('trail invariant violated: trail polarity must match assigns');
      }
    }
    let unassignedNamed = 0;
    for (let variable = 0; variable < this.assigns.length; variable += 1) {
      const assigned = this.assigns[variable] !== Value.UNSET;
      if (assigned !== (seen[variable] === 1)) {
        throw new Error('trail invariant violated: assigns and trail membership must agree');
      }
      if (!assigned && variable < this.cnf.numNamedVars) {
        unassignedNamed += 1;
      }
    }
    if (unassignedNamed !== this.unassignedNamed) {
      throw new Error('named assignment count must agree with assigns');
    }
  }
}
