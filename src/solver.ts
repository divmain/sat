// Mutable solver state, Phase-1 occurrence-list unit propagation, scoped
// pure-literal elimination, and the iterative chronological-backtracking
// (DPLL) search loop. Phase 2 replaces only the propagation mechanism and the
// conflict-handling branch — the public contract stays fixed.
// See Design § Solver Core State and Invariants and § Search: From DPLL to
// CDCL.

import { isNeg, litValue, neg, varOf } from './compile.js';
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
}

const DEBUG_ASSERTIONS = process.env.NODE_ENV !== 'production';

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
  readonly trail: number[] = [];
  readonly trailLim: number[] = [];
  qhead = 0;

  readonly clauses: Clause[];
  readonly occurs: Clause[][];
  readonly stats: SolverStats;
  readonly variablePriority: VariablePriority | undefined;

  private readonly cnf: CompiledCnf;
  private readonly enablePle: boolean;
  private readonly maxConflicts: number | undefined;
  private conflictsThisSolve = 0;
  private startupConflict: Clause | null = null;
  private startupConflictReported = false;
  private permanentUnsat = false;

  constructor(cnf: CompiledCnf, opts: SolverOptions = {}) {
    if (
      opts.maxConflicts !== undefined &&
      (!Number.isInteger(opts.maxConflicts) || opts.maxConflicts < 0)
    ) {
      throw new Error('maxConflicts must be a non-negative integer');
    }

    this.cnf = cnf;
    this.assigns = new Int8Array(cnf.numVars).fill(Value.UNSET);
    this.level = new Int32Array(cnf.numVars);
    this.reason = Array<Clause | null>(cnf.numVars).fill(null);
    this.clauses = [...cnf.clauses];
    this.occurs = Array.from({ length: cnf.numVars * 2 }, () => []);
    this.stats = opts.stats ?? emptyStats();
    this.variablePriority = opts.variablePriority;
    this.enablePle = opts.enablePle ?? false;
    this.maxConflicts = opts.maxConflicts;

    // Add clauses before assumptions. Units are deliberately absent from
    // occurrence lists: they are asserted once at level zero instead.
    for (const clause of this.clauses) {
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
        for (const lit of clause.lits) {
          const occurrenceList = this.occurs[lit];
          if (occurrenceList === undefined) {
            throw new Error(`clause contains out-of-range literal: ${lit}`);
          }
          occurrenceList.push(clause);
        }
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

    while (this.qhead < this.trail.length) {
      const assignedLit = this.trail[this.qhead];
      this.qhead += 1;
      const occurrenceList = this.occurs[neg(assignedLit)];
      if (occurrenceList === undefined) {
        throw new Error(`missing occurrence list for literal: ${neg(assignedLit)}`);
      }

      for (const clause of occurrenceList) {
        let unitLit: number | null = null;
        let unassignedCount = 0;
        let satisfied = false;

        for (const lit of clause.lits) {
          const value = litValue(lit, this.assigns);
          if (value === Value.TRUE) {
            satisfied = true;
            break;
          }
          if (value === Value.UNSET) {
            unitLit = lit;
            unassignedCount += 1;
          }
        }

        if (satisfied) {
          continue;
        }
        if (unassignedCount === 0) {
          this.recordConflict();
          return clause;
        }
        if (unassignedCount === 1 && unitLit !== null) {
          // The scan proved this variable unset, so a successful enqueue is a
          // new implication and counts as one propagation.
          if (!this.enqueue(unitLit, clause)) {
            this.recordConflict();
            return clause;
          }
          this.stats.propagations += 1;
        }
      }
    }

    return null;
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
    }
    this.trail.length = cutoff;
    this.trailLim.length = targetLevel;
    this.qhead = Math.min(this.qhead, cutoff);
    this.assertTrailInvariant();
  }

  solve(): boolean {
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

    // Phase 1 iterative chronological backtracking (Design § Search: From
    // DPLL to CDCL). `flipped` and `decisionLits` grow alongside `trailLim`:
    // entry i records the decision literal of decision level i+1 and whether
    // that level's decision has already been tried in its other polarity. A
    // conflict unwinds decision levels until one with an untried polarity is
    // found (its negation becomes the flipped decision at the same level);
    // exhausting every level means the level-0 prefix conflicts — UNSAT.
    // Aux variables are never branched on; SAT is reached as soon as every
    // named variable is assigned (Design § Termination condition).
    const flipped: boolean[] = [];
    const decisionLits: number[] = [];
    while (true) {
      if (this.propagate() !== null) {
        if (this.trailLim.length === 0) {
          this.permanentUnsat = true;
          return false;
        }
        if (!this.retryDecisionLevel(flipped, decisionLits)) {
          this.permanentUnsat = true;
          return false;
        }
      } else if (this.namedVariablesAssigned()) {
        return true;
      } else {
        const [variable, preferTrue] = this.pickDecision();
        const lit = variable * 2 + (preferTrue ? 0 : 1);
        this.newDecisionLevel();
        flipped.push(false);
        decisionLits.push(lit);
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

  private enqueueAssumptions(assumptions: VariableAssignments | undefined): void {
    if (assumptions === undefined) {
      return;
    }

    const translated: Array<[number, Value]> = [];
    for (const [name, value] of Object.entries(assumptions)) {
      const variable = this.cnf.nameToIndex.get(name);
      if (variable === undefined) {
        throw new Error(`unknown assumption variable: ${JSON.stringify(name)}`);
      }
      if (value !== Value.UNSET && value !== Value.FALSE && value !== Value.TRUE) {
        throw new Error(`invalid assumption value for ${JSON.stringify(name)}: ${String(value)}`);
      }
      if (value !== Value.UNSET) {
        translated.push([variable, value]);
      }
    }

    for (const [variable, value] of translated) {
      const lit = variable * 2 + (value === Value.FALSE ? 1 : 0);
      if (!this.enqueue(lit, null)) {
        this.startupConflict ??= this.reason[variable];
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
    for (let variable = 0; variable < this.cnf.numNamedVars; variable += 1) {
      if (this.assigns[variable] === Value.UNSET) {
        return false;
      }
    }
    return true;
  }

  // Unwind from a conflict: pop decision levels until a level whose decision
  // was not yet flipped is found, cancel it, and re-enter it with the
  // negation of the old decision literal (marked flipped). Returns false when
  // every decision level was exhausted — a level-0 conflict, i.e. UNSAT.
  private retryDecisionLevel(flipped: boolean[], decisionLits: number[]): boolean {
    while (this.trailLim.length > 0) {
      const levelIndex = this.trailLim.length - 1;
      const decisionLit = decisionLits[levelIndex];
      const alreadyFlipped = flipped[levelIndex] === true;

      this.cancelUntil(levelIndex);
      if (!alreadyFlipped) {
        const flippedLit = neg(decisionLit);
        flipped[levelIndex] = true;
        decisionLits[levelIndex] = flippedLit;
        this.newDecisionLevel();
        this.enqueue(flippedLit, null);
        return true;
      }

      flipped.length = levelIndex;
      decisionLits.length = levelIndex;
    }
    return false;
  }

  // Select the next decision: the `variablePriority` hook first (named,
  // unassigned, defensively revalidated), else the first unassigned named
  // variable, FALSE-first to match the v1 default polarity (Design §
  // Branching Heuristics). Aux variables are never decided.
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
          currentAssignments[name] = value;
        }
      }

      const picked = this.variablePriority(unassigned, currentAssignments);
      if (picked !== null) {
        const [name, preferTrue] = picked;
        const variable = this.cnf.nameToIndex.get(name);
        if (
          variable !== undefined &&
          variable < this.cnf.numNamedVars &&
          this.assigns[variable] === Value.UNSET
        ) {
          return [variable, preferTrue];
        }
      }
    }

    for (let variable = 0; variable < this.cnf.numNamedVars; variable += 1) {
      if (this.assigns[variable] === Value.UNSET) {
        return [variable, false];
      }
    }
    throw new Error('no unassigned named variable remains to decide');
  }

  private recordConflict(): void {
    this.stats.conflicts += 1;
    this.conflictsThisSolve += 1;
    if (this.maxConflicts !== undefined && this.conflictsThisSolve >= this.maxConflicts) {
      throw new Error(`maximum conflict budget exhausted (${this.maxConflicts})`);
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
    for (let variable = 0; variable < this.assigns.length; variable += 1) {
      const assigned = this.assigns[variable] !== Value.UNSET;
      if (assigned !== (seen[variable] === 1)) {
        throw new Error('trail invariant violated: assigns and trail membership must agree');
      }
    }
  }
}
