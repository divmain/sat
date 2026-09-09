// Canonical evidence helpers for the v3 candidate harness and the bench:legacy
// compiled-snapshot gate. These are the candidate-tree counterparts of the
// frozen recorder's test/v3-baseline-overlay/evidence.ts: the canonical forms
// and digests they produce are byte-compatible with the sealed references,
// but they import the CURRENT candidate sources. The frozen overlay is never
// imported from outside its directory, so this module must stay output-faithful
// to it; any intentional change is a schema event, not an edit.

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import type { CompiledCnf } from '../src/compile.js';
import { Value } from '../src/expr.js';
import type { BooleanExpr, VariableAssignments } from '../src/expr.js';
import type { Scenario } from './bench-v3-corpus.js';

export const json = (value: unknown): string => `${JSON.stringify(value, null, 2)}\n`;
export const sha256 = (value: string | Buffer): string =>
  createHash('sha256').update(value).digest('hex');
export const digest = (value: unknown): string => sha256(JSON.stringify(value));

export function inputIdentity(scenario: Scenario) {
  return {
    version: 1,
    id: scenario.id,
    mode: scenario.mode,
    definition: scenario.definition,
    expr: scenario.expr,
    assumptions: Object.entries(scenario.assumptions),
    calls: scenario.calls.map((call) => Object.entries(call)),
  };
}

// Numeric lexicographic order, shorter prefix first. Copy before sorting: the
// original clause/watch order must reach the solver unchanged.
export function compiledSnapshot(cnf: CompiledCnf) {
  assert.equal(cnf.nameToIndex.size, cnf.numNamedVars);
  assert.equal(cnf.indexToName.length, cnf.numNamedVars);
  const namedVariables = Array.from(cnf.nameToIndex, ([name, index]) => {
    assert.equal(cnf.indexToName[index], name);
    assert.ok(index >= 0 && index < cnf.numVars);
    return { index, name };
  }).sort((a, b) => a.index - b.index);
  const clauses = cnf.clauses.map((clause) => {
    assert.equal(clause.learned, false);
    assert.equal(clause.activity, 0);
    assert.equal(clause.lbd, 0);
    return [...clause.lits].sort((a, b) => a - b);
  });
  clauses.sort((a, b) => {
    for (let i = 0; i < Math.min(a.length, b.length); i += 1) {
      if (a[i] !== b[i]) return a[i] - b[i];
    }
    return a.length - b.length;
  });
  return {
    numVars: cnf.numVars,
    numNamedVars: cnf.numNamedVars,
    namedVariables,
    clauses,
    levelZeroUnsat: cnf.levelZeroUnsat,
  };
}

export type CompiledSnapshot = ReturnType<typeof compiledSnapshot>;

// Independent AST semantics, not solver/compiled-clause validation.
function evaluate(expr: BooleanExpr | string, model: VariableAssignments): boolean {
  if (typeof expr === 'string') return model[expr] === Value.TRUE;
  if ('and' in expr) return expr.and.every((child) => evaluate(child, model));
  if ('or' in expr) return expr.or.some((child) => evaluate(child, model));
  if ('not' in expr) return !evaluate(expr.not, model);
  if ('atMost' in expr) {
    const count = expr.atMost.exprs.filter((child) => evaluate(child, model)).length;
    return count <= expr.atMost.k;
  }
  if ('atLeast' in expr) {
    const count = expr.atLeast.exprs.filter((child) => evaluate(child, model)).length;
    return count >= expr.atLeast.k;
  }
  throw new Error('Unexpected BooleanExpr node');
}

export function modelEvidence(
  expr: BooleanExpr,
  assumptions: VariableAssignments,
  model: VariableAssignments,
) {
  // Do not share the compiler's name collector: tautological/folded variables
  // must remain visible even if a future collector regression loses them.
  const universe = new Set<string>();
  const pending: (BooleanExpr | string)[] = [expr];
  while (pending.length > 0) {
    const node = pending.pop();
    assert.ok(node !== undefined);
    if (typeof node === 'string') universe.add(node);
    else if ('and' in node) pending.push(...node.and);
    else if ('or' in node) pending.push(...node.or);
    else if ('not' in node) pending.push(node.not);
    else if ('atMost' in node) pending.push(...node.atMost.exprs);
    else pending.push(...node.atLeast.exprs);
  }
  const names = [...universe].sort();
  assert.deepEqual(Reflect.ownKeys(model).sort(), names);
  for (const name of names) {
    assert.ok(Object.prototype.propertyIsEnumerable.call(model, name));
    assert.ok(model[name] === Value.TRUE || model[name] === Value.FALSE);
  }
  assert.ok(evaluate(expr, model), 'model must satisfy independent AST evaluator');
  for (const [name, value] of Object.entries(assumptions)) {
    if (value !== Value.UNSET) assert.equal(model[name], value);
  }
  return digest(names.map((name) => [name, model[name]]));
}
