// Platform-neutrality guards for the library sources, plus the load-proof
// check that the test-suite preload (`--import ./test/debug.ts`, wired into
// every npm test script) actually reached this node:test worker. If script
// wiring ever drops the preload, the first test below fails loudly instead of
// letting audit coverage silently disappear. This spec deliberately does NOT
// import test/debug.ts: the marker must come from the preload alone, or the
// check would be vacuous.
import assert from 'node:assert';
import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { describe, it } from 'node:test';
import { fileURLToPath } from 'node:url';

// Exact-string allow-list: the guarded globalThis access that initializes the
// debug flag in src/solver.ts is the library's single intentional
// platform-specific reference. Every other `process` occurrence or `node:`
// import under src/ is a violation.
const ALLOWED_PLATFORM_ACCESS = "globalThis.process?.env?.SAT_DEBUG === '1'";

type DebugAuditGlobal = typeof globalThis & { __SAT_DEBUG_AUDITS__?: boolean };

function listSourceFiles(directory: string): string[] {
  const files: string[] = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const entryPath = join(directory, entry.name);
    if (entry.isDirectory()) {
      files.push(...listSourceFiles(entryPath));
    } else {
      files.push(entryPath);
    }
  }
  return files;
}

describe('Platform neutrality and preload load-proof', () => {
  it('the debug-audit preload reached this test worker', () => {
    assert.strictEqual(
      (globalThis as DebugAuditGlobal).__SAT_DEBUG_AUDITS__,
      true,
      'test/debug.ts was not preloaded into this node:test worker; every npm ' +
        'test script must pass --import ./test/debug.ts so solver debug audits ' +
        'run for the whole suite',
    );
  });

  it('src/ contains no bare process reference and no node: import', () => {
    const srcDirectory = join(dirname(fileURLToPath(import.meta.url)), '..', 'src');
    const violations: string[] = [];
    for (const file of listSourceFiles(srcDirectory)) {
      const lines = readFileSync(file, 'utf8').split('\n');
      for (const [index, line] of lines.entries()) {
        if (line.includes(ALLOWED_PLATFORM_ACCESS)) {
          continue;
        }
        if (/\bprocess\b/.test(line)) {
          violations.push(`${relative(srcDirectory, file)}:${index + 1}: bare process reference`);
        }
        if (/["']node:/.test(line)) {
          violations.push(`${relative(srcDirectory, file)}:${index + 1}: node: import`);
        }
      }
    }
    assert.deepStrictEqual(
      violations,
      [],
      `src/ must stay platform-neutral: no process reference except the guarded globalThis access, and no node: import.\n${violations.join(
        '\n',
      )}`,
    );
  });
});
