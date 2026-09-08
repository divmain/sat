import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describe, it } from 'node:test';

// These immutable generated references intentionally use JSON.stringify's
// expanded arrays, not Biome's compact arrays. Keep their exact serialization
// checked without importing or executing the frozen historical recorder.
// This is a formatting contract, not a substitute for authenticated replay.
describe('canonical generated reference bytes', () => {
  for (const name of ['v3-baseline.json', 'legacy-compiled-cnf.json']) {
    it(`${name} uses two-space JSON.stringify output and a trailing newline`, () => {
      const bytes = readFileSync(new URL(name, import.meta.url));
      const parsed: unknown = JSON.parse(bytes.toString('utf8'));
      const canonical = Buffer.from(`${JSON.stringify(parsed, null, 2)}\n`, 'utf8');
      assert.deepEqual(bytes, canonical);
    });
  }
});
