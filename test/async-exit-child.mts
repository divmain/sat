// Child-process entry for async.spec.ts's settle-and-exit proof. Runs real
// async solves with the platform MessageChannel scheduler (nothing injected)
// at a small yieldQuantum, then lets the runtime exit NATURALLY: any leaked
// port or listener would pin the event loop and trip the parent's backstop.
// Deliberately not a *.spec.ts file (test discovery) and not typechecked by
// the repo glob; the release consumer re-proves this against the packed
// tarball.

import { and, getAllSolutionsAsync, getSolutionAsync, not, or } from '../src/index.js';

const wide = and(...Array.from({ length: 96 }, (_, i) => or(`v${i}`, not(`v${i}`))));

const single = await getSolutionAsync(wide, { yieldQuantum: 64 });
if (single.status !== 'sat') {
  throw new Error(`expected sat, got ${single.status}`);
}

const all = await getAllSolutionsAsync(and('a', or('a', 'b')), { yieldQuantum: 64 });
if (all.status !== 'complete' || all.models.length !== 2) {
  throw new Error('expected two complete models');
}

console.log('ASYNC_CHILD_SETTLED');
