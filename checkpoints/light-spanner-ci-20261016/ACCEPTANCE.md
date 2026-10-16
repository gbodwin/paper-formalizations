# Bounded independent review acceptance

The user reports that independent skeptical review accepts candidate
`90b270f5442b3ebe50bd41a45f501b2277380d71` and recovery evidence
`9bb8e69d522f794fd297672131b5d6ef19fddcc6`. The reviewer is idle. This records that
review outcome; it is not a fresh reviewer execution. Clean exact-source CI and
its independent evidence review are separate gates before publication acceptance.

Accepted scope: finite connected simple graphs, positive actual-edge weights,
every real epsilon>0 and integer k>=1. The actual sorted greedy endpoint has
stretch `(1+epsilon)(2k-1)`, an actual contained input MST, and the tighter bound
`8+(2048/epsilon)n^(1/k)`. The coefficient-form endpoint gives
`(8+2048/epsilon)n^(1/k)`. The existence wrapper transfers actual-edge quantities
from the nonnegative extension and removes restrictions on off-graph weights;
it does not identify differently extended greedy runs definitionally.
Singletons use totalized zero division. Disconnected/MSF assembly, runtime,
lower-bound tightness and unused warmup/background results are excluded.

Historical comments in frozen `Counting.lean` saying dispersion/counting remain
obligations are superseded at the assembled-candidate level by BucketDispersion,
WeakCounting, MediumCounting and SamplingCounting. The comment in Construction
that the subsequent lightness argument remains open is superseded by
LightnessBound, MainTheorem and WeightExtension. The local supporting statements
in those files retain their original limited roles. Frozen source comments are
not edited, and the accepted global subdivision budget, chord-only strict bound,
t+1 hiker layers/t shuttle moves and all-epsilon +n repair are preserved.

No website publication or whole-paper acceptance is authorized or claimed here.

The new clean gate subsequently succeeded at run 38846027893, testing the exact
same candidate. Its artifact review remains separate and pending; consult
REPORT.md for immutable identities, exact diagnostic checks and access qualification.
