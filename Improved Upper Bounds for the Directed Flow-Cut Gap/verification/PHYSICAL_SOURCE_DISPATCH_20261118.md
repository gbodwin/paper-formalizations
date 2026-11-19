# Physical fractional dispatch and rounding

The recovered final dispatcher consists of fifteen modules from the public
October candidate. Their checked sources include the four minimal repairs
documented in [the recovery record](../../flow-continuation-drafts/20261118-replayed-store).
The inherited 722-source manifest still checks at the repaired median
ancestor and on this branch.

[PhysicalSourceDispatch](../DirectedFlowCutGap/PhysicalSourceDispatch.lean)
places the existing source parser and fractional dispatcher in a single
13,384-slot program. It begins with an empty heap, reads the original
serialized vertex tables in order, and passes the same heap and roots
to the solver. One register move installs the demand root. The paid
run includes the actual terminal attempt. Its charge is bounded by
a fixed polynomial in the length of the original encoded input.

[PhysicalCoverReader](../DirectedFlowCutGap/PhysicalCoverReader.lean)
extracts the exact obstruction, zero mask, or ordered best cover rows
from the actual terminal heap. The reader preserves numerator and
denominator bits until decoding. The result feeds the same rounding
tree whose support, probability and size bounds are proved elsewhere
in the formalization.

[PhysicalVertexSolver](../DirectedFlowCutGap/PhysicalVertexSolver.lean)
runs a functional parse to obtain types and the fuel bound. It dispatches
encoder-produced bytes directly and re-encodes other accepted demand label spellings. Both
rounding modes return a valid output for parse-accepted source tables
and any sufficient tape. The output records the exact unread suffix.
[PhysicalEdgeSolver](../DirectedFlowCutGap/PhysicalEdgeSolver.lean)
builds a binary line graph from the original rational edge instance,
uses the physical dispatcher with typed store preparation, then rounds
and projects to the original edges. Its paid dispatcher budget is
polynomial in original graph dimension, demand count and canonical
rational field width. The edge charge includes declared typed
preparation.

The charged prefix excludes the separate native parse, format comparison
and re-encoding, line graph construction, fuel calculation, terminal heap erasure and readback,
and deterministic work in rounding and selection. The fair-bit bound
counts random reads. A single fixed-instruction source-to-cut
implementation and a polynomial bound on all its deterministic bit
operations remain open.

[CachedReferenceExecution](../DirectedFlowCutGap/CachedReferenceExecution.lean)
executes the same fixed instructions with an indexed store and prefix sums
for the sequential lookup and append charges. The Lean refinement proves
the same transition and charge on every step and the same returned state
and charge for the fuelled evaluator, including a paid terminal attempt.

[RetainedChargedFairBits](../DirectedFlowCutGap/RetainedChargedFairBits.lean)
supplies the counted rounding controller with its actual bounded-rejection
sampler. The logged execution projects to the original lowered rounding
tree. The declared word-operation price is bounded for the computed
initial state at the algorithm’s restart and epoch parameters.

The short physical fixtures cover empty and self-demand runs for both
graph models, padded demand labels, and ordered cover readback from a
separately constructed positive heap. The full positive fixture uses the
cached evaluator over the three-vertex source chain. It checks ordered
request events, source exhaustion, original roots, all nine retained
states, and the paid stop. Both rounding modes then use the retained
rows from that same run. The earlier sequential-interpreter timeouts
are recorded separately in the recovery receipt.

[Heap readback and binary sampler charges](SAMPLING_READBACK_20261119.md)

[Constructive workflow](../../.github/workflows/flow-constructive-rounding.yml)
