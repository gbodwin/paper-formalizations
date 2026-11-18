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
uses the raw bytes in the physical run. A separate functional parse
provides types and the fuel bound. Both rounding modes return a valid
output for any sufficient tape and expose its exact unread suffix.
[PhysicalEdgeSolver](../DirectedFlowCutGap/PhysicalEdgeSolver.lean)
builds a binary line graph from the original rational edge instance,
uses the physical dispatcher with typed store preparation, then rounds
and projects to the original edges. Its paid dispatcher budget is
polynomial in original graph dimension, demand count and canonical
rational field width. The edge charge includes declared typed
preparation.

The charged prefix excludes the separate native parse or line graph
construction, fuel calculation, terminal heap erasure and readback,
and deterministic work in rounding and selection. The fair-bit bound
counts random reads. A single fixed-instruction source-to-cut
implementation and a polynomial bound on all its deterministic bit
operations remain open.

The physical fixtures check paid empty and self-demand runs for
both graph models, and a separately constructed positive heap for
ordered cover readback. The recovered positive whole-dispatch
fixtures previously timed out after reaching the grid. The old
positive run remains an open execution check. Kernel replay and
logical dependency gates run through [the constructive workflow](../../.github/workflows/flow-constructive-rounding.yml).
