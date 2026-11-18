# Constructive vertex rounding

The parent is the exact median repair `495fdbd58f015c8d6e804f0a0387e87142efed35`.
Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435` are pinned.

`EncodedIntegerRounding` builds the closure dictionary and threshold-demand
mask and runs the retained controller at the analyzed integer parameters.
Its ideal law equals the existing all-regime closure law. Its literal
fair-bit program preserves validity for every supported mask.

`EncodedUniformRounding` computes the rational uniformization parameters
once, passes the actual chain graph and integer cutoff to the controller, and
pulls back the selected mask through the stored original labels. It proves
support validity, the expected-size bound, a bound on bit calls, and the
explicit bounded-rejection event error.

`EncodedWeightedRounding` dispatches zero prepared objective to the computed
zero-cost mask. It runs the uniform program on the actual positive-cost
replica and uses the full-fiber pullback. Its ideal law has expected cost at
most `K n^ε sqrt(W) C` for a constant independent of the input, where `W`
and `C` are the input fractional mass and weighted objective.

All three sources in checkpoint `630cc3b65b223a20c45f9050e2b107314ee62d7e`
passed strict local checking and independent review. The local logical audit
covered 7,551 declarations in the 122-module import closure and traversed
47,683 type-and-body dependencies from 221 roots. The axiom whitelist is
`propext`, `Classical.choice` and `Quot.sound`. A separate all-declaration
check encountered generated recursion entries. The logical audit recorded
102 of them with their retained logical declarations and rejects their use
in the checked proof closures. Native compiler assurance remains unproved.

Direct official kernel replays passed for the eleven targets in that
checkpoint. They include the attained mathematical
vertex and edge bounds, sparsest-cut corollaries, and weak-decomposition
statements. The 722-module reference replay is a separate interpreter and
packing scope. The deterministic dispatch and pullback fixture covered small and enormous
thresholds, uniformization, and zero and positive weighted objectives. A
separate local rerun of the inherited nonterminal fair-bit fixture exceeded
its 180-second interpreter budget. All six passing dispatch cases asserted
zero draws.

## Original rational vertex input

`EncodedSizeRounding` computes the heavy-vertex split with the encoded
cube-root threshold and runs the weighted program on the retained survivor
graph. Its ideal law has expected cost at most `K n^(1/3+ε) C` for the
supplied weights and costs.

`EncodedVertexSolver` starts from a Boolean adjacency matrix, an ordered
list of demands, and a rational cost row. The executed fractional solver
returns an infeasibility tag, a zero-cost cut, or its grid of cover states.
`EncodedCutSelection` compares the stored rational costs of cuts sampled
from the actual covers and returns one of those cuts. Every supported cut
of each executable fair-bit variant is valid. The two ideal expected-cost
theorems compare with any feasible fractional comparator. The size bound
uses its cost. The mass bound uses that same comparator's cost and total
mass. The one-sample bit-program tail includes the explicit rejection error.

External byte parsing, an end-to-end bit-cost bound, amplified success
probability, and the constructive edge and exact-mass weak-decomposition
interfaces remain open.
