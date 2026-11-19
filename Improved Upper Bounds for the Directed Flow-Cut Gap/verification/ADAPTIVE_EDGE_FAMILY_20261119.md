# Adaptive rational edge families

The paper's tiny-edge modification is computed from the original rational
weights. The threshold demand list is computed by the binary shortest-path
solver on those original weights. It includes unreachable pairs and excludes
self-pairs. The modified weights give a fractional cut for that list.

`RandomizedEdgeFamily.calibrated_families` in Lean fixes two positive integer
parameters for each desired exponent. The runtime input contains the original
binary rational weights, the graph, and a confidence degree. The multiplier
and exponent denominator are fixed by the existence theorem. A dyadic
computation chooses the input-dependent factor using the original total mass.
At each iteration the encoded mass solver sees the current rational prices.
An exact price check either rejects the sample or accepts and retains an
integral cut. The accepted cut updates the next prices.

Every returned family has the computed horizon and cuts the original threshold
demands. Each edge's frequency under a uniform draw from the family is bounded
by a constant times its original weight, the requested power of the vertex
count, and the square root of the original total weight. The subunit-mass case
returns empty cuts because its threshold demands are all unreachable. On
independent fair bits of the proved length, the probability of failure for
graphs with at least two vertices is at most `n^(-confidence)`. The solver
preserves the literal unused suffix and bounds the bits it reads in the graph
dimensions, the actual stored widths of the original weights and computed
factor, and the calibrated confidence.

This scope uses the existing typed executable edge solver. Deterministic
bit-time of the complete adaptive loop, fixed-instruction lowering, and the
near-linear horizon at the exact original-weight rounding factor remain open.

The workflow `flow-adaptive-family.yml` builds the adaptive import closure on
the pinned toolchain, checks the canonical module index, audits the types and
bodies of adaptive declarations, and replays all ten added modules. The
execution fixture checks a complete three-cut zero-objective family, a complete
thirteen-cut subunit-mass family and two successive calls that each cut an
active edge. It also checks the unread tape and the subunit instance's computed
confidence. See the exact terminal CI record for the results.
