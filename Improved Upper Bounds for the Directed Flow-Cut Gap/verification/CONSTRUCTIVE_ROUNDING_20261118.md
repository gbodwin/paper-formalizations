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

`EncodedWeightedRounding` dispatches zero objective to the computed
zero-cost mask. It runs the uniform program on the actual positive-cost
replica and uses the full-fiber pullback. Its ideal law has expected cost at
most `K n^ε sqrt(W) C` for a constant independent of the input, where `W`
and `C` are the input fractional mass and weighted objective.

All three new sources passed strict local checking. The local logical audit
covered 7,551 declarations in the 122-module import closure and traversed
47,683 type-and-body dependencies from 221 roots. The axiom whitelist is
`propext`, `Classical.choice` and `Quot.sound`. A separate all-declaration
check encountered generated recursion entries. The logical audit recorded
102 of them with their retained logical declarations and rejects their use
in the checked proof closures. Native compiler assurance remains unproved.

Direct official kernel replays passed for the eleven target modules in
`scripts/CheckFlowConstructive.sh`. They include the attained mathematical
vertex and edge bounds, sparsest-cut corollaries, and weak-decomposition
statements. The 722-module reference replay is a separate interpreter and
packing scope. The executed rounding fixture covered small and enormous
thresholds, uniformization, and zero and positive weighted objectives. A
separate local rerun of the inherited nonterminal fair-bit fixture exceeded
its 180-second interpreter budget.

The weighted runner takes a stored rational fractional weight row. Connecting
fractional cover selection to this runner, edge execution, amplification,
and an end-to-end bit-cost theorem are further obligations.
