# Amplification and packed rounding boundary

`BinaryAmplificationPreparation` decodes the original price vector once.
It uses measured binary arithmetic for the grid width, draw count, repeat
count and trial budget. The retained original prices are shared through the
row-by-row sampler and each repeat. Lean equates the prepared values with the
existing typed solver and includes the charge in its full polynomial.

`PhysicalIntegerRounding.boundaryWords` produces and charges the exact input
words for the same packed program. The hard rounding path shares these words
between heap accounting and initialization. It reads the returned mask from the
same cached store, converts the word through one array and charges for the
copy. The guarded cache refines every attempt, including guard charges,
fuel failure and tape exhaustion. The native guard fixture consumes one
bit and checks the literal suffix and charge against the reference. A
second fixture enters the packed controller directly on an empty graph.

`WeakDecomposition.edge_family_of_original_floor` and its PMF theorem use
the exact original-weight oracle and the original near-linear horizon
when every positive actual edge weight is at least `1/(2n)`. The original
marginal factor is `4αw`. The general preprocessing theorem and the
quadratic-horizon exact-original-weight theorem retain their separate
hypotheses. No comparison between the unrestricted exact gap at `W` and
the gap at the modified total is assumed.
