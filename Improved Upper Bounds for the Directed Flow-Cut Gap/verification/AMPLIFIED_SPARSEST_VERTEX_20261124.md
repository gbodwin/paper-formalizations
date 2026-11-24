# High-confidence sparsest vertex cuts on a literal tape

`RationalVertexSparsityCode.score` assigns unit length to selected vertices
and zero length to the others. A demand is separated exactly when the
distance under these lengths is at least one, including an unreachable
demand. The verified binary shortest-path routine computes these distances
with each demand's endpoints excluded. The score divides original vertex
cost by the number of separated entries. For distinct input pairs this is
the number of separated demands in the set-based objective.

`AmplifiedNormalizedVertexSparsest.run` solves the exact normalized vertex
program once and computes the threshold and mode from those same lengths.
It repeats the chosen mode and retains a sampled cut with minimum exact
sparsity. The fair-tape and support proofs account for adaptive draw
ranges and bounded rejection.

With all demands reachable and at least one non-self pair with no direct
arc, the full tape suffices for the original vertex cut and exact unread
suffix. For distinct demands, every returned cut separates at least one.
Every returned cut has zero original price when the normalized optimum
is zero in this domain.

For a positive bound based on either scale of the computed optimum, a
common rounding constant suffices. The chance of exceeding twice that
bound on the stated uniform tape is at most
`2^(-(extra + 1)) + 2^(-confidence)`.
The mass scale uses the average-one mass of the returned minimum-price
assignment. The tape length has a polynomial upper bound in the graph
size and the numerical confidence parameters.

The native fixture observes score 3/2 on the original internal-vertex cut
and zero separations when selecting only the endpoints. It runs the
positive and zero-price optimized entries and checks the unread tape.
A two-sample fixture with the same score consumes six bits, rejects a
draw, selects the cheaper scored cut and leaves one bit unread.

Exact optimization still uses exhaustive rational elimination. A
complete structural bit-time bound remains open.
