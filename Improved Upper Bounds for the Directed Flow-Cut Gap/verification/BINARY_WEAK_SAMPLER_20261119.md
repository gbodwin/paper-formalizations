# Calibrated sampling of an edge cut

The binary sampler chooses an index in the actual returned family using the
unread tape. It retains bounded rejection as explicit failure and uses an
array for the selected index. Repeated cuts retain their multiplicities.
Every index has equal mass conditional on acceptance.

The original adjacency and weight entry runs the calibrated adaptive solver
first. Lean checks the combined finite fair-tape law, all original threshold
demands for a selected cut, the exact unread suffix and a polynomial for the
recorded solver and sampler charges. Each supported family carries the
original-weight marginal bound. The same bound applies conditional on
returning a cut. For n at least two, the total rejection probability is at
most n to the negative requested confidence exponent.

The native cases cover a rejected index followed by a distinct accepted
one, complete bounded rejection, short tape, and an original two-vertex
input of total weight one half. The latter produces an actual adaptive
family of empty cuts and samples it on the same literal tape.

This sampler uses the weight-dependent calibrated factor. The mathematical
minimum of the weight- and size-dependent bounds is in
`WeakDecompositionBounds`. The arbitrary-factor reduction has a
near-linear exact-original-weight theorem under the positive-weight floor
and a quadratic-horizon exact-original-weight theorem for all weights.
