# Checked input for the original-budget edge sampler

The weak-decomposition entry point reads adjacency and rational arc lengths from
the checked graph frame. The fraction field is row-major. The explicit-demand
field is empty because the sampler derives all distance-one demands from the
lengths. The frame accepts unreduced fractions and rejects trailing input.

`MeasuredRescaleWire.draw_value` gives the exact reference sampler result for
every source and literal tape. `draw_encode` specializes that statement to the
supported encoder. The decoder computes one preparation and passes it through
the shared `MeasuredBudgetRescaleEdgeFamily.drawPrepared` entry point. The
result distinguishes an invalid frame, exhaustion of a valid frame's tape,
a completed bounded rejection, and a completed cut. The latter two retain
the reference sampler fee, unread suffix, and number of bits consumed.

`check_valid_paid` and `draw_encode_paid` bound the measured prefix using the
source bit length and parsed dimension. They derive the bound on every
stored numerator and denominator from the checked input. The bound includes
the parser, the typed layout allowance, arithmetic preparation, and the
original-demand guard. Family construction, cut enumeration, exact-factor
feasibility, and addressed native execution have separate work obligations. The existing
correctness, probability, and horizon theorems apply through the exact output
equality with their stated hypotheses.

`MeasuredRescaleWireSmoke` exercises a 91-bit source, the exact cut and
six-bit draw, tape exhaustion, completed bounded rejection, a trailing bit,
and a nonempty explicit-demand field. The wire prefix charges are 42,925,
405, and 1,174 on the successful and two invalid inputs, respectively. The
successful sampler's separate reference fee is 31,871.

## Exact factor at two positive-arc endpoints

`TwoSideEdgeFactor.factor_one` applies when each simple path has at most one
positive-weight arc of each of two colors. It samples a real threshold from the
unit interval. An arc of the first color is selected when its weight reaches the
threshold. An arc of the second color is selected when its weight reaches one
minus the threshold. A threshold path must contain a selected arc, and each
arc's selection probability is at most its weight. The averaging proof gives a
valid cut within the factor-one bound for every nonnegative cost vector.

`RationalInstanceEdgeFactor.least_le_one_of_endpointCap_le_two` derives the
coloring when the set of actual positive-weight nonloop arcs has at most two
tails or at most two heads. This lets the exact search return zero when the
empty cut suffices and one otherwise, with no rational feasibility test in
either case. `leastSupported_eq` continues to characterize the same exact
instance factor on every input. The bisection and cut enumeration still apply
above the two-endpoint cap. The two native examples exercise each minimum in
the endpoint-cap formula using different graphs.
