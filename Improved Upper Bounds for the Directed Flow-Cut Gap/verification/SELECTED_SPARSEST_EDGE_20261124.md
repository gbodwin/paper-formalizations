# Selecting the smaller sparsest-edge bound on the literal tape

`NormalizedOptimalMode.runBest` computes the exact normalized rational
fractional objective, chooses a mode, and rounds the resulting lengths.
It compares `(H * W_avg)^3` with `n^2` using rational arithmetic. Here
`H` is the demand-count harmonic number and `W_avg` is the mass of the
returned lengths after normalizing to average demand distance one.
`pick_minimum` proves that the comparison selects the smaller of the
size scale and the mass scale. The executable comparison uses no real
powers or unknown constants.

`NormalizedOptimalSelected.complete_of_demand` proves termination with
the exact unread suffix on tapes with the stated budget when all demands
are reachable and at least one has different endpoints. The theorem
constructs feasible fractional lengths from that hypothesis and compares
the computed price against every real normalized comparator.
`cut_valid` gives an original-arc cut separating at least one demand.

For distinct reachable demands, a positive optimum, and the computed
positive threshold, `probability_bound` gives the finite-tape
upper-tail bound at twice the smaller of the two scales, with one
uniform constant. The probability is at most one half plus
`drawBound n · 2^(-T)`. For a zero returned fractional price,
`zero_price` proves every returned cut has zero cost on every tape
on reachable instances. This uses support inclusion through the finite
draw fallback and does not require a positive expected-cost bound.

The fixture computes optimum one on a one-direction graph and selects
the mass mode. A graph with both directions and opposite demands has
optimum two and selects the size mode. Both return original-arc cuts
and the exact unread suffix. A free-arc case returns a zero optimum and
the same cut and unread suffix.

The optimizer still uses exhaustive elimination. Polynomial optimization,
an executable vertex threshold, and high-confidence amplification of
the selected sparsest-cut entry remain open.
