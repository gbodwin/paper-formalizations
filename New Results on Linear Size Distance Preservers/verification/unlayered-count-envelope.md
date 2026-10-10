# An ideal unlayered count-template obstruction

This component investigates one alternative to the layered construction. It
proves an upper bound for the explicit numerical template below. It does not
construct an unlayered graph, claim that every unlayered construction has
these counts, or refute the original existential graph assertion.

## Exact hypotheses and conclusion

For natural M,n,b,ell,d,N,T,E with d>=1, assume

    ell * b^(d+1) <= n
    n^d * b^(d(d-1)) <= M * ell
    M * n^d <= N
    M <= T
    E <= M * n^d * b^(d(d-1)).

Here the intended optimistic straight-line interpretation removes the inner
layer factor from the vertex count, while dividing the number of separately
assigned length-ell paths by ell. The hypotheses themselves, not this
interpretation, define the theorem's scope. No positivity of the natural
scales is needed by the power envelope; d=1 and zero scales are covered.

`UnlayeredEnvelope.edge_power_envelope` proves

    E^(d^2+1) <= T^((2d-1)(d-1)) * N^(2d).

`edge_envelope` takes the exact positive root and proves

    E <= N^(2d/(d^2+1)) * T^((2d-1)(d-1)/(d^2+1)).

With N>1 and T>0, write log T=(2/3)log N-t. For any fixed real K>=0 and
0<=t<=K sqrt(log N), `full_edge_sqrt_deficit` gives

    E <= T^2 * exp(6 K^2),

uniformly in the dimension and every scale satisfying the five hypotheses.
The improved denominator d^2+1 therefore still cannot provide an unbounded
edge/terminal-square ratio within this count template at a fixed
square-root-log deficit. The argument is algebraic: its exact logarithmic
ratio is ((3d+1)t-(2/3)log N)/(d^2+1), bounded by 6t^2/log N.

`full_product_sqrt_deficit` includes the two connector edges per assigned
path. For ell>=1, an exact assignment count P*ell=n^d*b^(d(d-1)), P<=M,
and E<=M*n^d*b^(d(d-1))+2*M*P, it derives the capacity hypothesis and gives

    E <= 3*T^2*exp(6 K^2).

This full-count wrapper is still a numerical template; no graph implementation
or assertion that a particular external construction realizes its counts is
supplied.

## What remains open

A different direction family, path-incidence scheme, overlapping-port
construction, or other graph family may evade one of these five count
hypotheses. No bound for such a family follows here. In particular, the
original unweighted near-threshold existential assertion is still unresolved.
The certified displayed uniform-dimension lower bound and corrected
three-quarter-power logarithmic deficit are unchanged.

## Verification

The production source is a byte-identical copy of the hash-reviewed draft.
Adjacent local-gate and source-review receipts distinguish strict elaboration,
allowed-axiom audit, official kernel replay and full exact-commit CI. The
historical whole-package audit remains scoped to 939a39a9.

From the pinned repository after dependency builds:

    lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "New Results on Linear Size Distance Preservers/LinearDistancePreservers/UnlayeredEnvelope.lean"
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditUnlayered.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.UnlayeredEnvelope
