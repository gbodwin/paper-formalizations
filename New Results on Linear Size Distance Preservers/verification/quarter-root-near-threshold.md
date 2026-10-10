# Stronger corrected near-threshold range

`TheoremFourGeneral.superquadratic_quarter_root` proves this exact finite
statement. For natural N,T satisfying

    log N >= 8^4,  2 <= T <= N,
    T <= N^(2/3) exp(-32 (log N)^(3/4)),

there are an actual undirected unweighted simple graph G on Fin N and a
terminal set S of cardinality exactly T such that every H<=G preserving all
native terminal-to-terminal `SimpleGraph.edist` values satisfies

    T^2 exp(sqrt(log N)) <= |E(H)|.

No dimension, lattice, capacity, scale-selection, or graph-forcing premise is
supplied by the caller. The proof chooses d=floor((log N)^(1/4)). Its explicit
floor bounds place d in the elementary-sphere regime with A=1. The terminal
deficit supplies a gain of at least 16 sqrt(log N), while the actual graph
construction loses at most 15 sqrt(log N).

`superquadratic_quarter_root_eventual` fixes each real target factor B before
one natural N0, and then works simultaneously for every N>=N0 and every
admissible T in the displayed range, forcing |E(H)|>B T^2. The threshold is
coarse and the quantified finite domain may be empty for small N.

This improves the earlier proved logarithmic deficit exponent 5/6 to 3/4.
The source's stronger square-root-logarithmic deficit remains unresolved.
The construction-family upper envelope is not an arbitrary-graph upper bound
and does not refute the source's existential assertion.

## Reproduction and review

From the repository root, after building dependencies:

    lake build LinearDistancePreservers
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditQuarterRoot.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.QuarterRootParameters
    lake env leanchecker -v LinearDistancePreservers.QuarterRootTheorem
    lake env leanchecker -v LinearDistancePreservers.QuarterRootEventual

All three production sources, all 10 defining-module declarations, all three
official kernel replays, and all four library indexes passed locally. A
non-failing style warning is recorded explicitly in the evidence. Exact-source
independent component review checked both finite and eventual quantifiers.
Full exact-commit CI is a separate gate. The older qualified whole-package
audit is not extended by these component checks; the original paper remains
incomplete against the coverage inventory.
