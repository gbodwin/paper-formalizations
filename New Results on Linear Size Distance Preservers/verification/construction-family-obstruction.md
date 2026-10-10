# Scope of the construction-family obstruction

The four theorems in `ConstructionEnvelope.lean` concern the complete edge
count of the specific sharp-direction obstacle-product family, including
isolated-vertex padding. They do not give an upper bound for arbitrary graphs.

For natural M,n,b,ell,d,N,T,E, assume d>=1, ell>=1 and the exact count conditions

- ell*b^(d+1) <= n;
- n^d*b^(d(d-1)) <= M;
- M*ell*n^d <= N;
- M <= T;
- E = M*n^d*b^(d(d-1))*(ell+1).

Then

    E^[d(d+1)] <= 2^[d(d+1)] T^[(2d+1)(d-1)] N^(2d),

and taking the exact positive root gives

    E <= 2 N^[2/(d+1)] T^[(2d+1)(d-1)/(d(d+1))].

If N>1, T>0, log T = 2log N/3-t, and 0<=t<=K sqrt(log N), K>=0,
then the final theorem proves

    E <= 2 T^2 exp(27 K^2/8),

uniformly over every d and every count choice satisfying the hypotheses.
The d=1 endpoint and zero auxiliary powers are included.

The actual family uses the stronger conditions n>=(k+1) C b^(d+1)
with C>=1, port capacity at most M, N>=2M+M(k+1)n^d and T>=2M.
Thus its counts satisfy these numerical hypotheses with ell=k+1.
The result even allows ideal outer port capacity; no Behrend density loss
is imposed. Merely improving geometric constants or the outer port set
cannot make this family force an unbounded E/T^2 at fixed K.

This is stronger than the preceding `TheoremFourRateAudit`, which bounded
only the displayed lower-bound expression. It still does not refute the
original near-threshold existential graph claim: a graph family with different
count laws, or another unweighted metric gadget, is outside its scope.
The original larger uniform-d displayed rate and sharper existential claim
remain explicitly unresolved at this checkpoint.

The component passed strict source elaboration, all 15 defining-module
axiom checks, independent kernel replay and every library index check, plus
an independent exact-source semantic review. The fresh end-to-end audit at
939a39a9 continues to apply only to its unchanged 91 mathematical modules;
this added component has its own narrower review. No full original-paper
completion is asserted.
