# Natural subsequences inside the original near-threshold range

This component clarifies the quantifiers of the restricted count-template
obstruction. It does not produce a graph-existence counterexample.

Define the actual natural numbers

    N(q) = 2^(3q^2),
    T(k,q) = 2^(2q^2-kq).

For every real coefficient c, `exists_natural_subsequence` chooses one natural
k such that, along the natural index q tending to infinity,

    T(k,q) = o(N(q)^(2/3) exp(-c sqrt(log N(q)))).

This is Mathlib's actual `IsLittleO` at the natural `atTop` filter. The exponent
subtraction is exact once q>=k. The proof chooses k with

    k log 2 > c sqrt(3 log 2),

so the ratio of these two quantities is eventually exactly

    exp(-q (k log 2 - c sqrt(3 log 2))).

The vertex counts N(q) tend to infinity, and 2<=T(k,q)<=N(q) for
q>=max(k,1). These properties are proved, rather than left as rounding or
nonvacuity assumptions.

`every_deficit_has_bounded_count_subsequence` chooses this k and one positive
constant B=3 exp(6k^2), before q and before all count-template parameters.
Every instance of the connector-inclusive unlayered numerical template at
N(q),T(k,q) has E<=B T(k,q)^2, uniformly in its dimension and other scales.
Thus even a strictly little-o natural subsequence in every fixed
square-root-deficit range fails to give unbounded gain within this template.

## Exact scope

- This is a subsequence indexed by q; no terminal-count function on every
  natural N is defined here.
- The count-template hypotheses are exactly those of the reviewed
  `UnlayeredEnvelope.full_product_sqrt_deficit`.
- No unlayered graph implementation, arbitrary graph edge bound, or refutation
  of the original existential graph assertion is claimed.
- It neither improves nor weakens the certified actual graph lower bounds.

## Verification

The production module is a byte-identical copy of the reviewed draft. Adjacent
receipts identify the strict source build, defining-module axiom audit,
module indexes, independent official kernel replay and full exact-commit CI
as distinct stages. The historical whole-package audit remains scoped to
939a39a9; the updated corrected-main audit has its own frozen target.

After dependency builds, from the pinned repository root:

    lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "New Results on Linear Size Distance Preservers/LinearDistancePreservers/NaturalBoundary.lean"
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditNaturalBoundary.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.NaturalBoundary
