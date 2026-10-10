# Generic finite positive-real weighted obstacle product

`ObstacleProduct.exists_real_weighted_product` proves the weighted metric join
of Lemma 7 for the actual finite three-layer outer graph and the actual layered
inner graph represented by `ObstacleProduct.Data`. Input weights are arbitrary
finite nonnegative real numbers, strictly positive on actual edges. They need
not be integers, share a prescribed baseline, or have a supplied positive gap.

The hypotheses `RealOuterOptimal` and `RealInnerOptimal` state unique shortest
native paths in the actual input graphs. They do not assume anything about
optimality in the output graph. The theorems `real_outer_optimal_of_paths` and
`real_inner_optimal_of_paths` derive these hypotheses from the ordinary
simple-path formulation, using only positivity on actual input edges.

One positive epsilon is chosen before every endpoint class and competitor.
For every positive delta at most epsilon, the actual product graph has weight

    realPrimary wl wr + delta * realSecondary wi.

Thus each connector keeps its original outer weight, and each internal gadget
edge has exactly delta times its original inner weight. Every designated native
fullWalk is uniquely shortest against every native walk, including cyclic ones.
The function `product_weight_symmetric` proves symmetry whenever the input
inner weight is symmetric; connector weights are symmetric by definition.

`exists_real_weighted_forcing` uses the same uniform epsilon. For every admissible
delta and every actual subgraph H preserving the designated endpoint distances,
where distance is the infimum over actual weighted walks, it proves

    H = graph D,
    |E(H)| = |B| * |J| * (k+2).

All vertex/edge counts, layering, designated simple routes and edge covering
come from the actual existing obstacle-product graph. No graph-forcing,
path-projection, perturbation, gap-size or product-uniqueness certificate is
supplied by the caller.

## Proof structure

1. A recursively constructed outer walk deletes internal gadget edges and keeps
   actual connector edges. Its length is exactly the connector count, and its
   real cost equals the primary product cost.
2. Outer unique optimality gives weak primary optimality. Equality forces the
   projected walk to equal the actual two-edge outer route. The existing walk
   decomposition then confines the competitor to one inner gadget, and outer
   injectivity identifies its port labels.
3. Inner unique optimality supplies a strict secondary comparison for every
   different route. The finite path perturbation theorem chooses one epsilon
   for all actual simple paths and all endpoint classes at once.
4. Positive dart costs make every proper bypass strictly cheaper. Therefore
   simple-path optimality and uniqueness extend to every native walk. No
   assumption that the projected walk is simple is made.
5. Actual native infimum-distance preservation forces all covered edges. The
   edge-set identity gives equality with the entire product graph and its exact
   edge count.

## Scope and verification

Strict positivity on actual edges is explicit. Zero-weight, signed or infinite
input weights and nonfinite input graphs are outside this theorem. The existing
unweighted result, which works with epsilon=1, remains separately proved.
The main Theorem 3 normalized-integer construction and all prior mathematical
modules are unchanged. This generic metric join does not prove the unresolved
square-root-deficit near-threshold existential assertion.

Six source-compiled draft bodies are assembled into three production modules
by consolidating imports only. The adjacent manifest binds all input/output
hashes. Local defining-module axiom audit, official kernel replays, module-index
checks and independent exact-source semantic review are recorded separately.
Full exact-commit CI is a distinct gate. The earlier qualified whole-package
review at939a39a9 is not silently extended to this addition.

## Reproduction

    lake build LinearDistancePreservers
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditWeightedProduct.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.WeightedProjection
    lake env leanchecker -v LinearDistancePreservers.WeightedLexicographic
    lake env leanchecker -v LinearDistancePreservers.WeightedPerturbation
