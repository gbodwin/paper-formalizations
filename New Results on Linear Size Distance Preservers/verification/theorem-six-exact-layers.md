# Exact arbitrary layer sizes in the unweighted perfect-path construction

`DirectionEncoding.exact_arbitrary_layer_size` proves a fully quantified finite
version of the auxiliary Theorem6. For every dimension d>=2, one natural K>0
is chosen before every N,k,x. For every N>0, k>0, and natural x satisfying

    ((k+1)K)^(d(d-1)) x^(d+1) <= N^(d-1),

it constructs scalar directions w and the actual unweighted simple graph
`DirectionGraph.graph w N k` on

    Fin(k+1) × (Unit → ZMod N).

The second factor has cardinality exactly N, so every layer has exactly N
vertices. Its canonical paths have all of these proved properties:

- exactly kNx distinct graph edges;
- distinct actual native paths, with length k and one vertex in each layer;
- every vertex lies in exactly x of those paths;
- every graph edge belongs to exactly one path;
- every competing walk between a designated pair with length at most k is
  the designated canonical walk, hence every designated path is uniquely shortest.

The native-path and layering facts are the existing universal
`DirectionGraph.canonical_isPath`, `canonical_length` and `graph_layered`
theorems for this very graph; the new theorem additionally exports distinctness,
counts, incidence, ownership and endpoint-walk uniqueness explicitly.
There is no direction, geometry, perfect-power, path-uniqueness, or padding
premise supplied by the caller. The empty x=0 family is included.

For ell=k+1, the displayed natural-power budget is the exact finite form of

    x <= K^(-d(d-1)/(d+1)) N^((d-1)/(d+1)) ell^(-d(d-1)/(d+1)).

Thus the source fixed-dimension exponent is retained with a single
dimension-dependent constant and arbitrary prescribed layer cardinalities.
This explanatory real-power rearrangement is not claimed as a separately
named formal asymptotic theorem. The finite natural-power theorem is the
formal statement.

## Construction and rounding

1. Actual lattice-hull vertices give sharply many bounded integer directions
   in dimensions at least3. Primitive convex chains give the planar case.
   A common form supplies b^(d(d-1)) directions in a box of side C(d)b^(d+1),
   uniformly over positive integer b and every smaller requested family size.
2. Encode each d-dimensional vector in base B=(k+1)r. The code is below
   r B^(d-1), while every k-term coordinate sum is below B. Thus equality of
   encoded k-term averages decodes coordinatewise. Only this fixed-length
   rigidity is claimed; scalar convex rigidity for arbitrary averages is not.
3. Translation in ZMod N works for any N>=B^d. The encoded code bound gives
   the exact no-wrap inequality (k+1)r B^(d-1)<=N. This replaces the earlier
   restriction to perfect-power layer sizes without adding isolated vertices.
4. Integer rounding takes u=floor-root_(d(d-1))(x) and b=u+1 for x>0.
   Then b<=2u, u^(d(d-1))<=x<b^(d(d-1)); the factor2 is absorbed once in K.
   The stated budget supplies the required layer capacity exactly. For x=0,
   the actual empty direction family supplies every asserted property.

## Domain and verification boundary

The condition k>0 means at least two layers. The source's unrestricted
one-layer assertion with more than one distinct path through a vertex is not
claimed. The earlier depth-zero obstacle gadgets remain valid for their
separate main-result applications.

Seven independently reviewed draft bodies are assembled into three production
modules by changing imports only. The assembly manifest records every input
and output hash. Production-source build, defining-module axiom audit, official
kernel replays and index checks are recorded in the adjacent evidence. Full
exact-commit CI is separate. The fresh whole-package audit at939a39a9 is not
extended by this component review.

The original near-threshold square-root-deficit existential assertion remains
unresolved. This encoding retains the old direction/port count laws and does
not evade the separately proved construction-family obstruction. The generic
weighted obstacle-product lemma and the other source qualifications remain
as stated in the coverage inventory.

## Reproduction

From the repository root, after dependency builds:

    lake build LinearDistancePreservers
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditExactLayer.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.ExactLayerEncoding
    lake env leanchecker -v LinearDistancePreservers.ExactLayerDirections
    lake env leanchecker -v LinearDistancePreservers.TheoremSix
