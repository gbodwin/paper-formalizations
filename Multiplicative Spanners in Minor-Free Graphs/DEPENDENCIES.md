# Mathematical dependencies and completion boundary

This is an in-progress formalization of Bodwin–Hoppenworth–Tan,
*Multiplicative Spanners in Minor-Free Graphs*, arXiv:2504.16463v1.
The fixed-k conditional sparsity and connected lightness lower-bound
implication is proved locally. The main upper bounds remain open.

## Reused proved foundations

- `LightSpanners.Basic`, `.Greedy`, `.Distance`, `.Girth`, `.Construction`:
  actual mathlib graph walks, positive real edge weights, ENNReal weighted
  distances, sorted-edge greedy output, stretch and weighted girth. Reused
  source files match the existing project byte for byte.
- `VFTSpanners.Moore`: graph-level Moore bound with explicit uniform constant
  2. Its proof includes path counting and dense-core extraction. This is a
  proved import, not an assumed external theorem.
- Lean 4.34.0; mathlib commit
  `5ed2965256430c3649e86755f9576b54eca72435`.

## Remaining substantial dependencies

1. **Density increment, Theorem 9.** A genuine branch-set minor framework
   and the full small-dense-subgraph construction are required. Postle,
   arXiv:2006.14945v3, is the original cited result. Version 4 is a withdrawal
   because of a stronger coloring result, not a retraction of this theorem;
   see the source paper's footnote 3 and Delcourt–Postle,
   arXiv:2108.01633v5, the remark after Theorem 2.2. No density-increment
   axiom or assumed oracle has been introduced. The reformulation also
   needs the actual clique-minor density threshold (Kostochka–Thomason,
   average degree O(h sqrt(log h))): one chooses D at that threshold to
   exclude Postle's dense-minor outcome. This dependency is explicit in
   Delcourt–Postle v5, page 4, between Theorems 2.1 and 2.2. The original
   density-increment theorem uses edge density e(G)/v(G), rather than
   average degree 2e(G)/v(G); the factor of two must be tracked. Its
   constant-density and edgeless boundary cases also require separate
   treatment. None of these external graph theorems is currently proved
   by the density-elimination arithmetic module. `PostleMates` now proves
   Proposition3.2 using an actual induced graph and degree-sum count, and
   `PostlePullback` proves Corollary3.3 for integer-width genuine bounded
   minor models. Technical Theorems3.6,3.7 and their density increment
   construction remain open. Harmless source arithmetic repairs are
   separately disclosed in CORRECTIONS.md.
2. **Minor-preserving subdivision, Lemma 20.** The existing light-spanner
   subdivision proof needs an explicit clique-minor transport theorem.
   The new `SubdivisionMinor` module proves actual one-edge reflection for
   h ≥ 4. `MinorNormalization` now carries the invariant through actual
   repeated subdivisions, scaling and rounding, with explicit 2n−1 and 1/2
   quantitative bounds. `TriangleMinor` and `ThreeMinorNormalization` now
   close h=3 using actual cycle clique-models and the forest/tree argument;
   the combined theorem covers every h>=3.
3. **Actual clustering, Claims 22–23.** Must construct branch sets and
   short-cycle lifts with disjointness, connectedness and edge bounds proved.
   `ClusterGraph` now constructs the quotient minor and proves heavy-edge
   uniqueness intrinsically from weighted girth, including ties. It takes
   an explicit cluster family. The fourth batch constructs actual cycle
   lifts via edge removal and bounded host walks and proves Claim23 under
   those source invariants, with s≥4g. Hierarchy existence remains open.
4. **Charging, Lemma 24.** The proof is implicit in the cited BLWN17
   hierarchy. Its construction and charging invariants must be formalized;
   they are not accepted as a black-box hypothesis in a completed theorem.
5. **Girth-conjecture lower bound.** The explicitly conjectural premise is
   allowed by the paper. `girth_conjecture_sparse_lower_bound_all_h` now proves
   the full fixed-k sparsity family for h≥3 and every sufficiently large n,
   from that genuine premise alone. Exact finite edge extraction, rounded
   parameters, minor exclusion, copies/padding and the bounded-h star case
   are all constructed and proved. Constants and quantifier order are explicit.
   `girth_conjecture_connected_lower_bound` now strengthens this to an actual
   connected exact-n graph with a genuine unit-weight input MST and both
   lower bounds. The hub completion, bridge/girth argument, branch-set
   clique-minor localization, pendant reflection and MST existence/weight
   are proved. Its extra factor-two loss preserves the uniform h exponent.
   No disconnected MST ratio or minimum-spanning-forest convention is used.

## Completion gates

Local compilation, all-declaration allowed-axiom audit, independent kernel
replay, independent semantic review and exact-commit CI are recorded
separately. After the complete advertised scope is proved, a fresh skeptical
final auditor is required before a link is placed alongside this paper on
Greg's research website. Root coordinates that final audit and publication.
