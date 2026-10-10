# Mathematical dependencies and completion boundary

This is an in-progress formalization of Bodwin–Hoppenworth–Tan,
*Multiplicative Spanners in Minor-Free Graphs*, arXiv:2504.16463v1.
No main asymptotic theorem is currently represented as complete.

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
   axiom or assumed oracle has been introduced.
2. **Minor-preserving subdivision, Lemma 20.** The existing light-spanner
   subdivision proof needs an explicit clique-minor transport theorem.
3. **Actual clustering, Claims 22–23.** Must construct branch sets and
   short-cycle lifts with disjointness, connectedness, tie order and edge
   bounds proved. Numerical inequalities alone do not establish these claims.
4. **Charging, Lemma 24.** The proof is implicit in the cited BLWN17
   hierarchy. Its construction and charging invariants must be formalized;
   they are not accepted as a black-box hypothesis in a completed theorem.
5. **Girth-conjecture lower bound.** Its explicit conjectural premise is
   allowed by the paper. The implication still requires graph existence,
   clique-minor exclusion by edge count, disjoint copies and exact-size
   padding. A generic high-girth edge-forcing lemma is only one step.
   The source uses a disjoint union for its sparsity construction. The
   lightness conclusion additionally needs a connected construction (for
   example a verified one-vertex sum) or an explicit minimum-spanning-forest
   convention. No disconnected MST ratio will be silently adopted.

## Completion gates

Local compilation, all-declaration allowed-axiom audit, independent kernel
replay, independent semantic review and exact-commit CI are recorded
separately. After the complete advertised scope is proved, a fresh skeptical
final auditor is required before a link is placed alongside this paper on
Greg's research website. Root coordinates that final audit and publication.
