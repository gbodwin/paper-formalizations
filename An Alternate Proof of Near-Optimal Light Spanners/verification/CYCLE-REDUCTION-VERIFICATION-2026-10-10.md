# Complete unit-spanning-cycle reduction — 2026-10-10

This extends the fully CI-verified unit-MST checkpoint
`e742a8b07f6789c50cba125d00acd6b9685f75f9`:
https://github.com/gbodwin/paper-formalizations/actions/runs/38057329186
Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`
are unchanged.

## Exact theorem

`LightSpanners.unit_spanning_cycle_reduction_of_mst` completes Lemma 3.5
for finite positive-weight non-forest graphs, a nonnegative weighted-girth
threshold, and an explicit reference MST. It constructs an actual graph on
`Fin n′`, actual weights, a reference MST, and an oriented unit spanning cycle,
with `n′ ≤ 4n−4`, the same weighted-girth lower bound, and at least one quarter
of the original lightness. A unit spanning cycle includes the guarantee that
every graph edge has weight at least one.

The theorem assumes no spanning tour, representative choice, copied graph,
cycle correspondence, normalization, subdivision budget, or lightness transfer.
The reference MST is only used to state the input lightness. The existing
Kruskal theorem constructs a bottleneck-certified MST internally.

## New proof components

- `TreeTour`: leaf-removal induction constructs a closed tree walk of length
  exactly `2(n−1)` covering every vertex. It also proves that positive weighted
  girth in a non-forest is less than the vertex count.
- `TourCycle`: actual positions in that closed walk define a graph homomorphism
  from the canonical cycle. Surjectivity gives a representative for each old
  vertex. Every cycle in a connected degree-two graph is spanning, proving
  the canonical unit cycle's weighted-girth bound.
- `CycleProjection`: if a selected edge has a unique projected preimage,
  projecting its cycle complement and erasing loops yields an old cycle
  containing the selected projected edge, without increasing weight.
- `VertexCopies`: the new graph is the canonical position cycle together with
  each original non-tree chord lifted through its chosen representatives.
  Chords have unique projected preimages. Cycles consisting only of base
  edges and cycles containing a chord receive separate girth proofs.
- `CopyWeights`: exact finite-sum decomposition into base and old chords proves
  that total graph weight does not decrease. An actual new unit MST has weight
  bounded by twice the old unit-tree weight, yielding half the old lightness.
- `CycleReduction`: composes the already proved unit-MST stage with this
  spanning-cycle stage. The bounds `2n−1` then `2n′−2` give `4n−4`; the two
  half-lightness transfers give one quarter.

No literal bijection of cycle sets, nor exact equality of normalized weighted
girth, is claimed. The proved lower-bound preservation is the needed property.
A stronger statement that the tree tour uses each directed edge exactly once
is unnecessary and is not included in `exists_tree_tour`.

## Checks

- Aggregate build: passed, 25 source modules plus aggregate, 1400 jobs including
  cached dependencies.
- All-declarations audit: passed, 381 declarations including private/generated
  declarations, with only `propext`, `Classical.choice`, and `Quot.sound` allowed.
- Selected axiom audit, including the full reduction theorem: passed.
- All four repository module indexes: passed using `mk_all --check`.
- Sequential independent kernel replay: passed for all 25 source modules.
- Repository-wide build and audit: delegated to exact-commit CI after publication.

The local gate log is `cycle-reduction-2026-10-10-gate.txt`. Focused local checks
are not described as repository-wide compilation. Independent semantic review
of the chord-projection and copied-graph girth argument passed; the final
weight/composition review also passed and is recorded in
`copy-cycle-semantic-review-20261010.json`, pinned to the reviewed source hashes.
`git diff --check` passed before publication.

## Remaining paper scope

The graph reduction is complete within the hypotheses stated above. Safe and
extra-safe bucket paths, last-differing-bucket cycle extraction, dispersion,
hiker suffix exchanges and small-bucket floor handling, truncation/deletion,
independent edge sampling, and Theorem 5.1's final lightness bound remain open.
There are no project axioms, proof holes, or assumed replacements for these
missing combinatorial arguments.
