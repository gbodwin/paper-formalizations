# Multiplicative Spanners in Minor-Free Graphs

Greg Bodwin, Gary Hoppenworth and Zihan Tan.
[Source paper, arXiv:2504.16463v1](https://arxiv.org/abs/2504.16463v1).

**In progress. The main asymptotic sparsity and lightness theorems are not
complete.** This checkpoint starts the actual graph proofs and records
three source corrections without silently changing the paper.

## Scope

- Finite simple undirected graphs and actual mathlib walks.
- Explicit branch-set minor models: nonempty, pairwise disjoint connected
  vertex sets, with an actual host edge for every model adjacency.
- Actual sorted-edge greedy construction, with ties handled by its order.
- Positive real edge weights for girth interpretation; nonnegative weights
  suffice for stretch. ENNReal shortest distances handle disconnected pairs.
- Paper Claim 19 is replaced by the exact `t+1` weighted-girth guarantee.
  A parameterized actual greedy triangle refutes the printed threshold,
  including arbitrarily small positive `sε`; the numerical repair uses
  `s≥4g`. See [CORRECTIONS.md](CORRECTIONS.md).

## Proof modules

- `Minor`: branch-set model, hereditary clique-minor exclusion, cardinality
  obstruction, singleton-branch embedding.
- `Greedy`: Claims 14, 15, 18; corrected Claim 19; shortest-distance bound;
  exact scalar repair needed by Claim 23.
- `Claim19Counterexample`: actual greedy triangle family; metric-edge and
  K₄-minor-free hypotheses checked explicitly.
- `SmallMinors`: K₂-minor-free graphs are exactly edgeless graphs, clarifying
  the bounded-h lower-bound domain.
- `LowerBound`: every `(2k−1)`-spanner of an unweighted girth-`>2k` graph is
  the entire graph. This is the edge-forcing step, not the full lower bound.
- `Moore`: Theorem 11, with the explicit uniform constant2 and exact power
  form, reusing the repository's proved graph-level Moore theorem.
- `MinorEdgeCount`: a branch-set minor has at most as many edges as its host;
  fewer than `h.choose 2` host edges exclude a Kₕ minor.
- `DensityAlgebra`: eliminates the witness size and extracts the exponent
  `2/(k+1)` with all constants explicit. The small dense witness is not
  assumed to exist in a completed graph theorem.

The precise verification state is in [verification/status.json](verification/status.json).
[The source inventory](verification/source-inventory.json) accounts for all
25 unique numbered items, including cited background and conjectures.

## New graph components in this checkpoint

- `MinorComposition`: constructs walk lifts and genuine composite minor models.
- `MinorRestriction`: injective host transport, induced restriction and
  reduction to actual connected components; componentwise edge obstruction.
- `GirthComponents`: injective cycle transport and componentwise girth.
- `DisjointCopies`: an explicit graph on `J × V`, with exact vertex and
  edge multiplicities, minor/girth preservation and spanner edge forcing.
  This is the finite core-copy step, not a complete asymptotic lower bound.
- `MinorSingletonDegree`: singleton branch degree cannot exceed host degree.
- `SubdivisionMinor`: the actual one-edge `LightSpanners.subdivideEdge`
  preserves clique-minor exclusion for `h ≥ 4`. Walks are contracted with
  support control; model branches and crossing edges are built explicitly.
  Full normalization and small-h completion are still separate obligations.
- `DensityLinearLoss`: the arithmetic bound has uniform coefficient 2 and
  linear density loss L. Existence of the dense witness remains open.

All 15 modules compile. The audit covers 151 declarations, and every new
module plus the unchanged borrowed subdivision module passed local kernel
replay. The initial eight-module checkpoint has independent semantic review
and full exact-commit CI success. The seven additions have a separate
component review and exact-commit CI gate, recorded in the status file.
The initial source manifest is `verification/source-hashes.json`; the
15-module source manifest is `verification/checkpoint2-source-hashes.json`.

## Remaining work

The density-increment theorem, full minor-preserving normalization, actual cluster
hierarchy/cycle lifts, BLWN17 charging argument, and complete conditional
girth-conjecture family construction remain open. See
[DEPENDENCIES.md](DEPENDENCIES.md). None is disguised as an axiom, supplied
oracle, or hidden premise of a purported completed main result.

## Checks

From the repository root:

```sh
lake build MinorFreeSpanners
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

Local compilation, all-declaration axiom audit, independent kernel replay,
independent semantic review and exact-commit CI are separate gates. A fresh
skeptical final audit is additionally required on completion before a link
is added alongside the paper on Greg's research website.
