# Normalized sparsest-cut rounding contract

This document records the explicit interpretation used by the new sparsest-cut
modules. It is not a claim that the wording of Corollary 7 uniquely specifies this
normalization, and it is not a refutation of the printed corollary.

## Source correspondence

The source is Bodwin–Samborska, *Improved Upper Bounds for the Directed Flow-Cut
Gap*, arXiv:2604.03412v3. In `tex/intro.tex:234–235`, `W` is the total weight of a
fractional **multicut** whose demanded paths have weight at least one. The
sparsest-cut discussion at `tex/intro.tex:314–325` concerns cut cost divided by
the number of separated demands, cites AAC07, and states the size/mass minimum
up to subpolynomial factors. It does not specify the sparsest-LP normalization
or redefine `W` for that normalization.

AAC07's graph edge weights are costs, whereas its LP lengths use a separate
symbol. Preserving graph edge costs through that reduction does not by itself
prove preservation of total fractional length. The implementation therefore
uses an explicit, independently proved threshold reduction, not an assumed
invariance of the source's `W`.

The pinned PDF and TeX fingerprints are recorded in this paper library’s README. The primary AAC07
reference is https://web.math.princeton.edu/~nalon/PDFS/aac.pdf, Sections 2 and 7.

## The formal parameter and theorem

For a finite set `P` of `m` distinct ordered unit-demand pairs, a nonnegative
finite length assignment `w`, and nonnegative costs `c`, write

- `S = Σ_{p∈P} d_w(p)`, using actual directed distances;
- `C = Σ c w`, over vertices or actual graph edges as appropriate;
- `W = Σ w`, over those same variables;
- `W_avg = m W / S`.

The main theorems assume each demanded distance is finite and `S > 0`. For
every `ε > 0`, a positive constant `K` is chosen before the vertex type, graph,
demand set, lengths, and costs. An actual cut then has positive separation
count and satisfies

`cut cost / number separated ≤ K n^ε min(n^(1/3), sqrt(W_avg)) C/S`.

`SparsestVertexCorollary.vertex_sparsest_min_uniform` uses internal-vertex
distance and cuts, retaining demand endpoints. Its underlying verified
rounding inputs are `AdaptiveVertexBound.vertex_rounding_uniform` and
`AdaptiveVertexBound.vertex_weight_rounding_uniform`.

`SparsestEdgeCorollary.edge_sparsest_min_uniform` uses directed edge-length
distance and actual edge cuts, explicitly `X ⊆ graphEdges G`. Its rounding
inputs are `AdaptiveEdgeBound.edge_rounding_uniform` and
`AdaptiveEdgeBound.edge_weight_rounding_uniform`.

`vertex_sparsest_average_one_uniform` and `edge_sparsest_average_one_uniform`
also state the same bounds with raw total weight under the explicit normalization
`S = |P| > 0`.

These statements round every individual finite length assignment. They do not
assume an LP optimizer, a source-prescribed rule for choosing among optimizers,
a concurrent-flow duality theorem, or an implementation/runtime theorem. Those
additional statements require separate definitions and proofs.

## What is proved in the bridge

`FiniteHarmonicThreshold.exists_threshold` orders all demand indices by
nonincreasing distance, including repeated distance values and zeros. A rank
maximizer supplies a positive threshold `τ` and actual threshold count `k`
satisfying `S ≤ H_m τ k`. It follows that `τ ≥ S/(m H_m)` and
`W/τ ≤ H_m W_avg`. The selected threshold demands are shown to be a subset of
the demands actually separated by the returned graph cut.

The exact bridge losses are `H_m` for the size bound and `H_m^(3/2)` for the
mass-sensitive bound. The proof then uses `m ≤ n²` and the proved bound
`H_m ≤ 1 + 2 log(n+2)` to absorb both losses into arbitrarily small exponent
slack. Constants remain uniform over all instances.

Both graph bridge modules prove exact positive scaling of extended distances,
the fractional ratio, and `W_avg`, as well as construction of the normalization
`S = m`. In this average-distance-one normalization, `W_avg` is raw total
weight. Under `S = 1`, it is `mW`, and the modules record this identity explicitly.

## Degenerate cases

- If a demand is unreachable, the empty cut already separates it with zero
  cost. Separate `unreachable_zero_sparsity` theorems establish this case.
- Empty demand families have separation count zero. They are not assigned a
  mathematically meaningful positive-denominator sparsest ratio.
- Finite zero-distance demands are allowed and remain in `m` and the actual
  demand count. A zero distance sum is equivalent to every finite demanded
  distance being zero. The ratio theorem excludes only this all-zero sum.
- Zero fractional cost and zero graph costs are allowed without cancellation
  by the fractional objective. Empty vertex types cannot satisfy `S > 0`.

## Verification status

All five modules passed strict Lean compilation with `-j1`,
`-DautoImplicit=false`, and `-DwarningAsError=true` on 9 October 2026. All 115
owned declarations passed a transitive axiom audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Each module passed an isolated replay
using the official `LeanChecker.replayFromImports`. Exact source hashes,
commands, counts, and preserved logs are in
[`verification/sparsest-normalized/manifest.json`](verification/sparsest-normalized/manifest.json).
These gates certify the explicit contracts above; they do not resolve the
source paragraph's unspecified normalization by attribution.
