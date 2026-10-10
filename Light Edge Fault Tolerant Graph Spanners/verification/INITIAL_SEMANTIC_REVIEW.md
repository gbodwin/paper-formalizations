# Independent semantic review: initial four-module checkpoint

Date: 2026-10-10 (UTC). Paper: *Light Edge Fault Tolerant Graph Spanners*, arXiv:2502.10890v2.

## Verdict

**No semantic blocker found in the bounded checkpoint.** The four modules prove substantive foundational statements using actual graph walks, edge deletion, a recursive seeded construction, a finite minimum, and explicit finite Bernoulli masses. I found no vacuous graph predicate, hidden final lightness assumption, or assumption of the sampling conclusion. This is acceptance of these foundational components, not certification of the paper's main results.

This review read the source and relevant dependencies; it did **not** compile, run a kernel replay, or independently reproduce an axiom audit. No proof source was edited. The later EFT-specific shortest-path equivalence draft was not reviewed or certified.

## Exact reviewed inputs

Paths below are relative to `Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` in the checkout. SHA-256:

- `Basic.lean`: `904afbdb6b764ba7c81bd0623cb38ee71ef0ddc3136454a8dc5197696ed1d66f`
- `SeededGreedy.lean`: `0ac99a0ff6ee9864341acb5d6b1672cb8e059efb7a709a9748c0b4dbf002f862`
- `ConnectivityOptimum.lean`: `2840e414eb2138431b47730c46205fc54708f3ef30d76f67b1d86ce5be6c83ad`
- `BlockerSampling.lean`: `47a6b5d729561b82e9b283aeb89ad3e7080f97eabcb465cf4f03e98621d7cc15`

The inspected `LightSpanners` dependency tree is unchanged from checkout HEAD `90b270f5442b3ebe50bd41a45f501b2277380d71` (verified by a path-restricted Git diff). Relevant inspected modules: `Basic`, `Greedy`, `Construction`, `Distance`, `MinimumTree`, `Weight`, and `FiniteSampling`.

Source pins:

- v2 PDF: `8552afdf89b6a44ed642154379dfd3556bc6471cedb90c518733991123489b55`
- v2 HTML: `b1f899f39a3fb8cf36fe0402c81b44138e4b7e14f11766114ad4e8665e6ba603`
- extracted `paper.txt`: `acdb645018c6a6fe8f03d56427ddc8e91f532d15e90fff13294226413fb7ed68`
- `review/source-corrections.md`: `f0bda2e7229332ebb38c511f44a7cec30c66d5225d4c11a39e34d842df880e24`

I compared the extracted source at Definitions 1, 5, 7–8, Algorithm 1/Theorem 18, and the relevant sampling/estimator discussion, together with the supplied correction audit. The PDF/HTML are pinned for source identity; this was not a new visual PDF audit.

## Findings by component

### 1. Graph and fault semantics

`Basic.lean:11–16` deletes actual unordered edges using mathlib's `SimpleGraph.deleteEdges`. `IsEFTSpanner` requires a genuine subgraph and replaces every walk remaining after each fault set by a walk with the same endpoints and bounded weight. It does not simply demand a local inequality or assume connectivity. Unreachable pairs impose no walk obligation, while every reachable pair gets an actual witness; the connectivity consequence at lines 57–65 is therefore meaningful even on disconnected graphs.

Quantification over all finite subsets of unordered vertex pairs, including nonedges, is a harmless extension of the paper's faults restricted to `E(G)`: intersecting with `E(G)` leaves deletion in both `G` and its subgraph unchanged and cannot increase fault count. `FTCovered` appropriately excludes the candidate edge from the fault set, because stretch is needed only for surviving input edges.

The missing-edge connectivity lemma at lines 77–96 is sound even when the supplied fault set contains that missing edge: erase it before invoking preservation, then use its absence from `Q` to identify the two faulty preserver graphs. No packing theorem is smuggled into this result.

### 2. Seeded greedy construction and edge test

`greedyEdges` is an actual recursion. It processes the tail first, retains `seed`, and either retains the current edges or inserts the current candidate according to `FTCovered`. Its source graph is exactly the seed union the input list, and `greedy_subset` excludes additional edges. `greedy_covered` derives final coverage from the decision test and monotonicity, using the one-edge walk for an inserted edge. `output_isEFTSpanner` then proves the result for every finite input graph and seed subgraph, with stretch at least one and nonnegative weights.

The arbitrary seed is a legitimate strengthening of correctness, not an assumption of optimality. The paper's Algorithm 1 is obtained by choosing a minimum `2f`-fault connectivity preserver as the seed; the separately proved minimum exists. No lightness property follows merely from greedy correctness.

The concrete input filters out seed edges from the dependency's duplicate-free, nonincreasing-weight ordering. Tail-first evaluation thus visits non-seed edges in nondecreasing weight order; equal weights have an actual list order. At a genuine iteration the candidate is absent from the current edge set. `test_restrict_faults` proves that intersecting arbitrary faults with the current finite edge set preserves the coverage test. Consequently its extra `e ∉ F` condition is automatic for the paper's current-edge faults at those iterations. For arbitrary abstract lists/seeds that condition should not be silently dropped.

The walk-based rejection test and the paper's shortest-distance test agree in the finite nonnegative-weight regime, using the inspected dependency's `covered_iff_distance`; unreachability corresponds to infinite distance. The checkpoint does not itself package an EFT-specific equivalence theorem. Its definitions must not be advertised as unrestricted equivalence for negative weights or zero/negative stretch. Correctness actually assumes nonnegativity of the entire weight function on `Sym2 V`, which can be satisfied by a nonnegative extension off the graph.

Theorem 18's corrected `≤` condition and monotonic growth of `H` are implemented. Lemma 20's last-processed maximum-edge tie argument remains a later obligation, not a result established here.

### 3. Optimal connectivity-preserver weight

`ConnectivityOptimum.lean:11–28` minimizes the actual edge-weight sum over all genuine fault-connectivity preservers. The feasible set is nonempty because it contains `G`, and finite because the vertex type is finite. This proves an attained minimum without an oracle, connectedness assumption, or positivity requirement. Uniqueness concerns the minimum **weight**, appropriately allowing multiple minimizing graphs. Monotonicity follows from containment of feasible classes as the fault budget increases.

`competitiveLightness` is a ratio against an explicit `Q`; it denotes the paper's competitive lightness only when `Q` is supplied with the stated minimum-preserver property. Choice independence is genuine. Lean's totalized division also defines it at zero denominator, so future nontrivial lightness bounds must retain their positive-denominator or explicit degenerate-case conditions, as the comment already says.

### 4. Bernoulli sampling and threshold repair

The dependency defines `mass U p S = p^|S| (1-p)^|U\\S|`, proves total mass one, nonnegativity for `0 ≤ p ≤ 1`, and exact inclusion probabilities by finite-product expansion. `pair_probability` therefore derives genuine pairwise independence for distinct candidates and blockers; it does not assume a probability law as a hypothesis.

`survival_union_bound` proves the joint survival lower bound `p - |B| p²` by a pointwise indicator inequality and finite summation. Its hypotheses `B ⊆ U` and `e ∉ B` matter: they express relevant sampled blockers and prohibit self-blocking. The latter is explicit rather than omitted. Substituting `p = 1/(2f)`, `0 < f`, and `|B| ≤ f` correctly gives survival at least `1/(4f)`, including `f=1`. The old endpoint identity is also correct.

The two estimator lemmas correctly derive `estimate ≥ 3/8` from `actual ≥ 1/2` and error at most `1/8`, and `actual ≥ 1/4` from acceptance at `3/8` and the same error. These are numerical prerequisites. They do not yet establish estimator concentration, the necessary-edge true-probability premise, accepted-edge survival, adaptive sampling correctness, or runtime. Likewise the sampling lemma does not yet construct a graph blocking set, prove its cap/non-diagonality, relate survival to pruned graph weight, or prove Lemma 27 in full.

## Remaining boundaries

The inspected files contain no `sorry`, `admit`, custom `axiom`, or unsafe declaration. This textual check is not a transitive kernel axiom audit.

The main lightness and lower-bound theorems, host-tree/forest packing, cycle blocking, pruning, heavy/light decomposition, multigraph extension, rounded real-parameter implementation, concentration, and runtime remain open. The README and statement inventory preserve those distinctions. No foundational result here certifies the unmodified printed randomized algorithms or closes these larger proof obligations.

**Disposition:** suitable to retain as an explicitly partial foundational checkpoint, subject to the separate compilation/kernel/axiom checks. Any change to the four pinned source files requires rechecking the affected conclusions.
