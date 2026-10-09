# Directed flow-cut gap: reduction component semantic review

Reviewed 9 October 2026 against Bodwin–Samborska, arXiv:2604.03412v3. This is an independent source-level mathematical review of the exact snapshots identified below. No Lean files were edited and no compiler or kernel commands were run by this reviewer.

**Result:** No semantic mismatch, concealed conclusion, or omitted positivity assumption was found in `VertexRounding.lean`, `ShortcutContraction.lean`, `CandidateOptimization.lean`, `LevelCut.lean`, `FiniteSurvival.lean`, or `EpochAccounting.lean`. They prove genuine graph and finite analytic components and support a partial checkpoint. They do not establish the complete unit-cost reduction, the paper's efficient sampling claims, or its main flow-cut bounds.

## Vertex rounding and sampling

- `HasVertexRoundingFactor` explicitly requires, for every finite nonnegative vertex-cost vector, an actual integral cut of the original graph's threshold demands with the stated weighted-cost bound. It does not hide the graph theorem inside a newly named unconditional axiom. The conversion to real costs retains the same objective and graph admissibility predicate.
- `exists_finite_vertex_weak_decomposition` and its zero-avoiding version derive a nonempty finite indexed family whose every member hits every internal-vertex path for every original distance-at-least-one demand. The quotient of membership counts by the positive horizon is exactly the uniform inclusion marginal, bounded by `4 * α * w(v)`. Repeated members are permitted, as appropriate for the paper's multiset.
- The imported zero-weight penalty argument derives avoidance from the original cost oracle; zero-weight avoidance is not an additional premise. The scaled multiplicative-weights update uses its logarithm estimate in the proved valid range. Zero weights, an all-zero vector, an empty vertex type, and `α = 0` are covered. The zero-factor characterization correctly says that the empty cut is admissible.
- `vertexCardThresholdCut = {v | 1 ≤ |V| * w(v)}` is a direct deterministic graph construction. Every path of weight at least one meets it internally, by summing the strict opposite inequalities over its actual internal vertex set. Its cost is at most `|V|` times the fractional objective for every nonnegative cost vector. Thus the factor domain is demonstrably nonempty; it is not merely an oracle schema.
- `vertexDistance_lt_one_of_avoiding_threshold_cut` supplies the weak-diameter interpretation: any path avoiding a family member internally has original endpoint distance below one. This respects the paper's endpoint-excluding convention and handles disconnected demands without inventing paths.

These results give a valid existence-level vertex component of Theorem 33 (`reductions.tex`, lines 683–773). They repair the printed estimate at lines 748–749, where `log(1 + 1/x) = Θ(1/x)` is used in the wrong range. The reviewed result makes no claim of a polynomial-time oracle/sampler, an `Õ(n)` family size, the edge version, or the headline approximation factor.

## Shortcut contraction and permanent endpoints

- The transformed vertex type is literally the complement of the finite removed set. Each shortcut edge has a positive-length original simple-path witness with every interior vertex removed. This defines a genuine shortcut closure, rather than postulating path or cut transfer. Positive simple paths cannot close up, so the closure has no self-loops.
- `expand_walk` concatenates actual edge witnesses. `compress_walk` constructs actual shortcut walks and drops closed excursions when their surviving endpoints coincide. In both path theorems, the imported proved loop erasure preserves endpoints and support containment. Neither projected simplicity nor an assumed replacement path is used.
- `expand_path_weight_le` proves an original simple path of weight at most the shortcut path weight plus the total removed-set mass. Loop erasure is essential: the final simple path charges each removed vertex at most once, even if concatenated witnesses revisit it. Nonnegative weights and the disjointness of removed and surviving vertices justify the sum comparison.
- The exact removed-mass bound gives distance at least one half when the original distance is at least one and the removed mass is at most one half. Doubling surviving weights restores fractional feasibility. The cutoff lemmas derive the mass bound from `w(v) ≤ 1/(2|V|)`, including the empty-graph case. No reachability, positive-weight, or finite-distance premise is hidden.
- `cutsPair_iff` and `cutsPair_disjoint_iff` give exact cut feasibility for surviving endpoints, and `cutCost_pullback` gives exact cost. The family-level general theorem explicitly requires every original demand endpoint to survive. It therefore does not silently drop demands with removed endpoints.
- The port corollaries remove only cores. Every original source/sink representative remains in the survivor subtype, even when its original core is removed. The previously proved exact port-distance identity transfers every original demand; compression and core pullback produce an original integral cut. Zero port costs give exact final cost equality. The port construction's direct self edge also preserves the original zero-length path convention.

These results repair the contraction/endpoint step used by Theorem 29 (`reductions.tex`, lines 209–237). The file defines and proves the semantic shortcut closure; it does not yet implement or prove equivalence to the paper's sequential neighbor-update procedure. Weight clipping, cost rescaling and rounding, parallel-copy replication, the complete size/objective analysis, and the full theorem remain separate obligations. Those are scope limits, not defects in the proved component statements.

## Attained candidate optimization

`CandidateOptimization.lean` formalizes the candidate problem in Algorithm 2 (`body.tex`, lines 287–301), with the outside-cut mass defined at lines 324–327.

- The feasible set consists of actual fractional cuts for the stated demand family, with weight exactly one on `X` and weight at most `cap` outside `X`. The objective is precisely the sum outside `X`, with no implicit endpoint deletion.
- Given a feasible starting vector satisfying the outside cap, `installCut_fractional` sets coordinates in `X` to one and derives feasibility path by path. If a path meets `X` internally, that one coordinate suffices; otherwise its internal weight is unchanged. This remains correct when setting a coordinate to one decreases its old weight.
- Closed all-path constraints and coordinate bounds place the candidate set in a compact box. Nonemptiness is proved by `installCut`, and continuity of the outside sum gives an attained minimum. `exists_minimum` proves global minimality and a bound by the starting vector's outside mass; it does not assume an optimizer or the desired objective inequality.
- `one_le_outsideMass_of_uncut` extracts an actual path avoiding `X` internally. Its fractional weight is at least one and its internal support consists of vertices outside `X`, proving the lower bound used at `body.tex`, lines 383–385. Demand endpoints may themselves belong to `X`.

This is an existence and objective component. The feasible capped starting vector is an explicit hypothesis; algorithmic invariants providing it in every round, joint epoch analysis, and LP implementation/runtime remain separate.

## Deterministic level-cut geometry

`LevelCut.lean` gives the actual finite vertex set defined by the closed interval in Algorithm 2 (`body.tex`, lines 306–310), proves Lemma 11 (`body.tex`, lines 333–349), and supplies the single-round geometric step of Lemma 12 (lines 352–362).

- `exists_adjacent_break` proves a true-to-false predicate crossing across an actual adjacent pair of path indices. The two distance-crossing variants do not assume distances are monotone along a directed path. The local distance bound correctly charges the edge tail's weight under the endpoint-excluding convention.
- The Lemma 11 conclusion is exactly “the starting vertex is selected, or every path is cut internally.” A crossing tail is always distinct from the target; if the starting vertex is not selected, it is distinct from that endpoint as well. The accumulated-cut corollary uses ordinary cut monotonicity.
- For a selected feasible source demand, every level in the closed interval `[0,1]` cuts the demand internally. Positive levels use the crossing with equality permitted at the upper endpoint, covering `d = 1`. The separate zero-level proof uses a zero-to-positive crossing. In either proof a crossing tail equal to the source would give its successor distance zero via a direct edge, contradicting the crossing. Thus selecting a demand endpoint is never counted as cutting its own path.
- Extended distances are retained throughout: unreachable vertices cannot be selected at a finite level, and unreachable demands satisfy the cut conclusion vacuously. Zero weights and length-zero/direct-edge feasibility exclusions are handled explicitly.
- For finite distances, the selection event on `[0,1]` is proved to be the correctly clipped closed interval. Its nonnegative truncated endpoint difference is at most the vertex weight, and the infinite-distance case is assigned zero. No probability, measurability, or expectation claim is disguised as this deterministic length bound.

The full algorithm's iteration/termination and weight-update invariants, the uniform sampling measure, and the probabilistic cut-size analysis remain separate obligations.

## Finite sampling without replacement

`FiniteSurvival.lean` proves the finite inequalities used in Lemma 16 (`body.tex`, lines 470–477), while explicitly separating the stopped-process sampling law.

- The elementary symmetric-sum bound is proved, not assumed: two entries on opposite sides of the mean are replaced by the mean and their remaining sum. The entries stay nonnegative, their sum is unchanged, and their product increases; expansion of the elementary symmetric sum then permits induction on the number of remaining entries. Repeated numerical entries are retained as a multiset.
- `subsetAverage` is identified exactly with division by the number of fixed-size subsets. The normalized Maclaurin and exponential bounds assume a nonempty finite population and `k ≤ |s|`, proving the needed denominators positive. They include `k = 0`. Numerical entries need only be nonnegative; the exponential becomes a survival-decay estimate in the intended range `0 ≤ a(e) ≤ 1`.
- The dominated-average and stopped-event wrappers retain an explicit per-subset product-domination hypothesis. The event expression includes the joint indicator of reaching the round and surviving. It neither conditions on reaching the round nor asserts that such conditioning leaves a uniform subset. Arbitrary real weights are allowed in the wrapper, so it is an arithmetic inequality, not by itself a normalized probability model.

The paper's conditional-uniformity assertion at line 470 is not adopted. Connecting a pre-sampled permutation and independent levels to the actual stopped graph process, establishing product domination, and deriving the full high-probability/union-bound claim remain separate obligations.

## Epoch mass accounting

`EpochAccounting.lean` formalizes the mass expression in `body.tex`, lines 324–327, and the geometric accounting behind lines 379–392.

- `familyMass` sums actual outside-cut mass over a finite set of demand-pair labels. Different labels with equal weight functions each contribute; repeated copies of the same pair are not represented by this finite set. For frozen weights, shrinking the demand set and enlarging the selected cut can only decrease mass. The uniform initial-mass identity is exact.
- `geometric_mass_bound` proves `r^k * M(k) ≤ M(0)` by induction from every explicit step inequality `r * M(i+1) ≤ M(i)`. It does not assume current mass equals its value at the beginning of an epoch.
- `restart_power_le` combines that derived inequality with explicit unresolved mass `M(k) ≥ 1` and initial bound `M(0) ≤ A`. The logarithmic bound requires `r > 1`, so its denominator is positive. The power inequality also forces `A > 0`; no extra unproved logarithm-domain assumption is used. The case `k = 0` is included.

These are deterministic accounting lemmas, not a constructed epoch schedule or a proof that the algorithm supplies every shrink and terminal-mass premise. The power lemma alone permits `r ≤ 1`; a finite restart-count interpretation needs the `r > 1` condition exposed by the logarithmic theorem.

## Verification boundary and source fingerprints

The existing logs report successful compilation, axiom auditing and kernel replay for the first five modules. The axiom logs list only `propext`, `Classical.choice`, and `Quot.sound` for the sampled public theorems and report whole-module audits of 24, 39, 18, 30, and 29 declarations, respectively. `EpochAccounting` compiled without warnings; its aggregate axiom audit and kernel replay were still running when this report was finalized. Final aggregate results are a separate publication gate. This source review does not substitute for rerunning those checks if any source changes.

Checkpoint documentation should be updated to reflect these precise components while retaining the unfinished obligations. In particular, descriptions that still list low-weight contraction as entirely pending predate `ShortcutContraction`; static port and contraction results should not be conflated with the complete unit-cost theorem.

All hashes are SHA-256. Lean paths are relative to `Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/` in the repository.

| Source | SHA-256 |
| --- | --- |
| `VertexRounding.lean` | `94cc950f8e963599eb4e1c2ab443c643e976e4ba39dc0872da57cad58ae15662` |
| `ShortcutContraction.lean` | `414e3734bfeba918b89f1edf1673678b9bc7acada4cdfb4bdd246de42facc5db` |
| `CandidateOptimization.lean` | `0a39d1eecb5e2b875466e66ca408f41889debe67e167b704c9d4d249f82bc31a` |
| `LevelCut.lean` | `547a6b4ab2ef81294bb07ef4fe3965bd21131c353814494e20e443946561acd6` |
| `FiniteSurvival.lean` | `3570b1e17b46537badd766bbf777bc38d87065f8eb9e545a33046170bc80e5d3` |
| `EpochAccounting.lean` | `d698916d0cf6495589c73ddcf5a507957d240dcbe85b11cedbaf8afa086cd4a2` |
| `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| `PathExtraction.lean` | `abc2c7bcda89b3b7ee2d37dd254f4357724585ebc9963697304917899473c63e` |
| `TerminalPorts.lean` | `22bbef774144a67c6d8b631dd8ec5490846d46a7d5a530c18227df5d43bf5b88` |
| `ZeroWeights.lean` | `5f22048c0583355d9400c4d314a5a4e2bc92a74acbd39ed65e68898be3fd06a4` |
| `MultiplicativeWeights.lean` | `f5d00d7d54b6bd141550cfcb1fd40c3db79b6a25a84ad4951c460521f2cee3f4` |
| Pinned paper `tex/reductions.tex` | `d848044d8d074305eefde28f5080dc0c5b2622224edde16952407e12ac46fe4a` |
| Pinned paper `tex/body.tex` | `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325` |
| Pinned paper `tex/intro.tex` | `9619d3bab7a12edf3cc329880207681a3ad3084bef81e58ca3c7bb1c86bcc790` |
