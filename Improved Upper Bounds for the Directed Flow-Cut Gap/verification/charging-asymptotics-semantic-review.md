# Semantic review: self-reduction, charging, and subpolynomial bounds

Date: 2026-10-09. Paper: arXiv:2604.03412v3.

**Verdict:** no mathematical or specification error was found in the three frozen modules below. The self-reduction is a finite conditional rounding theorem; the charging module constructs the corrected finite graph-value witness at a stable state; the analytic module proves genuine uniform subpolynomial bounds. These results do not by themselves establish the paper's complete adaptive rounding algorithm, running time, or headline flow-cut theorem.

## Reviewed versions and verification evidence

Paths below are relative to the project's `DirectedFlowCutGap/` directory.

| Source | SHA-256 | Module-owned declarations audited |
| --- | --- | ---: |
| `WeightSelfReduction.lean` | `d89706238cb0c612ee7c2737be1a0c837ce48ed20c0749287e0719e73013362b` | 96 |
| `SubpolynomialBounds.lean` | `f699434e96940db5e00f10e101bd806696f5d6f698c8f82c69727c8ce7bab086` | 51 |
| `PathSystemCharging.lean` | `bc56f96afb836847e71b4caeab9ac3ff6f694c9adacbdc6537afe27e47025569` | 104 |

The existing `self-reduction-*`, `subpolynomial-*`, and final `charging-*` verification logs were inspected. Each compile log is empty, each all-owned-declaration axiom audit reports success, and each standalone kernel-replay log reports PASS. The audited dependencies use the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The final charging source and its association with the 104-declaration audit and replay were confirmed after freezing. Earlier 90-declaration charging-core evidence is not being substituted for the final check.

This review independently inspected the theorem statements and proof constructions, the relevant counting/median-shortcut/witness/probability interfaces, `WITNESS_REPAIR_PLAN.md`, and the source's Theorem 32 proof in `tex/reductions.tex:627–681`. It did not edit Lean source or rerun compilation or kernel replay. No `sorry`, `admit`, new `axiom`, `unsafe`, or `implemented_by` declaration occurs in the three reviewed sources.

## 1. Finite heavy-vertex self-reduction

`heavy w τ` is the actual set of vertices with weight at least `τ`; the residual graph has the subtype of surviving vertices. Residual weights are doubled and residual costs retain their original values. The proved bounds are:

- residual cardinality at most the original cardinality;
- residual total weight at most `2 n τ`;
- residual weighted objective at most twice the original objective;
- heavy-cut cost at most `weightedCost / τ`, for `τ > 0`.

The last estimate has the correct reciprocal factor. With `τ = 1/(4 n^(c/(1+c)))`, it gives `4 n^(c/(1+c))`, correcting the source's displayed coefficient rather than encoding its typo.

The path transfer is endpoint-safe. An original demanded path need only avoid the heavy set internally; its source or target may be heavy. `Path.trim` constructs the actual residual subpath from the first internal vertex to the last internal vertex, with edge length reduced by two. It includes the length-zero trimmed case and proves that every vertex of the trimmed path is an original internal vertex. No proof step requires the original demand endpoints to survive.

`Path.internal_distance_lower` closes any path between those internal vertices using the two original endpoint edges and applies genuine simple-path composition/loop erasure. It obtains the lower bound `1 - 2τ` without assuming an endpoint-excluding distance is an ordinary metric. For `τ ≤ 1/4`, doubling the residual weights makes the trimmed pair a threshold demand. `combined_isIntegralCut` then transfers an actual residual integral cut to every original threshold demand.

`round_of_bounded_oracle` explicitly assumes a residual rounding oracle over all instances with the stated cardinality and mass bounds, including empty and zero-objective instances. It proves the exact factor `1/τ + 2α`. It does not assume monotonicity of a gap function defined only at exact parameters.

`round_of_power_oracle` treats the exponent as a real number. For `n ≥ 1`, `c ≥ 0`, and a uniform actual graph oracle with factor `K W^c`, it proves the factor `(4+2K) n^(c/(1+c))`. The residual mass estimate, exponent addition/multiplication, denominator positivity, and threshold range are proved. The `c=0` case uses the documented real-power convention `0^0=1`.

**Scope:** the oracle is an explicit substantive hypothesis. The module does not itself produce that oracle or formalize the uniform `W^(c+o(1))`-to-`n^(c/(1+c)+o(1))` passage, nor does it assert an efficient algorithm.

## 2. Uniform subpolynomial estimates

The definition has the required quantifier order:

`∀ ε > 0, ∃ C > 0, ∀ n ≥ 1, |f n| ≤ C n^ε`.

The constant may depend on the chosen exponent and fixed external parameters, but is selected before the input size. No theorem replaces this with a separate size-dependent constant.

`Subpolynomial.of_eventually` genuinely absorbs finite exceptions: after obtaining a threshold `N`, it adds the finite sum of `|f i|` for `i < N` to the eventual constant. Its all-size estimate uses `n^ε ≥ 1` for positive integer sizes. Product closure divides the requested exponent between the factors. Finite sums, finite products, and fixed natural powers follow from these proved closures; they do not assert closure under an unbounded size-dependent number of factors.

The concrete choices are `r(n)=max(2, log(n+2))`, `J(n)=ceil(3 log(n+2)/log(r(n)))`, `B(n)=4^J(n)`, and `H(n)=2+ceil(log(n+2)/log 2)`. The padded logarithm arguments exceed one, and `r(n)≥2` makes `log(r(n))` strictly positive, even at size zero. The asymptotic bounds themselves explicitly concern `n≥1`.

The nontrivial cap estimate is proved from divergence of `log(r(n))`: eventually `3 log 4/log(r(n)) ≤ ε`, hence `B(n) ≤ 4(n+2)^ε`. The shift is bounded uniformly by `3^ε n^ε`, then finite exceptions are absorbed. This establishes subpolynomiality of `B`; the estimates for `r`, `J+1`, and `H+1` are also proved. The module then proves subpolynomiality of their products for every fixed tuple of natural degrees and of the stated logarithmic union-bound factor for every fixed polynomial degree.

The hard-regime result is equally substantive: a half-exponent argument absorbs a fixed multiplicative constant, yielding eventually `64B(n)≤n^ε` for every positive `ε`. `exists_hard_regime_threshold` selects a positive threshold before quantifying over sizes. Its cube-root specialization is valid. The exact geometric restart inequalities are separately proved using positive logarithms and the ceiling bounds.

**Scope:** these are analytic envelopes. They do not supply a graph algorithm, a probability-space coupling, or a running-time analysis. A direct domination of the charging module's `Nat.log2 n` factor by this module's padded `H(n)`, and a named subpolynomial bound for the exact charging denominator or complete expected-cost envelope, are outside this three-module verdict.

## 3. Constructed charging and canonical fan

An occurrence is the pair `(witness index, vertex)` belonging to the original frozen suffix and the selected base list. Distinct indexed witnesses remain distinct even when they have different labels and identical vertex lists. Prefixes and suffixes are never recomputed after deletions.

`charged` filters this original finite occurrence set by existence of an eligible incident shortcut. `assignedEdge` chooses an eligible edge for every charged occurrence; its fallback is used only outside that set. `surviving` is the complement. The exact cardinality partition and `surviving_halted` show that every eligible occurrence is removed once and that no survivor is eligible. Since eligibility depends only on the frozen label, height, shortcut set, and occurrence, this simultaneous construction realizes the maximal outcome of the deletion procedure without assuming such an outcome as data.

For each shortcut and demand label, there are at most two assigned occurrences, one for each endpoint, by per-label witness disjointness. The finite fiber sums consequently prove `edgeCharge ≤ 2 totalValue`. The long case selects a real edge from the actual shortcut set. Positive charged mass first proves that this set is nonempty; there is no division by an unchecked zero size.

The short case is also constructed. The surviving lists retain witness order. Consecutive positive gaps telescope across all intermediate entries. The halted two-hop inequality then gives a survivor count at most `2σ` for real `σ≥1`, avoiding the invalid implication `c>σ ⇒ c−1≥σ`.

Survivor-fiber counting produces many active witnesses. Averaging their actual frozen prefixes produces a shared prefix vertex and a nonempty fan. Each fan member supplies a surviving suffix/base target. The earliest target is chosen by the actual base-list order. Shared-prefix membership proves label injectivity before summing demand contributions.

The candidate pairs consist of the common initial pair and the actual outgoing shortcut pairs through one uniform mediator set, so there are at most `H+1`. The zero-, one-, and two-shortcut cases are all covered. Every candidate used in the averaging argument is proved reachable. Neither the common fan, its targets, a favorable charged edge, nor the desired final pair is a premise of the final construction.

## 4. Exact graph bridge and balanced constant

Heights are clipped in the extended nonnegative reals before conversion to real numbers. Thus an infinite distance has clipped height one, not the zero produced by converting infinity directly. `value_clippedHeight` identifies the real positive-part difference with bounded extended subtraction, and `value_eq_levelSeparationValue_toReal` connects it exactly to the pre-existing frozen level-separation probability.

Witness-carrier reachability proves finiteness of each retained witness distance before the below-one certificate is used. Consequently clipping preserves the certified height gaps. Internal carrier segments give paths in the common fully deleted graph; transitivity uses actual path composition and preserves surviving support. Deleted original demand endpoints are not reintroduced into shortcut paths.

With `λ=256B`, `H=Nat.log2(n)+1`, and `τ=σ/(λ²L)`, the module derives the actual base score at least `Ld/λ`, shortcut count at most `4LH`, and mediator width at most `H`. Its two alternatives give the minimum of

- `σd/(16 λ³ L H)`;
- `L²d/(256 λ³ σ n(H+1))`.

From `L≤n≤L³`, the real choice `σ=L sqrt(L/n)` is proved to lie in `[1,L]` and to satisfy `σ²n=L³`. The two bounds therefore imply `d sqrt(L/n)/(256 λ³(H+1))`. The witness count and incidence bounds supply `d≥M L/(8Br λn)`. The resulting denominator is exactly

`K = 2048 B r (256B)^4 (Nat.log2(n)+2)`.

`exists_stable_graph_value` constructs the witness system through `WitnessSystem.exists_system_of_stable`, derives all spacing and common-residual reachability inputs, and proves

`∃ u v, LevelResidualPath G X u v ∧ M (L/n)^(3/2)/K ≤ Σp (levelSeparationValue G (w p) (demand p).1 u v).toReal`.

The mass `M` and labels are those of the current state. No epoch-start mass is silently substituted. The logarithm here is Lean's natural-number `Nat.log2`; the bound is stated with that exact function.

## 5. Assumptions and remaining assembly

The final graph theorem explicitly requires finite vertex and demand-label types, a nonempty vertex type, `B≥1`, `L≥64B`, `r>1`, `L≤n≤L³`, positive current outside mass, original-graph fractional feasibility, the outside cap, candidate-objective dominance, and the stable mass comparison. Candidate-objective dominance is the sufficient optimality/lower-bound certificate stated in `hopt`; this theorem does not itself select or run an optimizer. Positive mass proves the constructed witness index type is nonempty.

These premises contain no requested witness family or favorable pair. The theorem supplies both. The remaining work is to connect such stable states to the actual adaptive random process, prove the applicable epoch and stopping/coupling invariants, account for other parameter regimes and finite graph exceptions, assemble the uniform rounding bound, and establish any claimed algorithmic running time and downstream reductions. This report does not evaluate later adapter or adaptive-assembly modules.

The explicit endpoint convention, quarter-rounding losses, real-parameter survivor correction, frozen probabilities, and current-state mass all align with the repaired argument in `WITNESS_REPAIR_PLAN.md`. The verified finite constant is conservative but sufficient for that repaired interface.
