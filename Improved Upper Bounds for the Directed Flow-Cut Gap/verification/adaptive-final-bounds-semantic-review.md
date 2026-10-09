# Semantic review: all-regime adaptive and vertex bounds

Drafts reviewed 9 October 2026, 04:58–05:00 UTC; frozen compiled sources reconciled 05:09 UTC, against arXiv:2604.03412v3 and the previously reviewed actual graph/cut/probability components.

**No mathematical or quantifier defect found in the three inspected final sources.** Their local strict compile logs are empty, all-owned-declaration axiom audits pass, and their isolated official LeanChecker replays pass. The argument discharges the former hard-regime parameter assumptions, covers every unweighted threshold at least one, constructs a normalized high-probability law, and composes the repaired reductions to both all-cost vertex rounding estimates. This remains a semantic and local verification assessment, not a runtime, whole-paper, or remote-publication certification. No Lean source was edited and no compiler was run by the reviewer.

## Exact reviewed final sources

Paths are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`. Current bytes independently hashed and compared against saved reviewed drafts at 05:08–05:09 UTC:

| File | Final SHA-256 | Owned declarations audited |
| --- | --- | ---: |
| `AdaptiveHighProbability.lean` | `b08155145f5ab38eb57babc0e32d052642a635099a1dde18d8247a408f3b62c9` | 24 |
| `AdaptiveAsymptotic.lean` | `eba3d6a189f8ee42a5b397d43090563f9e764e733c0808ab096df54679656afe` | 18 |
| `AdaptiveVertexBound.lean` | `379c29e78caa1ad57b8773fb4dec0763b1b8a7b21fcb16eb25e061f9b8edfbd4` | 23 |

The corresponding reviewed draft hashes were `f6162cf0fa12b70ee750a23e52200d7b921ab81c2932ccf5f4e6cb10d68ba0bc`, `fce24861a8fdcd3d64b1f1b7406f471cf85f7085679b024cf39e62703c5b7beb`, and `72721ad5fb12bddc7b58e5a0baff67dcae39f8aada23db77193ea4cd22739456`. The vertex module's separately reviewed addition of `vertex_weight_rounding_uniform` preceded that last draft hash. All final changes are semantic-preserving elaboration/proof repairs, omitted unused decidable-equality assumptions, a coercion lemma for the same restart factor, and a local classical decidability instance. No substantive theorem conclusion or construction changed.

The full sources and exact imported interfaces from `CandidateSchedule`, `UniformWeightReduction`, `UnitCostReduction`, and `WeightSelfReduction` were inspected. Existing semantic reports cover the underlying adaptive law, unconditional cost induction, probability construction, and graph reductions. No source-level `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide` occurs in these sources; local build and recursive axiom evidence are recorded separately below.

## Actual hard-regime law and confidence normalization

`AdaptiveHighProbability.roundingLaw` starts from the actual uniform initial state: original unweighted threshold demands, empty selected set, weight `1/L` for every label/vertex, and scale one. Its restart factor is the previously proved `r(n)>1`; its fuel is `J(n)+1`. Initial mass is at most `n³`, strictly below `r(n)^(J(n)+1)`, so the existing geometric-fuel validity theorem applies to every supported output.

The confidence height is exactly `log((J(n)+1)(n+2)^3)`. Its logarithm argument is positive even at zero; exponentiation gives the reciprocal of that argument. The source explicitly proves `n³ exp(-H)≤1`, discharging the failure-cost condition from AdaptiveCost. It uses confidence exponent three, not an arbitrary natural exponent for which this implication could fail.

The expected bound is an application of the actual bounded output theorem with initial scale one, cap `4^J=B(n)`, zero initial cut, and the correct geometric fuel. It retains `64B(n)≤L≤n≤L³`. Its prefactor is precisely `expectedCostEnvelope 3 n`, multiplied by `(n/L)^(3/2)`. No desired expected-cost estimate is introduced as a fresh premise.

Amplification invokes the genuine product PMF and minimum-sample selector previously reviewed. Under these domain conditions `n≥1` and the expected-cost budget is strictly positive. Nonnegative cardinality costs therefore give failure at threshold twice the expected envelope at most `n^(-κ)` with `max(1,ceil(κ log n/log 2))` trials. Every supported outcome remains a valid cut. There is no normalization loss or claim that only successful-size outputs are valid.

## All regimes, including empty graphs and large thresholds

`allRegimeLaw` is a concrete three-way law: adaptive output when `L≤n`, `64B(n)≤L`, and `n≤L³`; the deterministic full vertex set when `L≤n` but a hard test fails; and the deterministic empty set when `L>n`.

For `L≥1`, every demanded reachable path has an internal vertex, so the full set is a genuine internal-vertex cut. It does not rely on selecting an endpoint. For `L>n`, any actual path would have at most `n` internal vertices, contradicting its threshold requirement, so all demands are unreachable and the empty set is valid. This also handles the empty vertex type directly. No conversion of infinite distance to a zero real number is used.

The numerical easy case is correct: if `L³≤n` and `L>0`, then `n≤(n/L)^(3/2)`. For sizes beyond the single global threshold where `64B(n)≤n^(1/3)`, failure of either hard test forces `L³≤n`. For smaller positive sizes, `n<n₀` is absorbed by the prefactor `max(C,n₀)`, while `n^ε≥1` and `(n/L)^(3/2)≥1` in the full-set branch. Thus no size-dependent hidden constant is introduced. At `n=0`, the law is empty and the expected inequality is zero on both sides for positive ε.

The final expectation quantifiers are `∀ ε>0, ∃ C>0, ∀ finite vertex types, graphs, L≥1`. The single constant is chosen before size and threshold. A finite normalized expectation yields an actual supported outcome below the bound, using a positive-mass atom and a strict finite-sum contradiction. This is not a favorable-outcome assumption.

The all-regime high-probability theorem likewise selects one positive constant before the vertex type, graph, threshold, and confidence exponent `κ≥0`. The probability assertion explicitly assumes `n≥1`, while validity and expectation also cover `n=0`. For `L>n` the positive comparison budget is harmless because actual cost is zero. For `n=1` the requested `n^(-κ)=1` tail bound is correctly allowed to be trivial. The factor two from Markov/amplification is incorporated once into the final constant.

## Uniform weights and both bounded reductions

For a positive uniform weight `a≤1`, the graph-facing threshold is exactly `L=1/a≥1`. Actual path weight is `a` times its internal-vertex count, so every weighted threshold demand is an unweighted threshold demand at this `L`, including vacuous unreachable demands. The target scale becomes `(na)^(3/2)=W^(3/2)`. For `a=0`, the zero-objective cut theorem with unit costs yields cardinality zero; the argument does not divide by `a`. Empty graphs are included.

Consequently the source obtains `UniformCoreEstimate δ C` from the proved-law route with `C` selected before every finite instance. Intermediate bounded-oracle lemmas state this core estimate as a premise, but `exists_uniform_core` supplies it in the final theorem. No favorable cut, graph-value oracle, or final rounding conclusion remains assumed there.

The bounded uniform oracle factors `W^(3/2)=sqrt(W)*W`, including `W=0`, and uses monotonicity under actual upper bounds on vertex count and mass. Uniformization uses the existing repaired `6N` vertex, `2B` mass bounds and output loss two. Cost replication uses `4n²` vertices, `3W` mass and loss six. Substituting these exact bounds gives

`6 * [2C*(6*(4n²))^δ*sqrt(2*(3W))] = A(δ,C)*n^(2δ)*sqrt(W)`,

where `A(δ,C)=12C*24^δ*sqrt(6)`.

This agrees with `costConstant`; none of the size or mass blowups is omitted. The constant depends only on δ and the core constant. It does not depend on graph size, weights, or costs. The bounded residual oracle then enlarges only numerical bounds using nonnegative-exponent monotonicity; it does not assume monotonicity of a gap defined at exact parameter values. The imported reductions include arbitrary nonnegative weights/costs, zero objectives, and empty instances.

## Self-reduction and final quantifiers

The actual self-reduction uses `τ=1/(4n^(1/3))`, for positive integer `n`. Its imported finite theorem provides factor `1/τ+2α` on the original fractional objective and an actual residual graph with at most `n` vertices and total weight at most `2nτ`. The source retains the reciprocal factor four from the corrected heavy-cut estimate.

Here `2nτ=(1/2)n^(2/3)≤n^(2/3)`, so its square root is at most `n^(1/3)`. The residual oracle therefore has factor at most `A(δ,C)n^(2δ)n^(1/3)`, while the heavy term is `4n^(1/3)`. Since `n^(2δ)≥1` for `δ≥0`, their sum is at most

`(4+2A(δ,C))*n^(1/3+2δ)`.

The final theorem chooses `δ=ε/2` before obtaining the core constant and before any instance is quantified. Hence its claimed exponent `1/3+ε` and constant `K=4+2A(ε/2,C)` have the correct uniform order: `∀ ε>0, ∃ K>0, ∀ finite graphs and finite nonnegative w,c, ∃ valid X` with the stated objective bound. The empty vertex type is handled separately by the empty cut, avoiding positivity arguments at zero. The `HasVertexRoundingFactor` specialization retains a single constant for all cost vectors.

The added `vertex_weight_rounding_uniform` also packages the mass-sensitive estimate with one constant chosen before all instances: factor `K n^ε sqrt(W)`, obtained by the same `δ=ε/2` substitution into `arbitrary_cost_round`. Its constant is positive, independent of `n,w,c`, and zero-mass/empty cases remain included.

This corresponds to the unweighted core and uniform-weight conversion in `tex/body.tex:50–73`, the repaired weight/cost reductions, and the self-reduction in `tex/reductions.tex:627–681`. The compiled modules establish both mathematical all-cost **vertex** rounding estimates and an all-regime unweighted high-probability law. They do not by themselves establish an executable polynomial-time implementation, edge rounding, or a separate LP-duality identification with maximum directed multiflow.

## Independently inspected local verification evidence

The three `adaptive-{high-probability,asymptotic,vertex-bound}-compile.log` files are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Their audit drivers enumerate every declaration owned by the target module, fail if none are seen, recursively call `Lean.collectAxioms`, and reject anything beyond `propext`, `Classical.choice`, and `Quot.sound`. The resulting logs report 24, 18, and 23 declarations respectively, including generated declarations and both final vertex estimates.

| Component | Axiom audit log SHA-256 | Kernel replay log SHA-256 |
| --- | --- | --- |
| HighProbability | `c6002077358e5a700fd7d3212683646b606cfa70c983997a223111f4df2d2c7f` | `3cae11b7977c631c299a79143c96e2ec5aaf2523751db7a4a3935fa785e79ff2` |
| Asymptotic | `ad9b0fc3de9335bd89de161341f68ea03f771de779cf9d65a544681f9ea22dc9` | `5c3806dd8fe0d52f382a2f4e6834f0333471ea8248b86df1e450c2adb4f4caf4` |
| VertexBound | `c6a22bf594ef96af84e4918ad39f76333fb76ea66930e1176b8706d5d03f4db5` | `5669ebac04f48a925941a16bb9acf51758542cfca19514856881e5f6a222f2a0` |

Every replay driver imports official `LeanChecker`, invokes `replayFromImports` on its own target module, and prints its target-specific PASS afterward; all three logs contain that PASS. This replays the target's kernel declarations with its imported dependency environment. It is not an independent proof checker or a claim that every dependency was freshly recompiled in that isolated run.

These components were absent from the earlier sixth-checkpoint 35-source manifest; that checkpoint was not reused as evidence for them. The present findings are tied to the final source hashes and their own local checks. A later aggregate checkpoint should bind the full current dependency closure and root imports. Nothing in this report asserts a Git commit, remote push, or remote CI result.

## Seventh-checkpoint cross-check

At 05:14–05:15 UTC, the reviewer independently reconciled all 42 source hashes, all 41 component imports plus root, all 42 unique official kernel-replay PASS targets, and the 2,574-declaration recursive allowed-axiom audit. All sources reviewed here are included and unchanged. See `seventh-independent-verification-review.md` for exact evidence hashes, fresh-build scope, and local-versus-remote limitations.
