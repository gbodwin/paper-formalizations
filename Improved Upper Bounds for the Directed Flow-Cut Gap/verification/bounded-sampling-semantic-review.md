# Semantic review: cardinality-bounded finite sampling

Reviewed 9 October 2026, 05:10–05:12 UTC. **No mathematical or quantifier defect found in the inspected source.** The explicit horizon follows from the original all-cost oracle using finite penalties; the stronger avoidance oracle is derived rather than assumed. The matching frozen source has now passed strict compilation, its six-owned-declaration recursive axiom audit, and its isolated official kernel replay; the receipts were independently inspected at 05:12 UTC. No Lean source was edited and no compiler was run by the reviewer.

## Exact inspected source and scope

`repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/BoundedSampling.lean`

SHA-256: `1789301044290140f0193db7b9d35e6d9a0d0dab604aee5146b7e110b8872b5f`.

The complete source and its exact imported `exists_mw_family_of_min_weight` theorem were read. The latter constructs its family by the actual multiplicative-weights recurrence from a cost oracle, with a common update scale, rather than taking good family members or their desired marginal bounds as hypotheses. The output here is a finite sequence indexed by `Fin T`, hence repeated cuts are allowed and the denominator counts the full sequence. It is a finite existence theorem, not an implementation/runtime theorem.

## Finite penalty and the zero-potential case

For a set `S` with `α Σ_S w≤1/4`, put `C=Σ_{e∉S} c_e w_e`. When `C>0`, the proof replaces costs on `S` by `K=4αC`; its original-oracle fractional budget is at most `αC+K/4=2αC<K`. Consequently no returned set can contain a member of `S`, whose cost alone would be `K`. Once avoidance is established, the modified and original selected costs coincide and satisfy the factor-two estimate.

When `C=0`, the proof uses the finite positive penalty `K=1`. The budget is at most `1/4<K`, so avoidance still follows. This estimate alone would not show zero original selected cost; the source correctly uses its explicit assumption that all weights outside `S` are strictly positive. Every nonnegative term `c_e w_e` outside `S` is zero, forcing `c_e=0` on every selected element. Thus the zero-budget branch is genuine and requires no limiting argument or unbounded/infinite cost.

The assumptions are sufficient for arbitrary predicates `P` and any finite item universe. No special graph property is smuggled into the penalty theorem, and no existence of an avoiding admissible cut is separately assumed.

## Explicit horizon and actual original marginals

The main theorem assumes `m=card(E)>0`, `α>0`, and all `w_e≥0`. It chooses

`δ=1/(4αm)`, `S={e | w_e≤δ}`, `w′_e=max(δ,w_e)`.

The finite cardinality bound gives `α Σ_S w≤1/4`, and weights outside `S` exceed `δ>0`. Hence the penalty lemma supplies a cost oracle for the unchanged admissibility predicate together with avoidance of `S`. Raising weights to `w′` is used solely to majorize the potential of this derived oracle; the actual feasible-cut condition still refers to the original input.

The derived oracle factor is `2α`. The common recurrence scale is `η=1/(2m)=δ(2α)`, which satisfies the imported minimum-weight update condition. Its potential ratio obeys

`Σw′/δ ≤ (W+mδ)/δ = 4αmW+m`.

The positive integer horizon is exactly

`T=ceil₊(2m log(4αmW+m))+1`.

The logarithm argument is positive since `m>0`, and in fact is at least one. The ceiling inequality proves `log(Σw′/δ)≤ηT`; the extra one makes `T>0`, including `m=1,W=0`. The old recurrence then gives marginal at most `4w′(2α)`. For elements in `S`, all membership counts are exactly zero. For elements outside `S`, `w′=w`, yielding the claimed original-weight marginal `8αw_e`. There is no dependence on the minimum positive input weight.

The statement handles zero weights and even total mass zero when `m>0`. It does not handle an empty item type or `α=0`; those are excluded explicitly rather than hidden behind a division convention. A separate existing finite-family theorem is needed if a caller wants those regimes.

## Graph specialization and source correspondence

`exists_vertex_family` obtains the real cost oracle from `HasVertexRoundingFactor` and keeps `IsIntegralCut G X (thresholdDemands G w)` for every returned set. Both the actual graph and original threshold weights are unchanged. Thus uniform sampling from this positive-length family gives the counted marginals and a valid cut on every outcome. No flow-cut factor or main asymptotic estimate is newly postulated beyond the explicitly supplied all-cost factor interface.

This addresses the finite sampling construction in arXiv:2604.03412v3, `tex/reductions.tex:683–739`, using a repaired common-scale/finite-penalty argument. It is not a literal verification of the source's raw update-rate estimate or its informal large-cost step. The displayed horizon is linear in the number of items outside its logarithm. For vertex cuts that number is `n`; an edge instantiation must state whether the items are actual edges or all ordered pairs. Neither interpretation automatically establishes the paper's linear-in-vertices edge-family bound. No such edge bound or polynomial-time oracle implementation is asserted by this module.

## Independently inspected local verification

The current source hash was rechecked after the individual gates and remains exactly as above. Both `bounded-sampling-compile.log` and fresh `seventh-BoundedSampling-compile.log` are empty. `verify-seventh.sh` explicitly recompiles this source with `-j1 -DautoImplicit=false -DwarningAsError=true` before its individual audit and replay.

The audit driver enumerates all declarations owned by this module, fails on an empty enumeration, and recursively permits only `propext`, `Classical.choice`, and `Quot.sound`. Its log enumerates all six declarations, including the three mathematical theorems, and reports success. Audit log SHA-256: `d34d1402af50cf417ccaeb7827432e41688854dd1423aacef268dc30a44bbce1`.

The replay driver invokes official `LeanChecker.replayFromImports` on `DirectedFlowCutGap.BoundedSampling`, then prints its target-specific PASS, which is present. Replay log SHA-256: `87ef2416af7714cf4e59a7261c4680d0981eee94042eb354350735b3a3fd5a08`. This checks the target declarations with their imported dependency environment, not an independent verifier or a fresh rebuild of every dependency within that isolated call.

The larger seventh aggregate checkpoint subsequently completed successfully; its exact coverage and source-manifest reconciliation are recorded in `seventh-independent-verification-review.md`. This assessment says nothing about a remote Git commit, publication, or CI run.

## Seventh-checkpoint cross-check

At 05:14–05:15 UTC, the reviewer independently reconciled all 42 source hashes, all 41 component imports plus root, all 42 unique official kernel-replay PASS targets, and the 2,574-declaration recursive allowed-axiom audit. All sources reviewed here are included and unchanged. See `seventh-independent-verification-review.md` for exact evidence hashes, fresh-build scope, and local-versus-remote limitations.
