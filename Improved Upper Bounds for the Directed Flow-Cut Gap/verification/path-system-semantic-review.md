# Path-system counting and median shortcuts: semantic review

Reviewed 9 October 2026 against Bodwin–Samborska, arXiv:2604.03412v3, `body.tex` Lemmas 19–20 and the endpoint-aware witness repair plan.

**Result:** No mathematical mismatch, concealed averaging/shortcut witness, or missing boundary hypothesis was found in the two reviewed modules. They prove the stated finite counting and abstract reachability components. One minor mediator comment needs correction; downstream assembly remains a separate scope item.

This was an independent source review. No Lean source was edited and no compiler was run. The supplied verification logs report all-declaration axiom audits for 59 counting declarations and 106 median declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`, and successful LeanChecker replay for both modules. Strict compilation was reported by the coordinating verification task. These checks are distinct from this semantic review.

## Mathematical findings

1. **Indexed multiplicity is preserved.** `degree` sums membership indicators over the family index type, and `baseScore` sums the actual original suffix degrees along one indexed list. Equal lists at different indices are counted separately. `weighted_double_count` correctly counts membership once within each list; conversion to list length explicitly requires `Nodup`. Thus `averageDegree = totalIncidence / card V` is the degree average under exactly the hypotheses used by the base-path theorems.

2. **Quarter floors and constants are explicit.** Prefixes and suffixes are actual `take`/`drop` sublists, both of length `q / 4`. For `q ≥ 8`, the proved inequality is `q ≤ 8 floor(q/4)`. Prefix/suffix index separation is proved with natural-number rounding included. Writing `T` for total incidence, `A` for suffix incidence, `n = card V`, and `b_i` for base scores, the proof establishes `T ≤ 8A`, `A² ≤ n Σ_v suffixDegree(v)²`, and `Σ_v suffixDegree(v)² ≤ Σ_i b_i`. Consequently `T² ≤ 64n Σ_i b_i`. A maximum of the actual finite family supplies the base index; no averaging conclusion is an input. The real form gives `b_i ≥ ell · averageDegree / 64`, and `ell = L/(4B)`, with `B > 0`, yields precisely `Ld/(256B)`. This implements the already documented constant repair rather than asserting the printed coefficient-one estimate at fixed λ.

3. **Congestion and two-charge multiplicity have the right objects.** `LabelDisjoint` constrains distinct indices with the same label, permitting equal lists across different labels. It proves label injectivity among witnesses sharing a vertex, global degree at most the label count, and at most one witness per label at either endpoint. `endpoint_charge_card_le_two` then injects concrete events into `{x,y}` using their actual witness and endpoint maps. Its explicit `honce` premise says an indexed vertex occurrence is charged at most once; together with endpoint membership and fixed label this genuinely proves the bound two. The result remains conservative when `x = y` (in that case the proof actually bounds the event count by one).

4. **The shortcut tree and bounds are constructed.** `Tree.exists_balanced` splits the input at index `length / 2`, excludes the pivot from both children, and proves exact inorder reconstruction, recursive balance, and height at most the supplied depth. With `d = Nat.log2 length + 1`, the needed `length < 2^d` is proved, including length zero. `star` filters the two actual finite stars for reachability and unequal endpoints; `edges` takes their recursive union. Validity and cardinality are proved from these definitions. The resulting bounds are exactly `|S| ≤ 2 length (Nat.log2 length + 1)` and `|M_x| ≤ Nat.log2 length + 1`, without an assumed recurrence or logarithmic oracle.

5. **Backward reachability and short paths are real.** `Tree.twoHop` handles both same-child cases, pivot endpoints, equal endpoints, and both crossing orders. In the backward crossing case, `R x y` is composed with the forward relations `R y m` and `R m x` to obtain both selected edges. No antisymmetry or global reflexivity is used. A fixed `M_x` works for every reachable target. `TwoHop.exists_path` explicitly constructs `[x]`, `[x,y]`, or `[x,m,y]`, proves distinct vertices and actual consecutive edges, and bounds the edge count by two. `Tree.mediate_two_step` derives endpoint membership and reachability from the given shortcut edges, then supplies an allowed mediator when zero and one edges are excluded; its hypotheses faithfully express the source's exact-distance-two case.

6. **Empty and small domains are covered honestly.** Aggregate counting identities hold for empty index or vertex types. Base-path existence requires a nonempty index type; real division forms also require a nonempty vertex type. The lower-length condition rules out an impossible nonempty family on an empty vertex type. Quarter claims do not silently apply the mass lower bound to short lists. Empty and singleton shortcut lists have no edges; singleton reflexive travel uses zero edges. No finite ambient vertex type is needed for the median construction.

Supplemental Python checks independently enumerated all 144 transitive relations extending forward list order on sizes 0–5, checking the defined median construction, reachable nonloop edges, both explicit cardinality bounds, and every reachable pair's two-hop guarantee. Quarter lengths and separation were checked for sizes 0–64, and a duplicate-index fixture checked incidence multiplicity. These finite checks supplement, rather than replace, the universal Lean proofs.

## Documentation and integration scope

- `MedianShortcuts.lean:102–103` describes `mediators` as exactly the root-to-node chain with a possible leaf pivot. The definition continues down the right child after the queried vertex is the pivot. For the balanced list `[1,2,3,4,5,6,7]`, `M_4 = {4,6,7}`, although the root-to-node chain ends at 4. Describe it as a single-branch search chain containing the needed ancestors. The height bound and every theorem remain valid.
- The counting module proves a charging interface, not the deletion execution: a later construction must supply event membership and the once-per-occurrence invariant for frozen original suffixes. Likewise the median module takes a transitive relation and forward ordered reachability as inputs; a graph application must instantiate these with the common residual graph. It does not postulate the shortcut set or its two-hop guarantee.
- Converting the explicit list-length bounds to the repair plan's `4LH` / `H` bounds, connecting the witness system to these modules, and assembling the long/short charging and rounding arguments are outside these two files. Their absence is not a failure of the component statements. The previously recorded fixed-λ bookkeeping and real-σ off-by-one issue are not new findings of this review.

## Exact reviewed source fingerprints

SHA-256:

- `DirectedFlowCutGap/PathSystemCounting.lean`: `6c437889143da031628c7d914d701af3f2a3cd9672f6be67382209115430d844`
- `DirectedFlowCutGap/MedianShortcuts.lean`: `d357f86b271698c9e03a7a91ad84235e65c1f0e48f09ae01836af597dcb5e2f4`
- `sources/2604.03412v3/tex/body.tex`: `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325`
- `sources/2604.03412v3/WITNESS_REPAIR_PLAN.md`: `8900d2fd3bc25595ee12e69d9bf59674a06947321dbd7c32e5dc7581f701dcee`

The Lean fingerprints identify the exact audited source snapshot; any later change should be reconciled with this review and the corresponding compilation, axiom, and replay records.
