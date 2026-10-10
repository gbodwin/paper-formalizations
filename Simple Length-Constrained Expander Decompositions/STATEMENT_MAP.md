# Statement map — arXiv:2510.10227v1

The main corrected proof chains are complete locally and independently reviewed. Exact-checkpoint CI is reported separately in `VERIFICATION.md`. Finite simple graphs, integral capacities and node budgets, and finite cut sequences are explicit. Source statements do not explicitly require integral s; this matters for the exact exponent.

| Source | Checked counterpart and scope |
|---|---|
| Definitions 2.2–2.4 | Integral ordered demands; separate outgoing and incoming budgets. Results allow arbitrary integral node weights, a stronger scope than the source's degree cap. |
| Definitions 2.5–2.13 | Actual weighted walks, length-increase cuts, maximum attained demand volume, sparse cuts, expanders and decompositions. Positive sparse-cut volume is required; the zero decomposition is allowed. |
| Definition 1.1 | Ordered matching labels and earlier-walk exclusion. Real threshold is equivalent to its natural floor. |
| Lemmas 3.2–3.3 | Short cycles cannot have a unique highest edge; short increasing paths are unique per endpoint pair, with the odd-s convention included. |
| Lemma 3.4 | Actual matching permutations/hikers, exact total traversal 2m, fixed-length weak counting and conversion to simple paths. |
| Lemma 3.5 | Constructed finite hitting set, deletion and medium counting. |
| Lemma 3.6 | Exact fixed-size sample incidence counting and explicit subgraph-walk transfer. |
| Theorem 1.3 | For integer s≥2, density ≤8s n^(2/s) and an actual partition into ceil(8s n^(2/s)) forests. For real s≥2, actual partition with rounded exponent 2/floor(s), or smooth bound ceil(8s n^(4/s)). The literal all-real 2/s statement is disproved by the formal K_{a,a} family at s=5/2. |
| Appendix A matching bridge | Repaired separate outgoing/incoming copies, exactly 2\|A\| vertices, exact summed-volume edge count and reverse-order parallel greediness. |
| Appendix A dispersion / integrality | Constructed paired sparse orientation, controlled incidence, projection, and support-preserving factor-two integral extraction. Actual integral witness and strict final separation are derived. The source's literal one-copy/fractional definitions are not adopted. |
| Theorem 4.1 | Integer s≥2: explicit union ratio loss 512s \|A\|^(2/s). All-real s≥2 repair: 512s \|A\|^(4/s). Positive total attained volume required. Output is exactly (1+1/(s−1))*sum cuts, with h'=2h and s'=(s−1)/2. |
| Theorem 1.4 | Nonempty sparse sequence, unit capacities, original degree weighting: integer loss 2048s n^(4/s) φ; all-real loss 2048s n^(8/s) φ. Both are the stated n^O(1/s) form. |
| Lemma 5.2 | Sparse-cut cost ≤φ\|A\| through the full sparse-cut interface. |
| Theorem 5.1 | Constructed unscaled decomposition: integer slack 8s(2\|A\|)^(2/s); all-real repair 8s(2\|A\|)^(4/s). Finite termination, actual expansion, and cost are proved without a union-bound premise. |
| Theorem 1.2 | Unit capacities and original degree weights: integer cost ≤64s n^(4/s) φm; all-real cost ≤256s n^(8/s) φm. Both retain the printed n^O(1/s) form, including empty/zero cases. |

## Parameter-domain correction

Definition 1.1 and Theorem 1.3 say only s≥2; integrality is implicit in Section 3's even/odd proof. At s=5/2, the complete bipartite family has injective singleton-batch labels satisfying the literal definition. `BipartiteCounterexample` proves a² edges, K(2a−1)≥a² for every forest cover, and impossibility of any uniform constant times n^(4/5). Thus the exact unrestricted real exponent is false. `RealParameterArboricity` constructs the valid rounded and smooth repairs.

The real cut proofs round only the auxiliary counting threshold. `RealSequentialDemandGeometry` retains the original h*s separation and yields strict h*(s−1) final separation. The exact output cut and geometric parameters are unchanged; only the sparsity exponents weaken. This is not a claim that the exact printed 2/s general cut bounds have been extended to reals.

## Trust and remaining literal-source scope

Lean 4.34.0, mathlib 5ed2965256430c3649e86755f9576b54eca72435; no sorry, new axiom, unchecked native decision, Nash–Williams oracle, or integral transportation oracle. Forests, witnesses and finite termination are constructed.

Full literal-source verification is not claimed: Lemma 4.2's arbitrary-arboricity-oracle constant 8α(\|A\|,s) is replaced by the explicit constructive bound above. The full numerical two-edge maximal-sequence example remains a source-level calculation, while `RescalingCounterexample` proves its graph-level nonmonotonicity obstruction. The original source reading edition is preserved; corrections are separate.

The complete inventory of all 34 unique numbered items, omitted background statements, and runtime scope is in [COVERAGE_AUDIT.md](COVERAGE_AUDIT.md).
