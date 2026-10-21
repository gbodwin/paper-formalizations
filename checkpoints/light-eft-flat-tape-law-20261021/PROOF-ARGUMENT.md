# Mathematical source argument and sequential author inspection

The ten new theorem bodies have not been checked by Lean. This is an author's
source argument for the next independent review, not independent or kernel
acceptance. No model test is used as a substitute.

1. Let S be the accepted `samplingSchedule n m l`. Its accepted nodup theorem
   makes `S.get : Fin S.length → Coordinate` injective. Its accepted exhaustive
   membership theorem and the pinned `List.mem_iff_get` make it surjective.
   `Equiv.ofBijective` therefore constructs E with forward map exactly `S.get`.
   The accepted schedule length gives N, without charging S's construction.

2. Define the tensor corresponding to tape t by
   `T(t)(p,j,i,d) = t(E.symm (p,j,i,d))`. The inverse reads a tensor at `E(k)`.
   Both inverse laws reduce to the equivalence inverse identities. The
   `tapeEquiv_at_position` theorem makes each read explicit. Applying injectivity
   of E.symm and taking the first projection shows that p != q cannot share a
   flat index, irrespective of whether `candidateAt l p = candidateAt l q`.

3. Define `idealTapeLaw` directly using the accepted `BernoulliFlags.law` at
   finite type `Fin N`, with bias b = 1/(2f). For f > 0, b is in [0,1] by the
   same arithmetic argument as accepted `StoredFlagSample.sourceLaw`. Its mass
   is the literal product over all k of b or 1-b according to t(k). The tape
   law is not constructed by, assumed for, or inferred from any response reader.

4. Apply pinned `Equiv.prod_comp` to E and the factor at coordinate c given by
   the biased mass of `t(E.symm c)`. On the Fin N side, E.symm(E(k)) = k.
   On the coordinate side, three uses of `Fintype.prod_prod_type` expand the
   nested product type into four products over p, j, i, d. This is exactly the
   accepted `jointSourceLaw_mass` at T(t). Thus the masses agree under T.

5. For any tensor predicate P, unfold the finite probability sum. Replace each
   tape mass by the joint mass at T(t), then apply `Equiv.sum_comp` to the full
   tape/tensor equivalence T. This is event equality, hence exact pushforward
   law equality by the accepted `Transport.eq_of_prob_eq` and `Law.prob_map`.
   Reindexing a product, not a marginal calculation, supplies the joint law.

6. Instantiate P with the accepted `PaidJointBridge.storedAssignment`
   interpretation, then apply its accepted supplied-assignment event theorem.
   All randomness is still the explicitly defined ideal product tape law.
   No operational generation, caller execution or cost claim is added.

The author checked boundary cases sequentially: empty candidate list, empty host
type, zero repetitions and empty original-edge universe all yield an empty
coordinate type and Fin 0, with no selected coordinate needed. Every proof is
uniform and uses no nonempty premise or division by N. For repeated candidate
keys, positions remain distinct through T, while the accepted assignment fold
still resolves the repeated key head-first in its final interpretation. The
bijection neither changes that fold nor couples repeated positions.

The new module imports only the accepted supplied-response bridge. Expected
existing project imports are its 80 imports plus that bridge itself (81 total).
The external primary sources were read from the pinned mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435` and the preserved Lean 4.34.0
source tree. Statement signatures and orientation of `Equiv.prod_comp`, its
generated additive `sum_comp`, `Fintype.prod_prod_type`, list membership and
nodup-get injectivity, and `Equiv.ofBijective` were inspected directly.

Possible Lean elaboration issues remain a separate verification obligation:
dependent tape-length unfolding, product eta reductions in inverse proofs and
simplification of product-type products must later pass the unchanged bounded
validation route. No weakening, added axiom or assumed law is proposed to hide
such an issue. The current source is prepared for sequential independent review.
