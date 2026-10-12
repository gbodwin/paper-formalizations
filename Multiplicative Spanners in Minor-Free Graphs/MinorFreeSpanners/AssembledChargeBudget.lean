import MinorFreeSpanners.AssembledChargeLabels

/-! Cardinality charging matches exactly the allocations already retained
in the actual root and large-block ledgers. Overlaps only decrease the charge. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
 theorem weighted_card_union_le {α : Type*} (A B : Finset α) {a : ℝ} (ha : 0≤a) :
    a*(A∪B).card≤a*A.card+a*B.card := by
  classical
  have hh : ((A∪B).card:ℝ)≤A.card+B.card := by exact_mod_cast Finset.card_union_le A B
  simpa only [mul_add] using mul_le_mul_of_nonneg_left hh ha

 theorem weighted_card_biUnion_le {α β : Type*} (F : Finset α) (P : α → Finset β)
    {a : ℝ} (ha : 0≤a) : a*(F.biUnion P).card≤∑ t∈F,a*(P t).card := by
  classical
  have hh : ((F.biUnion P).card:ℝ)≤∑ t∈F,((P t).card:ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s:=F) (t:=P))
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left hh ha

namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)

 theorem root_charge_budget (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) (ha : 0≤a) (r : {r // r∈roots}) :
    a*(rootCharge O Q active owner r).card≤rootSpent O Q r+a*(assignedBlockUnion active owner r).card := by
  have h₁ := weighted_card_union_le
    ((O.components r).biUnion (Q r).selected ∪ (O.components r).biUnion (Q r).ends)
    (assignedBlockUnion active owner r) ha
  have h₂ := weighted_card_union_le
    ((O.components r).biUnion (Q r).selected) ((O.components r).biUnion (Q r).ends) ha
  have h₃ := weighted_card_biUnion_le (O.components r) (Q r).ends ha
  unfold rootCharge rootSpent
  linarith

 theorem charge_budget (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) (ha : 0≤a) :
    a*(chargeLabels O Q active owner).card≤
      (∑ r,(rootSpent O Q r+a*(assignedBlockUnion active owner r).card))+
        ∑ S∈largeLeftovers O Q,a*S.card := by
  have hu := weighted_card_union_le (Finset.univ.biUnion (rootCharge O Q active owner))
    ((largeLeftovers O Q).biUnion id) ha
  have hr := weighted_card_biUnion_le Finset.univ (rootCharge O Q active owner) ha
  have hl := weighted_card_biUnion_le (largeLeftovers O Q) id ha
  have hroots := Finset.sum_le_sum (s:=Finset.univ)
    (fun r _ => root_charge_budget O Q active owner ha r)
  exact hu.trans (add_le_add (hr.trans hroots) hl)

end AssembledPathFamilies
end MinorFreeSpanners
