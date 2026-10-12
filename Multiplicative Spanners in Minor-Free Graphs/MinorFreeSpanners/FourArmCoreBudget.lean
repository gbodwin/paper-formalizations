import MinorFreeSpanners.FourArmCore

/-! Convert the four-arm budget into the same actual coarse internal-edge
domain used by the original connector embedding. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem internalEdges_mono {I : Type*} [Fintype I] (H : SimpleGraph I)
    {S T : Finset I} (hST : S⊆T) : internalEdges H S⊆internalEdges H T := by
  classical
  intro e he
  obtain ⟨he,hS⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨he,hS.trans hST⟩

namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem FourArmCore.credit (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d credit : I → ℝ) (L M c b a : ℝ)
    {S : Finset I} (h : C.FourArmCore H d L B S) (hc : 0≤c)
    (hd : ∀ i∈S,d i≤D) (hcredit : ∀ i∈S,c*d i≤credit i)
    (hbase : ∀ i∈S,c*b≤credit i)
    (hpay : 8*a≤c*b) (hroom : 15*D+4*M+15+2*b≤6*L) :
    c*(2*(L+D)+M)+a*S.card+c*b/2≤(∑ i∈S,credit i)+c*(internalEdges H S).card := by
  classical
  obtain ⟨x,y,P,Q,hPQ,rfl,_⟩ := h
  have hbud := four_arm_credit H d credit L D M c b a P Q hPQ hc hd hcredit hbase hpay hroom
  have hsub : internalEdges H P.carrier∪internalEdges H Q.carrier⊆
      internalEdges H (P.carrier∪Q.carrier) :=
    Finset.union_subset (internalEdges_mono H Finset.subset_union_left)
      (internalEdges_mono H Finset.subset_union_right)
  have hcard : ((internalEdges H P.carrier∪internalEdges H Q.carrier).card:ℝ)≤
      (internalEdges H (P.carrier∪Q.carrier)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hm := mul_le_mul_of_nonneg_left hcard hc
  linarith

end ClusterFamily
end MinorFreeSpanners
