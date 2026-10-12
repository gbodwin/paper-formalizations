import MinorFreeSpanners.ResidualInteriorEdgeExclusion

/-! The first path step pays literal selected, endpoint and large-block old
labels. Every residual old label outside their union is in an actual small
non-endpoint block, with no implicit block-order premise. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def residualStepOneLabels {I J : Type*} (F : Finset J)
    (P : J → Finset (Finset I)) (selected ends : J → Finset I) (N : ℕ) : Finset I := by
  classical
  exact F.biUnion fun t => selected t ∪ ends t ∪ ((P t).filter (fun S => N<S.card)).biUnion id

 theorem unpaid_residual_label_block {I : Type*} (H : SimpleGraph I) (R : Finset I)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent) (d : I → ℝ) (M L : ℝ) (N : ℕ)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I))
    (selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hpart : ∀ t∈F,ResidualAttachmentPartition H R t d M L N (port t) (P t) (selected t) (ends t))
    {x : I} (hx : x∈F.biUnion (ResidualComponents.block H R))
    (hxpaid : x∉residualStepOneLabels F P selected ends N) :
    ∃ t∈F,∃ S∈P t,S.card≤N ∧ x∈S ∧ x∉ends t := by
  classical
  obtain ⟨t,ht,hxt⟩ := Finset.mem_biUnion.mp hx
  rw [←(hpart t ht).cover] at hxt
  obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hxt
  have hnot : x∉selected t ∪ ends t ∪ ((P t).filter (fun S => N<S.card)).biUnion id :=
    fun h => hxpaid (Finset.mem_biUnion.mpr ⟨t,ht,h⟩)
  refine ⟨t,ht,S,hS,?_,hxS,?_⟩
  · by_contra hn
    have hn' : N<S.card := by omega
    exact hnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨S,Finset.mem_filter.mpr ⟨hS,hn'⟩,hxS⟩))
  · intro he
    exact hnot (Finset.mem_union_left _ (Finset.mem_union_right _ he))

namespace ClusterFamily
variable {I V : Type*} {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem no_unpaid_residual_edge (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (hforest : H.IsAcyclic) (d : I → ℝ) (L M : ℝ)
    (W U R : Finset I) (hRW : R⊆W) (hRU : Disjoint R U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent) (N : ℕ)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I))
    (selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hpart : ∀ t∈F,ResidualAttachmentPartition H R t (fun i => d i+1)
      M L N (port t) (P t) (selected t) (ends t))
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D)
    {x y : I} (hx : x∈F.biUnion (ResidualComponents.block H R))
    (hy : y∈F.biUnion (ResidualComponents.block H R))
    (hxpaid : x∉residualStepOneLabels F P selected ends N)
    (hypaid : y∉residualStepOneLabels F P selected ends N)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) : ¬B.Adj a b := by
  obtain ⟨t,ht,S,hS,hSN,hxS,hxE⟩ := unpaid_residual_label_block H R F
    (fun i => d i+1) M L N port P selected ends hpart hx hxpaid
  obtain ⟨q,hq,T,hT,hTN,hyT,hyE⟩ := unpaid_residual_label_block H R F
    (fun i => d i+1) M L N port P selected ends hpart hy hypaid
  exact C.no_residual_small_interior_edge H hforest d L M W U R hRW hRU hmax
    F N port P selected ends hpart hL hd0 hd ht hq hS hT hSN hTN hxS hyT hxE hyE ha hb

end ClusterFamily
end MinorFreeSpanners
