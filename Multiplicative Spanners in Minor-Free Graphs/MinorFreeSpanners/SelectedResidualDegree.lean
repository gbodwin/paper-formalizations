import MinorFreeSpanners.SelectedCommonForest
import MinorFreeSpanners.MixedSmallAbsorptionPhase

/-! The common-tree construction preserves the literal old residual neighbor
count. Contracted roots cannot inflate a residual degree, and no original
residual neighbor is dropped. This is the degree premise used by path assembly. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]

omit [Fintype I] in
def selectedResidualEmbedding (P : Finset (Finset I)) :
    {i // i∉P.biUnion id} ↪ SelectedResidualIndex P := ⟨Sum.inr,Sum.inr_injective⟩

omit [Fintype I] in
 theorem selected_residual_induce_eq (P : Finset (Finset I))
    (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) :
    K.comap (selectedResidualEmbedding P)=H.induce {i | i∉P.biUnion id} := by
  ext i j
  exact hres i j

 theorem selected_residual_degree_card (P : Finset (Finset I))
    (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (i : {i // i∉P.biUnion id}) :
    ((K.neighborFinset (Sum.inr i))\selectedRoots P).card=
      ((H.neighborFinset i.val)\P.biUnion id).card := by
  classical
  apply Finset.card_bij (fun j _ => Sum.elim (fun _ => i.val) Subtype.val j)
  · intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hij,hnot⟩
    cases j with
    | inl S => exact (hnot (by simp [selectedRoots])).elim
    | inr j =>
      exact Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr ((hres i j).mp
        ((K.mem_neighborFinset _ _).mp hij)),j.property⟩
  · intro j hj k hk he
    cases j with
    | inl S => exact ((Finset.mem_sdiff.mp hj).2 (by simp [selectedRoots])).elim
    | inr j =>
      cases k with
      | inl S => exact ((Finset.mem_sdiff.mp hk).2 (by simp [selectedRoots])).elim
      | inr k => exact congrArg Sum.inr (Subtype.ext he)
  · intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hij,hnot⟩
    refine ⟨Sum.inr ⟨j,hnot⟩,Finset.mem_sdiff.mpr ⟨?_,by simp [selectedRoots]⟩,rfl⟩
    exact (K.mem_neighborFinset _ _).mpr ((hres i ⟨j,hnot⟩).mpr ((H.mem_neighborFinset _ _).mp hij))

end MinorFreeSpanners
