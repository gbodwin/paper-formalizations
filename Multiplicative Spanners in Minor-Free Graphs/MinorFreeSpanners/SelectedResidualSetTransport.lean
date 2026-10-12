import MinorFreeSpanners.SelectedResidualWalkTransport

/-! Original labels of a residual carrier preserve connectivity and every
internal neighbor count. No collapsed selected-root incidence is counted. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem original_residual_indices_disjoint {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (W : Finset (SelectedResidualIndex P)) :
    Disjoint (originalResidualIndices P W) (P.biUnion id) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hp
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  exact j.property hp

attribute [-instance] instDecidableEqSum in
 theorem selected_residual_connected_transport {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (W : Finset (SelectedResidualIndex P)) (hW : ∀ j∈W,j∉selectedRoots P)
    (hc : ConnectedWithin K W) : ConnectedWithin H (originalResidualIndices P W) := by
  classical
  intro x hx y hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  have hiW : Sum.inr i∈W := by simpa [residualIndexPreimage] using hi
  have hjW : Sum.inr j∈W := by simpa [residualIndexPreimage] using hj
  obtain ⟨p,hp⟩ := hc (Sum.inr i) hiW (Sum.inr j) hjW
  obtain ⟨q,hq,_,_⟩ := selected_residual_walk_transport P K H hres (fun _ => 0) (fun _ => 0) W hW p hp
  exact ⟨q,hq⟩

attribute [-instance] instDecidableEqSum in
 theorem selected_residual_neighbor_card {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (W : Finset (SelectedResidualIndex P)) (hW : ∀ j∈W,j∉selectedRoots P)
    (i : {i // i∉P.biUnion id}) :
    ((K.neighborFinset (Sum.inr i))∩W).card=
      ((H.neighborFinset i.val)∩originalResidualIndices P W).card := by
  classical
  apply Finset.card_bij (fun j _ => Sum.elim (fun _ => i.val) Subtype.val j)
  · intro j hj
    obtain ⟨hadj,hjW⟩ := Finset.mem_inter.mp hj
    cases j with
    | inl t => exact (hW _ hjW (by simp [selectedRoots])).elim
    | inr j =>
      refine Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr ((hres i j).mp
        ((K.mem_neighborFinset _ _).mp hadj)),?_⟩
      exact Finset.mem_image.mpr ⟨j,by simpa [residualIndexPreimage] using hjW,rfl⟩
  · intro j hj k hk he
    cases j with
    | inl t => exact (hW _ (Finset.mem_inter.mp hj).2 (by simp [selectedRoots])).elim
    | inr j =>
      cases k with
      | inl t => exact (hW _ (Finset.mem_inter.mp hk).2 (by simp [selectedRoots])).elim
      | inr k => exact congrArg Sum.inr (Subtype.ext he)
  · intro j hj
    obtain ⟨hadj,hjW⟩ := Finset.mem_inter.mp hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hjW
    refine ⟨Sum.inr k,Finset.mem_inter.mpr ⟨?_,?_⟩,rfl⟩
    · exact (K.mem_neighborFinset _ _).mpr ((hres i k).mpr ((H.mem_neighborFinset _ _).mp hadj))
    · simpa [residualIndexPreimage] using hk

end MinorFreeSpanners
