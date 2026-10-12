import MinorFreeSpanners.SelectedResidualSetTransport

/-! The original branching-maximality output is transported to the same
mixed tree, with the same residual carrier and its actual effective masses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem selected_residual_branching_maximality {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ) (L : ℝ)
    (hmax : ∀ W : Finset I,ConnectedWithin H W → Disjoint W (P.biUnion id) →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧ L≤pathMass (fun i => d i+1) p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (W : Finset (SelectedResidualIndex P)) (hconn : ConnectedWithin K W)
    (hW : ∀ j∈W,j∉selectedRoots P)
    (hlong : ∃ x y,∃ p : K.Walk x y,p.IsPath ∧ (∀ j∈p.support,j∈W) ∧
      L≤pathMass (mixedEffectiveDiameter d radius) p) :
    ∀ j∈W,((K.neighborFinset j)∩W).card≤2 := by
  classical
  have hlongOld : ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      (∀ i∈p.support,i∈originalResidualIndices P W) ∧ L≤pathMass (fun i => d i+1) p := by
    obtain ⟨x,y,p,hp,hs,hm⟩ := hlong
    have hx := hW x (hs x p.start_mem_support)
    have hy := hW y (hs y p.end_mem_support)
    cases x with
    | inl t => exact (hx (by simp [selectedRoots])).elim
    | inr x =>
      cases y with
      | inl t => exact (hy (by simp [selectedRoots])).elim
      | inr y =>
        obtain ⟨q,hqs,hqp,he⟩ := selected_residual_walk_transport P K H hres d radius W hW p hs
        exact ⟨x.val,y.val,q,hqp hp,hqs,by rwa [he]⟩
  have hold := hmax (originalResidualIndices P W)
    (selected_residual_connected_transport P K H hres W hW hconn)
    (original_residual_indices_disjoint P W) hlongOld
  intro j hj
  cases j with
  | inl t => exact (hW _ hj (by simp [selectedRoots])).elim
  | inr j =>
    rw [selected_residual_neighbor_card P K H hres W hW j]
    exact hold j.val (Finset.mem_image.mpr ⟨j,by simpa [residualIndexPreimage] using hj,rfl⟩)

end MinorFreeSpanners
