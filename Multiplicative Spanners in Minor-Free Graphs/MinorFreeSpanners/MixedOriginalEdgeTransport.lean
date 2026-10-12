import MinorFreeSpanners.MixedResidualHeavyEdges
import MinorFreeSpanners.OriginalUnpaidEdgeClassification

/-! Collapsing large selected roots preserves the literal original edge bag
incident to residual labels. It need not preserve multiplicities in the new
simple quotient, so weight bounds are transferred back to original labels. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

 theorem mixed_touching_edges_eq (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (S : Finset (SelectedResidualIndex P)) (hS : ∀ t : {S // S∈P},Sum.inl t∉S) :
    (C.selectedResidual hA P F hbranch).touchingEdges B S=
      C.touchingEdges B (originalResidualIndices P S) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨hBe,j,hj,k,x,hx,y,_,rfl⟩ := Finset.mem_filter.mp he
    cases j with
    | inl t => exact (hS t hj).elim
    | inr i =>
      have hi : i.val∈originalResidualIndices P S := Finset.mem_image.mpr
        ⟨i,by simpa [residualIndexPreimage] using hj,rfl⟩
      obtain ⟨l,hy⟩ := hcover y
      exact C.original_edge_mem_touching _ hi hx hy (mem_edgeFinset.mp hBe)
  · intro he
    obtain ⟨hBe,i,hi,j,x,hx,y,_,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨z,hz,hzi⟩ := Finset.mem_image.mp hi
    subst i
    have hiS : Sum.inr z∈S := by simpa [residualIndexPreimage] using hz
    obtain ⟨k,hy⟩ := C.selectedResidual_covers hA P F hbranch hcover y
    exact (C.selectedResidual hA P F hbranch).original_edge_mem_touching _ hiS hx hy
      (mem_edgeFinset.mp hBe)

 theorem mixed_touching_weight_le (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hB : B≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (S : Finset (SelectedResidualIndex P)) (hS : ∀ t : {S // S∈P},Sum.inl t∉S)
    (q : ℕ) (M : ℝ) (hM : 0≤M)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈(C.selectedResidual hA P F hbranch).touchingEdges B S,w e)≤((q:ℝ)*M)*S.card := by
  rw [C.mixed_touching_edges_eq hA P F hbranch hcover S hS]
  exact (C.mixed_residual_heavy_edges hA hB P F hbranch hcover S hS q M hM
    hdeg hweight hloop hsingle).1

end ClusterFamily
end MinorFreeSpanners
