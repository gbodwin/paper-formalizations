import MinorFreeSpanners.SelectedResidualClusters
import MinorFreeSpanners.TouchingClusterEdges

/-! Heavy-edge payment uses the ORIGINAL small-cluster labels. Collapsing a
selected large root may hide parallel incidences, so its new simple quotient
degree is deliberately not used for this count. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def residualIndexPreimage {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P)) :
    Finset {i // i∉P.biUnion id} := by
  classical
  exact Finset.univ.filter fun i => Sum.inr i∈S

noncomputable def originalResidualIndices {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P)) : Finset I :=
  (residualIndexPreimage P S).image Subtype.val

 theorem originalResidualIndices_card {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (hS : ∀ t : {S // S∈P},Sum.inl t∉S) :
    (originalResidualIndices P S).card=S.card := by
  classical
  have he : (residualIndexPreimage P S).image Sum.inr=S := by
    ext j
    cases j with
    | inl t => simp [residualIndexPreimage,hS t]
    | inr i => simp [residualIndexPreimage]
  rw [originalResidualIndices,Finset.card_image_of_injective _ Subtype.val_injective]
  calc
    _ = ((residualIndexPreimage P S).image Sum.inr).card :=
      (Finset.card_image_of_injective _ Sum.inr_injective).symm
    _ = S.card := congrArg Finset.card he

namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

 theorem mixed_residual_heavy_edges (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hB : B≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (S : Finset (SelectedResidualIndex P)) (hS : ∀ t : {S // S∈P},Sum.inl t∉S)
    (q : ℕ) (M : ℝ) (hM : 0≤M)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.touchingEdges B (originalResidualIndices P S),w e)≤((q:ℝ)*M)*S.card ∧
    (∀ j∈S,∀ x,x∈(C.selectedResidual hA P F hbranch).branch j →
      ∀ y,B.Adj x y → s(x,y)∈C.touchingEdges B (originalResidualIndices P S)) := by
  classical
  constructor
  · have hh := C.touching_edges_weight_le hA hB (originalResidualIndices P S) q M hM
      (by
        intro i hi
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
        exact hdeg j.val j.property) hweight hloop hsingle
    rwa [originalResidualIndices_card P S hS] at hh
  · intro j hj x hx y hxy
    cases j with
    | inl t => exact (hS t hj).elim
    | inr i =>
      have hi : i.val∈originalResidualIndices P S :=
        Finset.mem_image.mpr ⟨i,by simpa [residualIndexPreimage] using hj,rfl⟩
      obtain ⟨k,hyk⟩ := hcover y
      exact Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxy,i.val,hi,k,x,hx,y,hyk,rfl⟩

end ClusterFamily
end MinorFreeSpanners
