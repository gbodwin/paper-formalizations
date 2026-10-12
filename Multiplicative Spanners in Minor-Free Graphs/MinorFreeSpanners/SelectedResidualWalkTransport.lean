import MinorFreeSpanners.SelectedResidualGraphIso
import MinorFreeSpanners.PathMassTransport

/-! Transfer a literal residual walk to the old forest, preserving its support
labels, simplicity and effective mass. Selected roots are excluded explicitly. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def selectedResidualProjection {I : Type*} (P : Finset (Finset I))
    (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) :
    K.induce {j | j∉selectedRoots P} →g H :=
  (Embedding.induce {i | i∉P.biUnion id}).toHom.comp (selectedResidualGraphIso P K H hres).toHom

 theorem selectedResidualProjection_injective {I : Type*} (P : Finset (Finset I))
    (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) :
    Function.Injective (selectedResidualProjection P K H hres) :=
  Subtype.val_injective.comp (selectedResidualVertexEquiv P).injective

 theorem selected_residual_walk_transport {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ)
    (W : Finset (SelectedResidualIndex P)) (hW : ∀ j∈W,j∉selectedRoots P)
    {x y : {i // i∉P.biUnion id}} (p : K.Walk (Sum.inr x) (Sum.inr y))
    (hs : ∀ j∈p.support,j∈W) :
    ∃ q : H.Walk x.val y.val,
      (∀ i∈q.support,i∈originalResidualIndices P W) ∧
      (p.IsPath → q.IsPath) ∧ pathMass (fun i => d i+1) q=pathMass (mixedEffectiveDiameter d radius) p := by
  classical
  let S : Set (SelectedResidualIndex P) := {j | j∉selectedRoots P}
  have hpS : ∀ j∈p.support,j∈S := fun j hj => hW j (hs j hj)
  let p0 := p.induce S hpS
  let f := selectedResidualProjection P K H hres
  let q : H.Walk x.val y.val := p0.map f
  have hm := pathMass_map f (selectedResidualProjection_injective P K H hres)
    (fun i => d i+1) p0
  have he : (fun j : S => d (f j)+1)=(fun j : S => mixedEffectiveDiameter d radius j.val) := by
    funext j
    rcases j with ⟨j,hj⟩
    cases j with
    | inl t => exact (hj (by simp [selectedRoots])).elim
    | inr i => rfl
  rw [he] at hm
  refine ⟨q,?_,?_,hm.trans (pathMass_induce S (mixedEffectiveDiameter d radius) p hpS)⟩
  · intro i hi
    change i∈(p0.map f).support at hi
    rw [Walk.support_map,List.mem_map] at hi
    obtain ⟨j,hj,rfl⟩ := hi
    have hjp : j.val∈p.support := by
      have hh : j.val∈(p0.map (Embedding.induce S).toHom).support := by
        rw [Walk.support_map,List.mem_map]
        exact ⟨j,hj,rfl⟩
      simpa [p0] using hh
    rcases j with ⟨j,hnot⟩
    cases j with
    | inl t => exact (hnot (by simp [selectedRoots])).elim
    | inr i =>
      exact Finset.mem_image.mpr ⟨i,by simpa [residualIndexPreimage] using hs (Sum.inr i) hjp,rfl⟩
  · intro hp
    have hp0 : p0.IsPath := by
      apply Walk.IsPath.of_map (f:=(Embedding.induce S).toHom)
      simpa [p0] using hp
    exact hp0.map (selectedResidualProjection_injective P K H hres)

end MinorFreeSpanners
