import MinorFreeSpanners.SelectedResidualWalkTransport
import MinorFreeSpanners.WeightedInteriorTransport

/-! Actual mixed residual interiors are sent to the unchanged original labels.
Selected roots never enter the map, so neither their larger radii nor their
uniform family diameter changes the path thresholds used by maximality. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem originalResidualIndices_mem_iff {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (W : Finset (SelectedResidualIndex P)) (i : {i // i∉P.biUnion id}) :
    i.val∈originalResidualIndices P W ↔ Sum.inr i∈W := by
  classical
  simp only [originalResidualIndices,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    have hh : j=i := Subtype.ext he
    subst j
    simpa [residualIndexPreimage] using hj
  · intro hi
    exact ⟨i,by simpa [residualIndexPreimage] using hi,rfl⟩

 theorem originalResidualIndices_disjoint {I : Type*} [Fintype I]
    (P : Finset (Finset I)) {W Z : Finset (SelectedResidualIndex P)} (h : Disjoint W Z) :
    Disjoint (originalResidualIndices P W) (originalResidualIndices P Z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.disjoint_left.mp h
    ((originalResidualIndices_mem_iff P W x).mp (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    ((originalResidualIndices_mem_iff P Z x).mp hj)

 theorem selected_residual_interior_transport {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hK : K.IsAcyclic) (hH : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ) (L : ℝ)
    (W : Finset (SelectedResidualIndex P)) (hW : ∀ j∈W,j∉selectedRoots P)
    {x y : {i // i∉P.biUnion id}} (p : K.Walk (Sum.inr x) (Sum.inr y))
    (hp : p.IsPath) (hs : ∀ j∈p.support,j∈W) :
    ∃ q : H.Walk x.val y.val,q.IsPath ∧
      (∀ i∈q.support,i∈originalResidualIndices P W) ∧
      ∀ i : {i // i∉P.biUnion id},
        WeightedInterior (mixedEffectiveDiameter d radius) L p (Sum.inr i) →
          WeightedInterior (fun i => d i+1) L q i.val := by
  classical
  let S : Set (SelectedResidualIndex P) := {j | j∉selectedRoots P}
  have hpS : ∀ j∈p.support,j∈S := fun j hj => hW j (hs j hj)
  let p0 := p.induce S hpS
  let f := selectedResidualProjection P K H hres
  let q : H.Walk x.val y.val := p0.map f
  have hp0 : p0.IsPath := by
    apply Walk.IsPath.of_map (f:=(Embedding.induce S).toHom)
    simpa [p0] using hp
  have he : (fun j : S => d (f j)+1)=(fun j : S => mixedEffectiveDiameter d radius j.val) := by
    funext j
    rcases j with ⟨j,hj⟩
    cases j with
    | inl t => exact (hj (by simp [selectedRoots])).elim
    | inr i => rfl
  refine ⟨q,hp0.map (selectedResidualProjection_injective P K H hres),?_,?_⟩
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
    | inr i => exact (originalResidualIndices_mem_iff P W i).mpr (hs _ hjp)
  · intro i hi
    let i0 : S := ⟨Sum.inr i,by simp [S,selectedRoots]⟩
    have hi0 : WeightedInterior (fun j : S => mixedEffectiveDiameter d radius j.val) L p0 i0 := by
      apply (weightedInterior_map_iff hK (Embedding.induce S).toHom Subtype.val_injective
        (mixedEffectiveDiameter d radius) L p0 hp0).mp
      simpa [p0,i0] using hi
    have hq := (weightedInterior_map_iff hH f (selectedResidualProjection_injective P K H hres)
      (fun i => d i+1) L p0 hp0).mpr (he ▸ hi0)
    exact hq

 theorem originalResidualIndices_subset_complement {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (W : Finset (SelectedResidualIndex P)) :
    originalResidualIndices P W⊆Finset.univ\P.biUnion id := by
  classical
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_sdiff.mpr ⟨mem_univ _,j.property⟩

 theorem selected_residual_interior_path_transport {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hK : K.IsAcyclic) (hH : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ) (L : ℝ)
    (W : Finset (SelectedResidualIndex P)) (hW : ∀ j∈W,j∉selectedRoots P)
    {x y : SelectedResidualIndex P} (p : K.Walk x y)
    (hp : p.IsPath) (hs : ∀ j∈p.support,j∈W) :
    ∃ a b,∃ q : H.Walk a b,q.IsPath ∧
      (∀ i∈q.support,i∈originalResidualIndices P W) ∧
      ∀ i : {i // i∉P.biUnion id},
        WeightedInterior (mixedEffectiveDiameter d radius) L p (Sum.inr i) →
          WeightedInterior (fun i => d i+1) L q i.val := by
  have hx := hW x (hs x p.start_mem_support)
  have hy := hW y (hs y p.end_mem_support)
  cases x with
  | inl S => exact (hx (by simp [selectedRoots])).elim
  | inr x =>
    cases y with
    | inl S => exact (hy (by simp [selectedRoots])).elim
    | inr y =>
      obtain ⟨q,hq,hqs,hi⟩ := selected_residual_interior_transport P K H hK hH hres d radius L W hW p hp hs
      exact ⟨x.val,y.val,q,hq,hqs,hi⟩

end MinorFreeSpanners
