import MinorFreeSpanners.ExpandedResidualLabels

/-! The actual expanded roots and remaining original singletons partition the
previous mixed labels. This is the carrier-level bridge to one common next tree. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
noncomputable def expandedResidualLabel {I J : Type*} [Fintype I] [Fintype J]
    (P : Finset (Finset I)) (S : J → Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (U : Finset (Finset I)) (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (i : {i // i∉U.biUnion id}) : {i // i∉P.biUnion id} :=
  ⟨i.val,by
    intro hi
    apply i.property
    exact (Finset.ext_iff.mp hU i.val).mpr (old_selected_subset_expanded P _ hroot hi)⟩

attribute [-instance] instDecidableEqSum in
noncomputable def expandedPiece {I J : Type*} [Fintype I] [Fintype J]
    (P : Finset (Finset I)) (S : J → Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (U : Finset (Finset I)) (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (e : J ≃ {g // g∈U}) : SelectedResidualIndex U → Set (SelectedResidualIndex P) :=
  Sum.elim (fun g => (S (e.symm g) : Set _))
    (fun i => {Sum.inr (expandedResidualLabel P S hroot U hU i)})

namespace ClusterFamily
variable {I J V : Type*} [Fintype I] [Fintype J]
variable {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E E' : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem expanded_piece_branch (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={g // g∈P}) G w E)
    (hbranch : ∀ g,F.branch g={x | ∃ i∈g.val,x∈C.branch i})
    (S : J → Finset (SelectedResidualIndex P)) (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (Fnew : ClusterFamily (I:=J) G w E')
    (hnew : ∀ j,Fnew.branch j={x | ∃ i∈S j,x∈(C.selectedResidual hA P F hbranch).branch i})
    (U : Finset (Finset I)) (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (e : J ≃ {g // g∈U})
    (hfinal : ∀ g,(Fnew.reindex e.symm).branch g={x | ∃ i∈g.val,x∈C.branch i})
    (j : SelectedResidualIndex U) (x : V) :
    x∈(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).branch j ↔
      ∃ i∈expandedPiece P S hroot U hU e j,x∈(C.selectedResidual hA P F hbranch).branch i := by
  cases j with
  | inl g => exact Set.ext_iff.mp (hnew (e.symm g)) x
  | inr i => simp only [expandedPiece,Sum.elim_inr,Set.mem_singleton_iff,exists_eq_left]
             rfl

attribute [-instance] instDecidableEqSum in
noncomputable def expandedLabelPartition (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={g // g∈P}) G w E)
    (hbranch : ∀ g,F.branch g={x | ∃ i∈g.val,x∈C.branch i})
    (S : J → Finset (SelectedResidualIndex P)) (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (Fnew : ClusterFamily (I:=J) G w E')
    (hnew : ∀ j,Fnew.branch j={x | ∃ i∈S j,x∈(C.selectedResidual hA P F hbranch).branch i})
    (U : Finset (Finset I)) (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (e : J ≃ {g // g∈U})
    (hfinal : ∀ g,(Fnew.reindex e.symm).branch g={x | ∃ i∈g.val,x∈C.branch i}) :
    LabelPartition (SelectedResidualIndex P) (SelectedResidualIndex U) where
  piece := expandedPiece P S hroot U hU e
  nonempty := by
    intro j
    obtain ⟨x,hx⟩ := (C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).nonempty j
    obtain ⟨i,hi,_⟩ := (C.expanded_piece_branch hA P F hbranch S hroot Fnew hnew U hU e hfinal j x).mp hx
    exact ⟨i,hi⟩
  disjoint := by
    intro j k hne
    apply Set.disjoint_left.mpr
    intro i hi hj
    obtain ⟨x,hx⟩ := (C.selectedResidual hA P F hbranch).nonempty i
    exact Set.disjoint_left.mp ((C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).disjoint j k hne)
      ((C.expanded_piece_branch hA P F hbranch S hroot Fnew hnew U hU e hfinal j x).mpr ⟨i,hi,hx⟩)
      ((C.expanded_piece_branch hA P F hbranch S hroot Fnew hnew U hU e hfinal k x).mpr ⟨i,hj,hx⟩)
  covers := by
    classical
    intro i
    by_cases hi : i∈Finset.univ.biUnion S
    · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hi
      refine ⟨Sum.inl (e j),?_⟩
      change i∈S (e.symm (e j))
      simpa only [e.symm_apply_apply] using hj
    · cases i with
      | inl g => exact (hi (hroot (by simp [selectedRoots]))).elim
      | inr i =>
        have hiU : i.val∉U.biUnion id := by
          rw [hU]
          exact fun hh => hi ((residual_mem_originalMixedLabels P _ i).mp hh)
        refine ⟨Sum.inr ⟨i.val,hiU⟩,?_⟩
        exact Set.mem_singleton _

end ClusterFamily
end MinorFreeSpanners
