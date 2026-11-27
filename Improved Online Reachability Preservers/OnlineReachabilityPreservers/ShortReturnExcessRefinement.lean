import OnlineReachabilityPreservers.ShortReturnSharedClipping

/-! Track the excess saved when the short-return components are recomputed. -/

namespace OnlineReachabilityPreservers

open Finset

variable {I V : Type*} [LinearOrder I] [LinearOrder V] [Fintype I] [Fintype V]

/-- A surviving degree class belongs to a unique original degree class,
even when its own canonical representative has changed. -/
theorem shortReturnDegreeClass_refines_of_sublist {rows kept : I → List V}
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) (k : ℕ) :
    ∀ ⦃a b⦄, a ∈ pieceIncidences kept univ → b ∈ pieceIncidences kept univ →
      shortReturnDegreeClass kept k a = shortReturnDegreeClass kept k b →
      shortReturnDegreeClass rows k a = shortReturnDegreeClass rows k b := by
  rintro ⟨i, x⟩ ⟨j, y⟩ _ onB same
  have vertices : x = y := congrArg Prod.fst same
  subst y
  have together : componentLabel (shortReturnCopyRowGraph kept k x) i =
      componentLabel (shortReturnCopyRowGraph kept k x) j := congrArg Prod.snd same
  have inComponent : j ∈ shortReturnCopyRowComponent kept k x i := by
    apply mem_filter.mpr
    exact ⟨mem_occurrences.mpr (List.mem_toFinset.mpr (mem_pieceIncidences.mp onB).2), together.symm⟩
  have inOriginal := shortReturnCopyRowComponent_subset_of_sublist simple sub k x i inComponent
  exact Prod.ext rfl (mem_filter.mp inOriginal).2.symm

omit [LinearOrder I] in
/-- A surviving path class belongs to a unique original path class. -/
theorem shortReturnPathClass_refines_of_sublist {rows kept : I → List V}
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) (k : ℕ) :
    ∀ ⦃a b⦄, a ∈ pieceIncidences kept univ → b ∈ pieceIncidences kept univ →
      shortReturnPathClass kept k a = shortReturnPathClass kept k b →
      shortReturnPathClass rows k a = shortReturnPathClass rows k b := by
  rintro ⟨i, x⟩ ⟨j, y⟩ _ onB same
  have parents : i = j := congrArg Prod.fst same
  subst j
  have together : componentLabel (shortReturnRowGraph kept k i) x =
      componentLabel (shortReturnRowGraph kept k i) y := congrArg Prod.snd same
  have inComponent : y ∈ shortReturnRowComponent kept k i x := by
    apply mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr (mem_pieceIncidences.mp onB).2, together.symm⟩
  have inOriginal := shortReturnRowComponent_subset_of_sublist simple sub k i x inComponent
  exact Prod.ext rfl (mem_filter.mp inOriginal).2.symm

private theorem shortReturnExcess_le_old_labels {rows kept : I → List V}
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) (D L k : ℕ) :
    shortReturnDegreeExcessMass kept D k ≤
      FiberClipping.totalExcess (pieceIncidences kept univ) (shortReturnDegreeClass rows k) D ∧
    shortReturnPathExcessMass kept L k ≤
      FiberClipping.totalExcess (pieceIncidences kept univ) (shortReturnPathClass rows k) L := by
  rw [← shortReturnDegreeClass_totalExcess kept D k, ← shortReturnPathClass_totalExcess kept L k]
  exact ⟨FiberClipping.totalExcess_le_of_refinement (pieceIncidences kept univ)
    (shortReturnDegreeClass kept k) (shortReturnDegreeClass rows k) D
    (fun {_ _} left right same => shortReturnDegreeClass_refines_of_sublist simple sub k left right same),
    FiberClipping.totalExcess_le_of_refinement (pieceIncidences kept univ)
      (shortReturnPathClass kept k) (shortReturnPathClass rows k) L
      (fun {_ _} left right same => shortReturnPathClass_refines_of_sublist simple sub k left right same)⟩

/-- Each total excess can only decrease under rowwise restriction at
its original prescribed width. -/
theorem shortReturnExcess_le_of_sublist {rows kept : I → List V}
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) (D L k : ℕ) :
    shortReturnDegreeExcessMass kept D k ≤ shortReturnDegreeExcessMass rows D k ∧
      shortReturnPathExcessMass kept L k ≤ shortReturnPathExcessMass rows L k := by
  have incidences : pieceIncidences kept univ ⊆ pieceIncidences rows univ := by
    intro a on
    obtain ⟨row, vertex⟩ := mem_pieceIncidences.mp on
    exact mem_pieceIncidences.mpr ⟨row, (sub _).subset vertex⟩
  have losses := shortReturnExcess_le_old_labels simple sub D L k
  rw [← shortReturnDegreeClass_totalExcess rows D k, ← shortReturnPathClass_totalExcess rows L k]
  exact ⟨losses.1.trans (FiberClipping.totalExcess_mono incidences (shortReturnDegreeClass rows k) D),
    losses.2.trans (FiberClipping.totalExcess_mono incidences (shortReturnPathClass rows k) L)⟩

/-- Every incidence in a feasible shared deletion set saves at least
one unit on each side, even after the components are recomputed. -/
theorem ShortReturnSharedDeletion.recomputed_excess {rows : I → List V} {D L k : ℕ}
    {shared : Finset (I × V)} (fits : ShortReturnSharedDeletion rows D L k shared)
    (simple : ∀ i, (rows i).Nodup) :
    let kept := erasePieceIncidences rows shared
    shortReturnDegreeExcessMass kept D k + shared.card ≤ shortReturnDegreeExcessMass rows D k ∧
      shortReturnPathExcessMass kept L k + shared.card ≤ shortReturnPathExcessMass rows L k := by
  let kept := erasePieceIncidences rows shared
  have sub := erasePieceIncidences_sublist rows shared
  have loss := shortReturnExcess_le_old_labels simple sub D L k
  obtain ⟨within, degree, path⟩ := fits
  have erased : pieceIncidences kept univ = pieceIncidences rows univ \ shared :=
    pieceIncidences_erase rows shared
  rw [erased] at loss
  have paidV := FiberClipping.totalExcess_sdiff_add_card_of_fits within (shortReturnDegreeClass rows k) D degree
  have paidI := FiberClipping.totalExcess_sdiff_add_card_of_fits within (shortReturnPathClass rows k) L path
  rw [shortReturnDegreeClass_totalExcess] at paidV
  rw [shortReturnPathClass_totalExcess] at paidI
  exact ⟨(Nat.add_le_add_right loss.1 _).trans_eq paidV, (Nat.add_le_add_right loss.2 _).trans_eq paidI⟩

end OnlineReachabilityPreservers
