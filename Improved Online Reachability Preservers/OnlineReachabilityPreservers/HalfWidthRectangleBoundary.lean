import OnlineReachabilityPreservers.HalfWidthRectangleRepair

/-! Pay for a width-boundary erasure in a dense retained rectangle. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Only test width-walk spans in a dense chosen rectangle, and only
check degree-copy returns on its parents after the boundary erasure. -/
def HasSupportedHalfShortSpanWidthRepair {n p : ℕ} (paths : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  ∃ A : Finset (ListVertexBlockIndex paths D), A.card ≤ n ∧
    ∃ B : Finset (ListBlockIndex copies L), B.card ≤ p ∧
      let masked := listPiecesInRectangle raw A B
      let marked := widthBoundaryIncidences copies L (L/3)
      let kept := erasePieceIncidences masked marked
      27*M ≤ 31*(∑ j ∈ B, ((raw j).toFinset ∩ A).card) ∧
      CrossedWidthWalkSpanLEOn copies L masked (cutoff-3) (L/3) ∧
      NoShortBackwardCopyReturnIn (parentsRestrictedToPieces copies kept Sigma.fst) (cutoff-3)

/-- If a dense rectangle passes the supported span and degree tests,
third-width erasure leaves enough to keep M/27 with the four original
caps, both original budgets and the input cutoff. -/
theorem regularization_list_frozen_half_of_supported_short_spans {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasSupportedHalfShortSpanWidthRepair paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) cutoff ∧
      M ≤ 27*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,retained,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free two hn hp dense long low
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree.halfFree,by omega,upper,caps⟩
  obtain ⟨A,va,B,pa,mass,span,degreeSafe⟩ := repair (Nat.lt_of_not_ge low)
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  let masked := listPiecesInRectangle raw A B
  let marked := widthBoundaryIncidences copies L (L/3)
  have copiedSimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have sub (j : ListBlockIndex copies L) : (masked j).Sublist (splitListPaths copies L j) := by
    unfold masked listPiecesInRectangle
    split
    · exact List.filter_sublist
    · exact List.nil_sublist _
  obtain ⟨widthPos,_,_⟩ := four_average_width hp long
  have widthSafe := noShortBackwardReturnAcrossPieces_erase_width_boundary_of_sublist
    copies copiedSimple masked sub widthPos span
  have charge : 3*marked.card ≤ M := by
    have bound := widthBoundaryIncidences_scaled_mass copies copiedSimple
      (scale := 3) (width := L) (margin := L/3) (by omega)
    simpa only [copies,splitListVertices_length,M] using bound
  apply regularization_list_frozen_half_of_supported_width_erasure paths simple free hn hp dense long (by decide)
  refine ⟨A,va,B,pa,marked,degreeSafe,widthSafe,?_⟩
  exact dense_width_rectangle_pays_third_erasure hn hp va pa mass charge

/-- The supported short-span repair also gives a literal distinct
nonempty witness at the same half cutoff. -/
theorem regularization_list_frozen_half_distinct_of_supported_short_spans {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) cutoff)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasSupportedHalfShortSpanWidthRepair paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) cutoff ∧ M ≤ 27*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := cutoff) (retention := 27)
    paths distinct nonempty simple free two hn hp dense (by decide)
    (fun long => regularization_list_frozen_half_of_supported_short_spans paths simple free two hn hp dense long repair)

end OnlineReachabilityPreservers
