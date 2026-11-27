import OnlineReachabilityPreservers.FullReturnBoundaryCover

/-! Erase width-boundary incidences using the comparison graph of the pieces. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V]

/-- A bounded backward walk in the given pieces must have both
endpoints within the chosen span on its parent. -/
def CrossedWidthWalkSpanLEOn (rows : I → List V) (width : ℕ)
    (pieces : ListBlockIndex rows width → List V) (radius margin : ℕ) : Prop :=
  let graph := listPiecePrecedenceGraph pieces
  ∀ ⦃i j : ListBlockIndex rows width⦄ ⦃earlier later : V⦄,
    i ≠ j → i.fst = j.fst →
    earlier ∈ pieces i → later ∈ pieces j → Before rows j.fst earlier later →
    later ∈ reachIn graph earlier radius →
    (rows j.fst).idxOf later ≤ (rows j.fst).idxOf earlier+margin

/-- In the actual width-piece graph, every bounded return across two
blocks of the same parent spans at most the given margin in that parent. -/
def CrossedWidthWalkSpanLE (rows : I → List V) (width radius margin : ℕ) : Prop :=
  CrossedWidthWalkSpanLEOn rows width (splitListPaths rows width) radius margin

omit [LinearOrder I] in
/-- The test can be restricted to sublists of the width pieces. Erasure
removes the later endpoint of any remaining tested backward walk. -/
theorem noShortBackwardReturnAcrossPieces_erase_width_boundary_of_sublist {width radius margin : ℕ}
    (rows : I → List V) (simple : ∀ i, (rows i).Nodup) (pieces : ListBlockIndex rows width → List V)
    (sub : ∀ j, (pieces j).Sublist (splitListPaths rows width j))
    (positive : 0 < width) (span : CrossedWidthWalkSpanLEOn rows width pieces radius margin) :
    let kept := erasePieceIncidences pieces (widthBoundaryIncidences rows width margin)
    NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph kept) id rows kept Sigma.fst radius := by
  let marked := widthBoundaryIncidences rows width margin
  let kept := erasePieceIncidences pieces marked
  have pieceSimple (i : ListBlockIndex rows width) : (pieces i).Nodup :=
    (sub i).nodup (List.filter_sublist.nodup (simple i.fst))
  have steps {x y : V} (step : Edge (listPiecePrecedenceGraph kept) x y) :
      Edge (listPiecePrecedenceGraph pieces) (id x) (id y) := by
    obtain ⟨i,inside⟩ := listPiecePrecedenceGraph_edge.mp step
    exact listPiecePrecedenceGraph_edge.mpr
      ⟨i,listBefore_of_sublist (pieceSimple i) (erasePieceIncidences_sublist pieces marked i) inside⟩
  change NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph kept) id rows kept Sigma.fst radius
  intro i j x y apart same first last forward back
  have oldFirst := mem_erasePieceIncidences.mp first
  have oldLast := mem_erasePieceIncidences.mp last
  have oldBack := project_reachIn id (fun {_ _} => steps) radius back
  have reversed : Before rows j.fst x y := same ▸ forward
  have markedLast := mem_widthBoundaryIncidences_of_parent_span rows positive apart.symm same.symm
    ((sub j).subset oldLast.1) ((sub i).subset oldFirst.1) reversed
    (span apart same oldFirst.1 oldLast.1 reversed oldBack)
  exact oldLast.2 markedLast

omit [LinearOrder I] in
/-- A comparison walk remaining after boundary erasure would already
exist in the original pieces. The span bound forces its later endpoint
into the erased part of its width block. -/
theorem noShortBackwardReturnAcrossPieces_erase_width_boundary {width radius margin : ℕ}
    (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (positive : 0 < width) (span : CrossedWidthWalkSpanLE rows width radius margin) :
    let kept := erasePieceIncidences (splitListPaths rows width) (widthBoundaryIncidences rows width margin)
    NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph kept) id rows kept Sigma.fst radius :=
  noShortBackwardReturnAcrossPieces_erase_width_boundary_of_sublist rows simple (splitListPaths rows width)
    (fun _ => List.Sublist.refl _) positive span

/-- A short-span test on the retained sublists gives half exclusion
after boundary erasure, with parent arrival order and cutoff fixed. -/
theorem halfBridgeFree_erase_short_span_width_walks_of_sublist {width cutoff margin : ℕ}
    (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (pieces : ListBlockIndex rows width → List V)
    (sub : ∀ j, (pieces j).Sublist (splitListPaths rows width j))
    (free : HalfBridgeFree (Before rows) cutoff) (positive : 0 < width)
    (span : CrossedWidthWalkSpanLEOn rows width pieces (cutoff-3) margin) :
    HalfBridgeFree (Before (erasePieceIncidences pieces (widthBoundaryIncidences rows width margin))) cutoff := by
  let marked := widthBoundaryIncidences rows width margin
  let kept := erasePieceIncidences pieces marked
  have oldSub (i : ListBlockIndex rows width) : (kept i).Sublist (splitListPaths rows width i) :=
    (erasePieceIncidences_sublist pieces marked i).trans (sub i)
  have parentSub (i : ListBlockIndex rows width) : (kept i).Sublist (rows i.fst) :=
    (oldSub i).trans List.filter_sublist
  refine halfBridgeFree_of_disjoint_split_of_no_backward_returns (listPiecePrecedenceGraph kept) id
    free Sigma.fst (block_parent_mono _ width) (fun {i _ _} step => listBefore_of_sublist
      (paths := rows ∘ Sigma.fst) (simple i.fst) (parentSub i) step)
    (fun {i _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨i,step⟩) ?_ ?_
  · intro i j x apart same first last
    exact splitListPaths_disjoint apart same ((oldSub i).subset first) ((oldSub j).subset last)
  · exact noShortBackwardReturnAcrossPieces_erase_width_boundary_of_sublist rows simple pieces sub positive span

/-- If the parent rows already have half-bridge exclusion, boundary
erasure preserves it through the input cutoff. The comparison walk
test uses radius cutoff minus three and the original arrival order. -/
theorem halfBridgeFree_erase_short_span_width_walks {width cutoff margin : ℕ}
    (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) cutoff) (positive : 0 < width)
    (span : CrossedWidthWalkSpanLE rows width (cutoff-3) margin) :
    HalfBridgeFree (Before (erasePieceIncidences (splitListPaths rows width)
      (widthBoundaryIncidences rows width margin))) cutoff :=
  halfBridgeFree_erase_short_span_width_walks_of_sublist rows simple (splitListPaths rows width)
    (fun _ => List.Sublist.refl _) free positive span

open Finset
open scoped Sigma.Lex

/-- For the standard copies, half exclusion must survive the degree
split. Each actual bounded width return has parent span at most one
eighth of the original width, rounded down. -/
def HasHalfShortSpanWidthRepair {n p : ℕ} (paths : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  HalfBridgeFree (Before copies) cutoff ∧ CrossedWidthWalkSpanLE copies L (cutoff-3) (L/8)

/-- On the dense branch, erase at most one eighth of the incidences
from the standard width pieces and keep the same half cutoff. The
original budgets and caps leave at least one thirty-second of the mass. -/
theorem regularization_list_frozen_half_of_short_span_width_walks {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasHalfShortSpanWidthRepair paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) cutoff ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',va,p',pa,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free two hn hp dense long low
    exact ⟨n',va,p',pa,clean,cleanSimple,cleanFree.halfFree,by omega,upper,caps⟩
  have high := lt_of_not_ge low
  obtain ⟨safe,span⟩ := repair high
  let D := 4*M/n
  let L := 4*M/p
  let W := ListVertexBlockIndex paths D
  let copies := splitListVertices paths D
  let J := ListBlockIndex copies L
  let pieces : J → List W := listRegularizedPaths paths D L
  let marked := widthBoundaryIncidences copies L (L/8)
  let kept := erasePieceIncidences pieces marked
  have parentSimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have pieceSimple (j : J) : (pieces j).Nodup := listRegularizedPaths_simple paths simple D L j
  have sub (j : J) := erasePieceIncidences_sublist pieces marked j
  have keptSimple (j : J) : (kept j).Nodup := (sub j).nodup (pieceSimple j)
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  have keptFree : HalfBridgeFree (Before kept) cutoff :=
    halfBridgeFree_erase_short_span_width_walks copies parentSimple safe lPos span
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have cost : 8*marked.card ≤ M := by
    have bound := widthBoundaryIncidences_scaled_mass copies parentSimple
      (width := L) (margin := L/8) (scale := 8) (by omega)
    simpa only [copies,splitListVertices_length,M] using bound
  have lost := erasePieceIncidences_mass_add_loss pieceSimple (univ : Finset J) marked
  change (∑ j, (kept j).length) + (pieceIncidences pieces univ ∩ marked).card = _ at lost
  change (∑ j, (pieces j).length) = M at mass
  rw [mass] at lost
  have spent : (pieceIncidences pieces (univ : Finset J) ∩ marked).card ≤ marked.card :=
    card_le_card inter_subset_right
  have keep : 7*M ≤ 8*(∑ j, (kept j).length) := by omega
  have within : (∑ j, (kept j).length) ≤ M := by omega
  obtain ⟨rawV,rawP⟩ := regularization_list_counts paths simple dPos lPos
  simp only [Fintype.card_fin] at rawV rawP
  change Fintype.card W ≤ n+M/D at rawV
  change Fintype.card J ≤ p+M/L at rawP
  have dv : 31*(M/D) ≤ 8*n := large_average_width_budget hn
    ((Nat.mul_le_mul_left 8 (le_max_left n p)).trans high.le)
  have lp : 31*(M/L) ≤ 8*p := large_average_width_budget hp
    ((Nat.mul_le_mul_left 8 (le_max_right n p)).trans high.le)
  have vertices : 31*Fintype.card W ≤ 39*n := by omega
  have rows : 31*Fintype.card J ≤ 39*p := by omega
  have keptDegree (v : W) : (occurrences (fun j => (kept j).toFinset) v).card ≤ D := by
    apply le_trans _ (degree v)
    apply card_le_card
    intro j on
    simp only [mem_occurrences,List.mem_toFinset] at on ⊢
    exact (sub j).subset on
  exact regularization_list_frozen_after_caps_with_ratios_of_mass (half := true) (k := cutoff)
    (retention := 32) (vNum := 31) (vDen := 39) (pNum := 31) (pDen := 39)
    kept keptSimple keptFree hn hp dense long (by decide) (by decide) (by decide) (by decide)
    vertices rows (fun i => (sub i).length_le.trans (length i)) keptDegree within (by omega)

/-- Short-span repair gives distinct nonempty rows for feasible literal
input at the same half cutoff. -/
theorem regularization_list_frozen_half_distinct_of_short_span_width_walks {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) cutoff)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasHalfShortSpanWidthRepair paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) cutoff ∧ M ≤ 32*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := cutoff) (retention := 32)
    paths distinct nonempty simple free two hn hp dense (by decide)
    (fun long => regularization_list_frozen_half_of_short_span_width_walks
      paths simple free two hn hp dense long repair)

end OnlineReachabilityPreservers
