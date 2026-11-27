import OnlineReachabilityPreservers.BackwardCopyReturns
import OnlineReachabilityPreservers.FrozenCappedRectangle
import OnlineReachabilityPreservers.HalfReturnBoundaryCover

/-! Check the degree and width returns on retained width pieces. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

/-- Keep a parent incidence exactly when one of its supplied pieces
contains that vertex. Comparisons use the original parent order. -/
def parentsRestrictedToPieces {I J V : Type*} [DecidableEq I] [DecidableEq V] [Fintype J]
    (rows : I → List V) (pieces : J → List V) (parent : J → I) (i : I) : List V :=
  (rows i).filter fun v => decide (∃ j, parent j = i ∧ v ∈ pieces j)

/-- The retained parents are rowwise sublists of the original parents. -/
theorem parentsRestrictedToPieces_sublist {I J V : Type*} [DecidableEq I] [DecidableEq V] [Fintype J]
    (rows : I → List V) (pieces : J → List V) (parent : J → I) (i : I) :
    (parentsRestrictedToPieces rows pieces parent i).Sublist (rows i) := List.filter_sublist

/-- Each retained piece stays a sublist of its retained parent. -/
theorem sublist_parentsRestrictedToPieces {I J V : Type*} [DecidableEq I] [DecidableEq V] [Fintype J]
    {rows : I → List V} {pieces : J → List V} {parent : J → I} {j : J}
    (sub : (pieces j).Sublist (rows (parent j))) :
    (pieces j).Sublist (parentsRestrictedToPieces rows pieces parent (parent j)) := by
  let select (v : V) := decide (∃ t, parent t = parent j ∧ v ∈ pieces t)
  have same : (pieces j).filter select = pieces j :=
    List.filter_eq_self.mpr (fun v on => decide_eq_true ⟨j,rfl,on⟩)
  change (pieces j).Sublist ((rows (parent j)).filter select)
  rw [← same]
  exact sub.filter _

open scoped Sigma.Lex

/-- Test the earlier-degree-copy return on the parents reconstructed
from the retained width pieces. The width test only sees comparisons
in those pieces and parent comparisons of their two endpoints. -/
theorem halfBridgeFree_width_sublists_of_supported_returns {n p cutoff D L : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff)
    (pieces : ListBlockIndex (splitListVertices paths D) L → List (ListVertexBlockIndex paths D))
    (sub : ∀ j, (pieces j).Sublist (listRegularizedPaths paths D L j))
    (degreeSafe : NoShortBackwardCopyReturnIn
      (parentsRestrictedToPieces (splitListVertices paths D) pieces Sigma.fst) (cutoff-3))
    (widthSafe : NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph pieces) id
      (splitListVertices paths D) pieces Sigma.fst (cutoff-3)) :
    HalfBridgeFree (Before pieces) cutoff := by
  let copies := splitListVertices paths D
  let J := ListBlockIndex copies L
  let parent (j : J) := j.fst
  let kept := parentsRestrictedToPieces copies pieces parent
  have copiedSimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have parentSub (i : Fin p) : (kept i).Sublist (copies i) :=
    parentsRestrictedToPieces_sublist copies pieces parent i
  have pieceSub (j : J) : (pieces j).Sublist (copies (parent j)) := (sub j).trans List.filter_sublist
  have support (j : J) : (pieces j).Sublist (kept (parent j)) := sublist_parentsRestrictedToPieces (pieceSub j)
  have keptFree : HalfBridgeFree (Before kept) cutoff :=
    copied_subrows_halfFree_of_noShortBackwardCopyReturn paths simple kept parentSub free degreeSafe
  refine halfBridgeFree_of_disjoint_split_of_no_backward_returns (listPiecePrecedenceGraph pieces) id keptFree parent
    (block_parent_mono _ L) (fun {j _ _} step => listBefore_of_sublist
      (paths := kept ∘ parent) ((parentSub (parent j)).nodup (copiedSimple (parent j))) (support j) step)
    (fun {j _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨j,step⟩) ?_ ?_
  · intro i j v different same first last
    exact splitListPaths_disjoint different same ((sub i).subset first) ((sub j).subset last)
  · intro i j x y different same first last step back
    have forward : Before copies (parent i) x y := listBefore_of_sublist
      (copiedSimple (parent i)) (parentSub (parent i)) step
    exact widthSafe different same first last forward back

open Finset

/-- The rectangle supports the two return tests after erasure and pays
for the erasure, peeling at the original averages, and retention. -/
def HasHalfReturnErasureWithinRectangle {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff retention : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  ∃ A : Finset (ListVertexBlockIndex paths D), A.card ≤ n ∧
    ∃ B : Finset (ListBlockIndex copies L), B.card ≤ p ∧
      ∃ deleted : Finset (ListBlockIndex copies L × ListVertexBlockIndex paths D),
        let kept := erasePieceIncidences (listPiecesInRectangle raw A B) deleted
        NoShortBackwardCopyReturnIn (parentsRestrictedToPieces copies kept Sigma.fst) (cutoff-3) ∧
        NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph kept) id copies kept Sigma.fst (cutoff-3) ∧
        (M:ℝ)/retention+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+deleted.card ≤
          ((∑ j ∈ B, ((raw j).toFinset ∩ A).card : ℕ):ℝ)

/-- Test the two short returns after restricting to the selected supports
and erasing the certified incidences. The witness keeps the original
half cutoff, both original budgets, and all four original-average caps. -/
theorem regularization_list_frozen_half_of_supported_width_erasure {n p cutoff retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (ret : 0 < retention) (certificate : HasHalfReturnErasureWithinRectangle paths cutoff retention) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) cutoff ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let W := ListVertexBlockIndex paths D
  let J := ListBlockIndex copies L
  let raw : J → List W := listRegularizedPaths paths D L
  obtain ⟨A,va,B,pa,deleted,degreeSafe,widthSafe,budget⟩ := certificate
  let masked := listPiecesInRectangle raw A B
  let kept := erasePieceIncidences masked deleted
  have maskSub (j : J) : (masked j).Sublist (raw j) := by
    unfold masked listPiecesInRectangle
    split
    · exact List.filter_sublist
    · exact List.nil_sublist _
  have maskSimple (j : J) : (masked j).Nodup :=
    (maskSub j).nodup (listRegularizedPaths_simple paths simple D L j)
  have erasedSub (j : J) : (kept j).Sublist (raw j) := (erasePieceIncidences_sublist masked deleted j).trans (maskSub j)
  have erasedSimple (j : J) : (kept j).Nodup := (erasePieceIncidences_sublist masked deleted j).nodup (maskSimple j)
  have keptFree : HalfBridgeFree (Before kept) cutoff :=
    halfBridgeFree_width_sublists_of_supported_returns paths simple free kept erasedSub degreeSafe widthSafe
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have keptDegree (v : W) : (occurrences (fun j => (kept j).toFinset) v).card ≤ D := by
    refine (card_le_card ?_).trans (degree v)
    intro j on
    have present := (mem_occurrences (marks := fun i : J => (kept i).toFinset)).mp on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((erasedSub j).subset (List.mem_toFinset.mp present)))
  have rawRectangle : (∑ j ∈ B, (masked j).length) = ∑ j ∈ B, ((raw j).toFinset ∩ A).card := by
    refine sum_congr rfl fun j active => ?_
    rw [← List.toFinset_card_of_nodup (maskSimple j)]
    congr 1
    ext v
    simp [masked,listPiecesInRectangle,active]
  have inA (j : J) (active : j ∈ B) : (kept j).toFinset ⊆ A := by
    intro v on
    have present := (erasePieceIncidences_sublist masked deleted j).subset (List.mem_toFinset.mp on)
    have mem : v ∈ raw j ∧ v ∈ A := by simpa [masked,listPiecesInRectangle,active] using present
    exact mem.2
  have erasedRectangle : (∑ j ∈ B, (kept j).length) = ∑ j ∈ B, ((kept j).toFinset ∩ A).card := by
    refine sum_congr rfl fun j active => ?_
    rw [inter_eq_left.mpr (inA j active),List.toFinset_card_of_nodup (erasedSimple j)]
  have lost := erasePieceIncidences_mass_add_loss maskSimple B deleted
  change (∑ j ∈ B, (kept j).length)+(pieceIncidences masked B ∩ deleted).card = _ at lost
  rw [rawRectangle,erasedRectangle] at lost
  have cost : (pieceIncidences masked B ∩ deleted).card ≤ deleted.card := card_le_card inter_subset_right
  have enoughAfter : (∑ j ∈ B, ((raw j).toFinset ∩ A).card) ≤
      (∑ j ∈ B, ((kept j).toFinset ∩ A).card)+deleted.card := by omega
  apply regularization_list_frozen_of_capped_rectangle (half := true) kept erasedSimple keptFree
    hn hp dense long ret (fun i => (erasedSub i).length_le.trans (length i)) keptDegree
    ((sum_le_sum fun i _ => (erasedSub i).length_le).trans mass.le) A B va pa
  have paid : ((∑ j ∈ B, ((raw j).toFinset ∩ A).card : ℕ):ℝ) ≤
      ((∑ j ∈ B, ((kept j).toFinset ∩ A).card : ℕ):ℝ)+deleted.card := by exact_mod_cast enoughAfter
  change (M:ℝ)/retention+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+deleted.card ≤
    ((∑ j ∈ B, ((raw j).toFinset ∩ A).card : ℕ):ℝ) at budget
  change (M:ℝ)/retention+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card ≤
    ((∑ j ∈ B, ((kept j).toFinset ∩ A).card : ℕ):ℝ)
  linarith only [paid,budget]

/-- A feasible literal input has a distinct nonempty witness under the
same supported return and budget certificate if the retention factor is
at least eight. -/
theorem regularization_list_frozen_half_distinct_of_supported_width_erasure {n p cutoff retention : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) cutoff)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (ret : 8 ≤ retention) (certificate : HasHalfReturnErasureWithinRectangle paths cutoff retention) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) cutoff ∧ M ≤ retention*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := cutoff) (retention := retention)
    paths distinct nonempty simple free two hn hp dense ret
    (fun long => regularization_list_frozen_half_of_supported_width_erasure paths simple free hn hp dense long
      (by omega) certificate)

end OnlineReachabilityPreservers
