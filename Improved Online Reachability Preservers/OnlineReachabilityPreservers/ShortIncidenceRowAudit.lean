import OnlineReachabilityPreservers.IncidenceConnectionSearch
import OnlineReachabilityPreservers.RainbowListSearch
import OnlineReachabilityPreservers.ShortIncidenceDegreePacking

/-! A long deletion component can separate into width-bounded short groups. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- Reverse triples on the long row, with a corridor joining the two
triples through their private endpoints. -/
def shortIncidenceCorridorRows : Fin 18 → List (Fin 9) :=
  ![[0,1,2,3,4,5],[2,1,0,6],[5,4,3,8],[6,7],[7,8],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem shortIncidenceCorridorRows_widths :
    (∀ i, (shortIncidenceCorridorRows i).Nodup) ∧
    (let M := ∑ i, (shortIncidenceCorridorRows i).length
     M = 18 ∧ 4*M/9 = 8 ∧ 4*M/18 = 4 ∧ 4 < (shortIncidenceCorridorRows 0).length) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private theorem shortIncidenceCorridor_no_rainbow : ∀ (fuel : Fin 4) (river : Fin 18) (x y : Fin 9),
    BeforeIn shortIncidenceCorridorRows river x y →
    rainbowSearch shortIncidenceCorridorRows fuel.val
      ((List.finRange 18).filter fun i => decide (i ≠ river)) x y = false := by
  unfold BeforeIn
  decide

/-- No bridge through size four is present before grouping. -/
theorem shortIncidenceCorridorRows_fullFree : BridgeFree (BeforeIn shortIncidenceCorridorRows) 4 := by
  intro d small
  refine ⟨fun bridge => ?_⟩
  let fuel : Fin 4 := ⟨d+1,by omega⟩
  let allowed := (List.finRange 18).filter fun i => decide (i ≠ bridge.river)
  have present (i : Fin (d+1)) : bridge.arc i ∈ allowed :=
    List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true (bridge.river_ne_arc i).symm⟩
  have found := rainbowSearch_of_chain shortIncidenceCorridorRows bridge.vertex bridge.arc
    bridge.distinctArcs allowed present bridge.arcStep
  have absent := shortIncidenceCorridor_no_rainbow fuel bridge.river _ _ bridge.riverStep
  change rainbowSearch shortIncidenceCorridorRows (d+1) allowed
    (bridge.vertex 0) (bridge.vertex (Fin.last (d+1))) = false at absent
  rw [absent] at found
  contradiction

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
/-- The corridor puts all six neighbors of the first row in one
deleted-row component, too large for the original path width four. -/
theorem shortIncidenceCorridorRows_whole_group :
    (incidenceRowDeletionGroup shortIncidenceCorridorRows 0 0).card = 6 := by
  rw [← incidenceRowDeletionGroupBySearch_eq]
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private theorem shortIncidenceCorridor_search_sizes : ∀ (i : Fin 18) (x : Fin 9),
    (shortIncidenceRowGroupBySearch shortIncidenceCorridorRows 2 i x).card ≤ 3 := by decide

/-- Every radius-two neighbor group has at most three vertices. -/
theorem shortIncidenceCorridorRows_short_groups (i : Fin 18) (x : Fin 9) :
    (shortIncidenceRowGroup shortIncidenceCorridorRows 2 i x).card ≤ 3 := by
  rw [← shortIncidenceRowGroupBySearch_eq]
  exact shortIncidenceCorridor_search_sizes i x

private theorem shortIncidenceCorridor_transposed_marks (x : Fin 9) :
    (incidenceTranspose shortIncidenceCorridorRows x).toFinset =
      occurrences (fun i => (shortIncidenceCorridorRows i).toFinset) x := by
  ext i
  simp only [List.mem_toFinset,mem_incidenceTranspose,mem_occurrences]

private theorem shortIncidenceCorridor_degree_bound : ∀ x : Fin 9,
    ((incidenceTranspose shortIncidenceCorridorRows x).toFinset).card ≤ 2 := by
  simp only [shortIncidenceCorridor_transposed_marks]
  decide

private theorem shortIncidenceCorridor_degree_groups (v : Fin 9) (i : Fin 18) :
    (shortIncidenceVertexGroup shortIncidenceCorridorRows 2 v i).card ≤ 2 := by
  let transpose := incidenceTranspose shortIncidenceCorridorRows
  have retain : shortIncidenceRowGroup transpose 2 v i ⊆ (transpose v).toFinset := by
    intro j present
    have member := shortIncidenceRowGroup_subset 2 v i present
    exact List.mem_toFinset.mpr (mem_incidenceRowDeletionGroup.mp member).1
  exact (card_le_card retain).trans (shortIncidenceCorridor_degree_bound v)

/-- The example meets both finite-cutoff tests at the actual original
widths. The indexed full witness uses both budgets and all four caps. -/
theorem shortIncidenceCorridorRows_frozen :
    ∃ n' ≤ 9, ∃ p' ≤ 18, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) 4 ∧
      18 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 18 ∧ frozenListCaps 9 18 18 clean := by
  have mass := shortIncidenceCorridorRows_widths.2.1
  have dense : 9 ≤ ∑ i, (shortIncidenceCorridorRows i).length := by rw [mass]; decide
  have result := regularization_list_frozen_of_short_incidence_group_rooms (half := false)
    (k := 4) shortIncidenceCorridorRows shortIncidenceCorridorRows_widths.1 shortIncidenceCorridorRows_fullFree
    (by decide) (by decide) dense mass.ge
    (by
      dsimp only
      rw [mass]
      intro x i _
      exact (shortIncidenceCorridor_degree_groups x i).trans (by decide))
    (by
      dsimp only
      rw [mass]
      intro i x _
      exact (shortIncidenceCorridorRows_short_groups i x).trans (by decide))
  simpa only [mass,localOrderAdmissible,Bool.false_eq_true,ite_false] using result

end OnlineReachabilityPreservers.SourceAudit
