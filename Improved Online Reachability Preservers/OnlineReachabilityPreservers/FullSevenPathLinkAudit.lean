import OnlineReachabilityPreservers.FullSevenLinkedCleaning

/-! A strict comparison between the two sufficient component tests. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- The long row has just one direct reverse, on its endpoints. -/
def sevenPathLinkRows : Fin 7 → List (Fin 5) :=
  ![[0,1,2,3,4], [4,0], [], [], [], [], []]

local instance decidableSevenPathLinkBefore (i : Fin 7) (x y : Fin 5) :
    Decidable (BeforeIn sevenPathLinkRows i x y) := by
  unfold BeforeIn
  infer_instance

set_option synthInstance.maxSize 2000 in
private theorem sevenPathLinkRows_step : ∀ (i : Fin 7) (x y : Fin 5),
    BeforeIn sevenPathLinkRows i x y →
      (i = 0 ∧ x < y) ∨ (i = 1 ∧ x = 4 ∧ y = 0) := by
  decide +kernel

/-- A river comparison and its first arc cannot use distinct rows. -/
theorem sevenPathLinkRows_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn sevenPathLinkRows) cutoff := by
  intro j _
  refine ⟨fun bridge => ?_⟩
  rcases sevenPathLinkRows_step _ _ _ bridge.riverStep with ⟨river, increasing⟩ | ⟨river, start, _⟩ <;>
    rcases sevenPathLinkRows_step _ _ _ (bridge.arcStep 0) with ⟨first, higher⟩ | ⟨first, four, _⟩
  · exact bridge.river_ne_arc 0 (river.trans first.symm)
  · change bridge.vertex 0 = (4 : Fin 5) at four
    rw [four] at increasing
    omega
  · change bridge.vertex 0 < bridge.vertex (Fin.succ 0) at higher
    rw [start] at higher
    omega
  · exact bridge.river_ne_arc 0 (river.trans first.symm)

private theorem sevenPathLinkRows_no_two_step (x y : Fin 5) :
    ¬ ∃ a c z, TwoStepReturnAt sevenPathLinkRows 0 a c y x z := by
  rintro ⟨a, c, z, route⟩
  rcases sevenPathLinkRows_step _ _ _ route.into_return with ⟨same, _⟩ | ⟨first, _, _⟩
  · exact route.cross.left_ne_right same
  rcases sevenPathLinkRows_step _ _ _ route.cross.step with ⟨same, _⟩ | ⟨last, _, _⟩
  · exact route.cross.right_ne_middle same.symm
  · exact route.cross.left_ne_middle (first.trans last.symm)

set_option synthInstance.maxSize 2000 in
private theorem sevenPathLinkRows_direct : ∀ x y,
    (BeforeIn sevenPathLinkRows 0 x y ∧ ∃ j, BeforeIn sevenPathLinkRows j y x) ↔
      x = (0 : Fin 5) ∧ y = 4 := by
  decide +kernel

private theorem sevenPathLinkRows_only_endpoint_link (x y : Fin 5) :
    fullSevenPathLink sevenPathLinkRows 0 x y ↔ x = 0 ∧ y = 4 := by
  simpa only [fullSevenPathLink, sevenPathLinkRows_no_two_step x y, or_false] using
    sevenPathLinkRows_direct x y

private def sevenPathLinkRows_two_edges : Arcs (Fin 5) := {(0,4), (4,0)}

private theorem sevenPathLinkRows_graph :
    fullSevenPathLinkGraph sevenPathLinkRows 0 = sevenPathLinkRows_two_edges := by
  ext e
  rcases e with ⟨x, y⟩
  change Edge (fullSevenPathLinkGraph sevenPathLinkRows 0) x y ↔ (x,y) ∈ sevenPathLinkRows_two_edges
  rw [fullSevenPathLinkGraph_edge, sevenPathLinkRows_only_endpoint_link, sevenPathLinkRows_only_endpoint_link]
  simp [sevenPathLinkRows_two_edges, and_comm]

theorem sevenPathLinkRows_widths :
    let M := ∑ i, (sevenPathLinkRows i).length
    M = 7 ∧ 4*M/5 = 5 ∧ 4*M/7 = 4 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The protected group fits width four, whereas the unlabelled
radius-two group based at the same vertex does not. -/
theorem sevenPathLinkRows_component_sizes :
    (fullSevenPathLinkComponent sevenPathLinkRows 0 0).card = 2 ∧
    (shortReturnRowComponent sevenPathLinkRows 5 0 0).card = 5 := by
  unfold fullSevenPathLinkComponent
  rw [sevenPathLinkRows_graph]
  decide +kernel

set_option maxRecDepth 8192 in
/-- Every protected group on the original rows fits at the same width. -/
theorem sevenPathLinkRows_component_room :
    ∀ i, ∀ x ∈ sevenPathLinkRows i, (fullSevenPathLinkComponent sevenPathLinkRows i x).card ≤ 4 := by
  intro i x _
  by_cases same : i = 0
  · subst i
    unfold fullSevenPathLinkComponent
    rw [sevenPathLinkRows_graph]
    exact (by decide +kernel : ∀ a : Fin 5,
      (linkedGroupComponent (sevenPathLinkRows 0).toFinset sevenPathLinkRows_two_edges a).card ≤ 4) x
  · have small : ∀ j : Fin 7, j ≠ 0 → (sevenPathLinkRows j).length ≤ 2 := by decide
    exact (card_filter_le _ _).trans ((List.toFinset_card_le _).trans ((small i same).trans (by decide)))

/-- The original protected component test gives a frozen full-seven witness. -/
theorem sevenPathLinkRows_frozen :
    ∃ n' ≤ 5, ∃ p' ≤ 7, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) 7 ∧
      7 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 7 ∧ frozenListCaps 5 7 7 clean := by
  have room : let M := ∑ i, (sevenPathLinkRows i).length
      ∀ i, ∀ x ∈ sevenPathLinkRows i, (fullSevenPathLinkComponent sevenPathLinkRows i x).card ≤ 4*M/7 := by
    dsimp only
    rw [sevenPathLinkRows_widths.2.2]
    exact sevenPathLinkRows_component_room
  have witness := regularization_list_frozen_full_seven_of_path_link_components sevenPathLinkRows
    (by decide) (sevenPathLinkRows_fullFree 7) (by decide) (by decide) (by decide) (by decide) room
  simpa only [sevenPathLinkRows_widths.1] using witness

end OnlineReachabilityPreservers.SourceAudit
