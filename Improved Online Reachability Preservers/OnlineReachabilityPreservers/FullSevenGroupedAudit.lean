import OnlineReachabilityPreservers.ShortReturnStandardCleaning

/-! An example where grouping a two-step return succeeds at the
original widths even though the contiguous test fails. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

local instance decidableGroupedBefore {I V : Type*} [DecidableEq V]
    (rows : I → List V) (i : I) (x y : V) : Decidable (BeforeIn rows i x y) := by
  unfold BeforeIn
  infer_instance

/-- The reverse path of length two crosses the width-four cut in row zero. -/
def sevenGroupedRows : Fin 9 → List (Fin 6) :=
  ![[0,1,2,3,4], [4,5], [5,0], [], [], [], [], [], []]

theorem sevenGroupedRows_widths :
    let M := ∑ i, (sevenGroupedRows i).length
    M = 9 ∧ 4*M/6 = 6 ∧ 4*M/9 = 4 := by decide

private theorem sevenGroupedRows_step (i : Fin 9) (x y : Fin 6)
    (step : BeforeIn sevenGroupedRows i x y) :
    (i = 0 ∧ x < y ∧ y < 5) ∨ (i = 1 ∧ x = 4 ∧ y = 5) ∨ (i = 2 ∧ x = 5 ∧ y = 0) := by
  have checked : ∀ (i : Fin 9) (x y : Fin 6), BeforeIn sevenGroupedRows i x y →
      (i = 0 ∧ x < y ∧ y < 5) ∨ (i = 1 ∧ x = 4 ∧ y = 5) ∨ (i = 2 ∧ x = 5 ∧ y = 0) := by decide
  exact checked i x y step

/-- Each possible river has a corner that excludes a chain on the other rows. -/
theorem sevenGroupedRows_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn sevenGroupedRows) cutoff := by
  intro j _
  refine ⟨fun b => ?_⟩
  have shape := sevenGroupedRows_step _ _ _ b.riverStep
  have first : BeforeIn sevenGroupedRows (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
  have last : BeforeIn sevenGroupedRows (b.arc (Fin.last j))
      (b.vertex (Fin.last j).castSucc) (b.vertex (Fin.last (j+1))) := by
    simpa only [Fin.succ_last] using b.arcStep (Fin.last j)
  rcases shape with ⟨river, increasing, upper⟩ | ⟨river, _, finish⟩ | ⟨river, start, _⟩
  · rcases sevenGroupedRows_step _ _ _ first with ⟨same, _, _⟩ | ⟨_, four, _⟩ | ⟨_, five, _⟩
    · exact b.river_ne_arc 0 (river.trans same.symm)
    · rw [four] at increasing
      omega
    · rw [five] at increasing
      omega
  · rcases sevenGroupedRows_step _ _ _ last with ⟨_, _, upper⟩ | ⟨same, _, _⟩ | ⟨_, _, zero⟩
    · rw [finish] at upper
      exact (lt_irrefl _ upper)
    · exact b.river_ne_arc _ (river.trans same.symm)
    · exact (by decide : (5 : Fin 6) ≠ 0) (finish.symm.trans zero)
  · rcases sevenGroupedRows_step _ _ _ first with ⟨_, increasing, upper⟩ | ⟨_, four, _⟩ | ⟨same, _, _⟩
    · rw [start] at increasing
      exact (lt_asymm increasing upper)
    · exact (by decide : (5 : Fin 6) ≠ 4) (start.symm.trans four)
    · exact b.river_ne_arc 0 (river.trans same.symm)

private abbrev ExampleCopy := ListVertexBlockIndex sevenGroupedRows 6
private abbrev ExamplePieces := ListBlockIndex (splitListVertices sevenGroupedRows 6) 4

private def exampleCopyZero : ExampleCopy := ⟨0, ⟨0, by decide⟩⟩
private def exampleCopyFour : ExampleCopy := ⟨4, ⟨0, by decide⟩⟩
private def exampleCopyFive : ExampleCopy := ⟨5, ⟨0, by decide⟩⟩

/-- The return 4 → 5 → 0 still crosses the cut on the actual copied pieces. -/
theorem sevenGroupedRows_contiguous_test_fails :
    ¬ NoShortReturnAcrossCopiedWidthCuts sevenGroupedRows 6 4 5 := by
  intro safe
  let copies := splitListVertices sevenGroupedRows 6
  let pieces := listRegularizedPaths sevenGroupedRows 6 4
  let graph := listPiecePrecedenceGraph pieces
  let first : ExamplePieces := ⟨1, ⟨0, by decide⟩⟩
  let last : ExamplePieces := ⟨2, ⟨0, by decide⟩⟩
  have forward : BeforeIn copies 0 exampleCopyZero exampleCopyFour := by decide
  have apart : (copies 0).idxOf exampleCopyZero / 4 ≠ (copies 0).idxOf exampleCopyFour / 4 := by decide
  have beforeFirst : BeforeIn pieces first exampleCopyFour exampleCopyFive :=
    ⟨by decide, by decide, by decide⟩
  have beforeLast : BeforeIn pieces last exampleCopyFive exampleCopyZero :=
    ⟨by decide, by decide, by decide⟩
  have lastEdge : Edge graph exampleCopyFive exampleCopyZero :=
    listPiecePrecedenceGraph_edge.mpr ⟨last, beforeLast⟩
  have firstEdge : Edge graph exampleCopyFour exampleCopyFive :=
    listPiecePrecedenceGraph_edge.mpr ⟨first, beforeFirst⟩
  have one : exampleCopyFive ∈ reachIn graph exampleCopyZero 1 :=
    reachIn_succ.mpr (Or.inr ⟨exampleCopyZero, lastEdge, target_mem_reachIn _ _ 0⟩)
  have two : exampleCopyFour ∈ reachIn graph exampleCopyZero 2 :=
    reachIn_succ.mpr (Or.inr ⟨exampleCopyFive, firstEdge, one⟩)
  exact safe forward apart two

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
/-- At radius two, all original row components fit the width four. -/
theorem sevenGroupedRows_component_room :
    ∀ i, ∀ x ∈ sevenGroupedRows i, (shortReturnRowComponent sevenGroupedRows 5 i x).card ≤ 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
/-- At radius four, the original component of vertex zero contains the
whole five-vertex row and exceeds the width four. -/
theorem sevenGroupedRows_four_step_component :
    (shortReturnRowComponent sevenGroupedRows 7 0 0).card = 5 := by
  decide +kernel

/-- Grouping gives a full-seven witness at the same widths and budgets. -/
theorem sevenGroupedRows_frozen :
    ∃ n' ≤ 6, ∃ p' ≤ 9, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) 7 ∧
      9 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 9 ∧ frozenListCaps 6 9 9 clean := by
  have room : let M := ∑ i, (sevenGroupedRows i).length
      ∀ i, ∀ x ∈ sevenGroupedRows i, (shortReturnRowComponent sevenGroupedRows 5 i x).card ≤ 4*M/9 := by
    dsimp only
    rw [sevenGroupedRows_widths.2.2]
    exact sevenGroupedRows_component_room
  have witness := regularization_list_frozen_full_seven_of_two_step_components sevenGroupedRows
    (by decide) (sevenGroupedRows_fullFree 7) (by decide) (by decide) (by decide) (by decide) room
  simpa only [sevenGroupedRows_widths.1] using witness

end OnlineReachabilityPreservers.SourceAudit
