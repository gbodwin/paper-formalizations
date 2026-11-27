import OnlineReachabilityPreservers.FullSevenWidthCleaning
import OnlineReachabilityPreservers.RainbowListSearch

/-! A radius-two check can miss a new size-eight bridge. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

local instance decidableEightBefore {I : Type*} (rows : I → List (Fin 8))
    (i : I) (x y : Fin 8) : Decidable (BeforeIn rows i x y) := by
  unfold BeforeIn
  infer_instance

/-- The long row supplies two separated steps of the terminal detour. -/
def eightSplitRows : Fin 7 → List (Fin 8) :=
  ![[4,5,0,1], [1,2], [2,3], [3,4], [5,6], [6,7], [0,7]]

/-- Split the long row at its midpoint and retain all other rows. -/
def eightSplitPieces : Fin 8 → List (Fin 8) :=
  ![[4,5], [0,1], [1,2], [2,3], [3,4], [5,6], [6,7], [0,7]]

def eightSplitParent : Fin 8 → Fin 7 := ![0,0,1,2,3,4,5,6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3500000 in
set_option synthInstance.maxSize 2000 in
private theorem eightSplitRows_search : ∀ (fuel row : Fin 7) (x y : Fin 8),
    BeforeIn eightSplitRows row x y →
    rainbowSearch eightSplitRows fuel.val ((List.finRange 7).filter (fun i => decide (i ≠ row))) x y = false := by
  decide +kernel

/-- The original family excludes full bridges at every size. -/
theorem eightSplitRows_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn eightSplitRows) cutoff :=
  fun d _ => isEmpty_bridge_of_rainbowSearch eightSplitRows eightSplitRows_search d

set_option synthInstance.maxSize 2000 in
/-- The original mass is sixteen, each vertex has degree two and only
the length-four row is longer than the original mean of sixteen sevenths. -/
theorem eightSplitRows_parameters :
    (∑ i, (eightSplitRows i).length) = 16 ∧
    (∀ v, (occurrences (fun i => (eightSplitRows i).toFinset) v).card = 2) ∧
    (eightSplitRows 0).length = 4 ∧
    (∀ i, i ≠ 0 → (eightSplitRows i).length = 2) := by decide

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 2000 in
/-- The original simple rows have unique intersections. The split is
disjoint and covers all incidences. -/
theorem eightSplitPieces_spec :
    (∀ i, (eightSplitRows i).Nodup) ∧
    (∀ (i j : Fin 7), i ≠ j → ∀ x y : Fin 8, x ∈ eightSplitRows i → x ∈ eightSplitRows j →
      y ∈ eightSplitRows i → y ∈ eightSplitRows j → x = y) ∧
    (∀ i, (eightSplitPieces i).Sublist (eightSplitRows (eightSplitParent i))) ∧
    (∀ i j x, i ≠ j → eightSplitParent i = eightSplitParent j →
      x ∈ eightSplitPieces i → x ∈ eightSplitPieces j → False) ∧
    (∀ i x, x ∈ eightSplitRows i → ∃ j, eightSplitParent j = i ∧ x ∈ eightSplitPieces j) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxSize 3000 in
/-- No return of at most two steps crosses the midpoint on the graph
of the actual pieces. -/
theorem eightSplitPieces_radius_two :
    NoShortBackwardReturnAcrossPieces (listPiecePrecedenceGraph eightSplitPieces) id
      eightSplitRows eightSplitPieces eightSplitParent 2 := by
  unfold NoShortBackwardReturnAcrossPieces
  decide +kernel

/-- The chain 1 → 2 → 3 → 4 crosses the split against the original
order of the long row. -/
theorem eightSplitPieces_crossed_three_step :
    ¬ NoCrossedThreeStepReturn eightSplitRows eightSplitPieces eightSplitParent := by
  intro safe
  let labels : Fin 4 → Fin 7 := ![eightSplitParent 2, eightSplitParent 3, eightSplitParent 4, eightSplitParent 1]
  have distinct : ∀ i j, labels i = labels j → i = j := by decide
  exact safe (i := 1) (j := 0) (a := 2) (c := 3) (d := 4) (x := 1) (y := 4) (z := 2) (w := 3)
    (by decide) (by decide) (fun {_ _} => distinct _ _) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- After the split, the seven consecutive steps are on distinct
pieces and give a bridge against the terminal-to-terminal row. -/
theorem eightSplitPieces_creates_full_eight : Nonempty (Bridge (BeforeIn eightSplitPieces) 6) := by
  let vertices : Fin 8 → Fin 8 := id
  let arcs : Fin 7 → Fin 8 := ![1,2,3,4,0,5,6]
  have arcDistinct : ∀ i j, arcs i = arcs j → i = j := by decide
  have riverDistinct : ∀ i, (7 : Fin 8) ≠ arcs i := by decide
  have follows : ∀ i, BeforeIn eightSplitPieces (arcs i) (vertices i.castSucc) (vertices i.succ) := by decide
  exact ⟨⟨vertices, arcs, 7, Function.injective_id, fun {_ _} => arcDistinct _ _, riverDistinct,
    by decide, follows⟩⟩

end OnlineReachabilityPreservers.SourceAudit
