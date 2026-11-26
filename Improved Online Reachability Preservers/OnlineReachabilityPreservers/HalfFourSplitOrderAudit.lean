import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! An arrival order cannot repair one prescribed half-bridge path split. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- Uniform degree two and mean length seven halves. Only the third row exceeds the mean. -/
def splitOrderExample : Fin 4 → List (Fin 7) :=
  ![[1,6,0],[2,5],[0,2,4,6,3,1],[5,3,4]]

/-- Split the length-six row into its two consecutive halves. -/
def splitOrderExampleAfter : Fin 5 → List (Fin 7) :=
  ![[1,6,0],[2,5],[0,2,4],[6,3,1],[5,3,4]]

theorem splitOrderExample_parameters :
    (∑ i, (splitOrderExample i).length) = 14 ∧
      (∀ i, (splitOrderExample i).Nodup ∧ 1 ≤ (splitOrderExample i).length ∧
        (i ≠ 2 → (splitOrderExample i).length ≤ 3)) ∧
      (splitOrderExample 2).length = 6 ∧
      (∀ v, (occurrences (fun i => (splitOrderExample i).toFinset) v).card = 2) ∧
      splitOrderExampleAfter 0 = splitOrderExample 0 ∧ splitOrderExampleAfter 1 = splitOrderExample 1 ∧
      splitOrderExampleAfter 2 = (splitOrderExample 2).take 3 ∧
      splitOrderExampleAfter 3 = (splitOrderExample 2).drop 3 ∧
      splitOrderExampleAfter 4 = splitOrderExample 3 ∧
      (∀ i, (splitOrderExampleAfter i).Nodup ∧ 1 ≤ (splitOrderExampleAfter i).length ∧
        (splitOrderExampleAfter i).length ≤ 3) ∧
      (∀ v, (occurrences (fun i => (splitOrderExampleAfter i).toFinset) v).card = 2) := by
  decide

set_option maxRecDepth 16384 in
private theorem splitOrderExample_noHalfTwo :
    ∀ (r a : Fin 4) (u v : Fin 7), a < r →
      BeforeIn splitOrderExample r u v → BeforeIn splitOrderExample a u v → False := by
  unfold BeforeIn
  decide

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 4000000 in
private theorem splitOrderExample_noHalfThree :
    ∀ (r a b : Fin 4), b < r → r ≠ a → a ≠ b →
      ∀ (u v w : Fin 7), u ≠ w →
        BeforeIn splitOrderExample r u w →
        BeforeIn splitOrderExample a u v → BeforeIn splitOrderExample b v w → False := by
  unfold BeforeIn
  decide

private def splitOrderExample_meets (a b : Fin 4) : Prop :=
  ∃ v, v ∈ splitOrderExample a ∧ v ∈ splitOrderExample b

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem splitOrderExample_noIntersectionSquare :
    ∀ (r a b c : Fin 4), r ≠ a → r ≠ b → r ≠ c → a ≠ b → a ≠ c → b ≠ c →
      splitOrderExample_meets r a → splitOrderExample_meets a b →
      splitOrderExample_meets b c → splitOrderExample_meets c r → False := by
  unfold splitOrderExample_meets
  decide

/-- The original arrivals exclude every half-bridge through size four. -/
theorem splitOrderExample_halfFree : HalfBridgeFree (BeforeIn splitOrderExample) 4 := by
  intro d fits b order
  have bound : d ≤ 2 := by omega
  have distinctArcs {i j : Fin (d+1)} (different : i ≠ j) : b.arc i ≠ b.arc j :=
    fun eq => different (b.distinctArcs eq)
  have distinctCorners {i j : Fin (d+2)} (different : i ≠ j) : b.vertex i ≠ b.vertex j :=
    fun eq => different (b.distinctVertices eq)
  interval_cases d
  · exact splitOrderExample_noHalfTwo _ _ _ _ order b.riverStep (b.arcStep 0)
  · exact splitOrderExample_noHalfThree _ _ _ order (b.river_ne_arc 0) (distinctArcs (by decide)) _ _ _
      (distinctCorners (by decide)) b.riverStep (b.arcStep 0) (b.arcStep 1)
  · exact splitOrderExample_noIntersectionSquare _ _ _ _ (b.river_ne_arc 0) (b.river_ne_arc 1) (b.river_ne_arc 2)
      (distinctArcs (by decide)) (distinctArcs (by decide)) (distinctArcs (by decide))
      ⟨_,b.riverStep.1,(b.arcStep 0).1⟩ ⟨_,(b.arcStep 0).2.1,(b.arcStep 1).1⟩
      ⟨_,(b.arcStep 1).2.1,(b.arcStep 2).1⟩ ⟨_,(b.arcStep 2).2.1,b.riverStep.2.1⟩

private def splitOrderExample_three : Bridge (BeforeIn splitOrderExampleAfter) 1 := by
  let vertex : Fin 3 → Fin 7 := ![2,5,4]
  let arc : Fin 2 → Fin 5 := ![1,4]
  have corners : ∀ i j, vertex i = vertex j → i = j := by decide
  have labels : ∀ i j, arc i = arc j → i = j := by decide
  refine ⟨vertex,arc,2,fun {_ _} => corners _ _,fun {_ _} => labels _ _,by decide,?_,?_⟩
  · unfold BeforeIn
    decide
  · unfold BeforeIn
    decide

private def splitOrderExample_four : Bridge (BeforeIn splitOrderExampleAfter) 2 := by
  let vertex : Fin 4 → Fin 7 := ![3,1,0,4]
  let arc : Fin 3 → Fin 5 := ![3,0,2]
  have corners : ∀ i j, vertex i = vertex j → i = j := by decide
  have labels : ∀ i j, arc i = arc j → i = j := by decide
  refine ⟨vertex,arc,4,fun {_ _} => corners _ _,fun {_ _} => labels _ _,by decide,?_,?_⟩
  · unfold BeforeIn
    decide
  · unfold BeforeIn
    decide

/-- The two split pieces and the unchanged rows admit no half-four-free
arrival order. The 3-bridge and 4-bridge force opposite relative orders. -/
theorem splitOrderExample_no_reordering (order : Fin 5 ≃ Fin 5) :
    ¬ HalfBridgeFree (BeforeIn (fun i => splitOrderExampleAfter (order i))) 4 := by
  intro free
  have move (i : Fin 5) (u v : Fin 7) (step : BeforeIn splitOrderExampleAfter i u v) :
      BeforeIn (fun j => splitOrderExampleAfter (order j)) (order.symm i) u v := by
    simpa only [BeforeIn,Equiv.apply_symm_apply] using step
  have separate : order.symm 2 ≠ order.symm 4 := fun same =>
    (by decide : (2 : Fin 5) ≠ 4) (order.symm.injective same)
  rcases lt_or_gt_of_ne separate with forward | backward
  · exact free (k := 2) (by decide)
      (splitOrderExample_four.mapPaths order.symm order.symm.injective move) forward
  · exact free (k := 1) (by decide)
      (splitOrderExample_three.mapPaths order.symm order.symm.injective move) backward

/-- The example's budgets admit a separate cleaned witness. -/
theorem splitOrderExample_cleans :
    ∃ n' ≤ 7, ∃ p' ≤ 4, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) 4 ∧
      14 ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 14 ∧ frozenListCaps 7 4 14 clean := by
  exact full_frozen_cleaning_sparse_four (by decide) (by decide) (by decide) (by decide) (by decide)

end OnlineReachabilityPreservers.SourceAudit
