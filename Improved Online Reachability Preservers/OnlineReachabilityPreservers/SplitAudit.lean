import OnlineReachabilityPreservers.Bridges
import Mathlib.Data.Fin.VecNotation

/-! A cyclic example for the printed splitting step and the cited consecutive-edge overlay. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

def splitExample : Fin 3 → List (Fin 4) := ![[0, 1, 2, 3], [3, 0], [2, 1]]

def splitExampleAfter : Fin 4 → List (Fin 4) := ![[0, 1], [2, 3], [3, 0], [2, 1]]

def BeforeIn {I V : Type*} [DecidableEq V] (paths : I → List V) (i : I) (u v : V) : Prop :=
  u ∈ paths i ∧ v ∈ paths i ∧ (paths i).idxOf u < (paths i).idxOf v

private def hasBridge (k : ℕ) : Prop :=
  ∃ (v : Fin (k + 2) → Fin 4) (a : Fin (k + 1) → Fin 3) (r : Fin 3),
    (∀ i j, v i = v j → i = j) ∧ (∀ i j, a i = a j → i = j) ∧
    (∀ i, r ≠ a i) ∧ BeforeIn splitExample r (v 0) (v (Fin.last (k + 1))) ∧
    (∀ i, BeforeIn splitExample (a i) (v i.castSucc) (v i.succ))

private theorem no_original_two :
    ∀ (x y : Fin 4) (a r : Fin 3), r ≠ a →
      BeforeIn splitExample a x y → BeforeIn splitExample r x y → False := by
  unfold BeforeIn
  decide

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 1000000 in
private theorem no_original_three :
    ∀ (x y z : Fin 4) (a b r : Fin 3), a ≠ b → r ≠ a → r ≠ b →
      BeforeIn splitExample a x y → BeforeIn splitExample b y z →
      BeforeIn splitExample r x z → False := by
  unfold BeforeIn
  decide

private theorem absent_below_four (k : ℕ) (h : k ≤ 1) : ¬ hasBridge k := by
  interval_cases k
  · rintro ⟨v, a, r, _, _, hne, hr, ha⟩
    exact no_original_two (v 0) (v 1) (a 0) r (hne 0) (ha 0) hr
  · rintro ⟨v, a, r, _, hinj, hne, hr, ha⟩
    have h01 : a 0 ≠ a 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (hinj 0 1 he)
    exact no_original_three (v 0) (v 1) (v 2) (a 0) (a 1) r h01 (hne 0) (hne 1)
      (ha 0) (ha 1) hr

private def pathIndices {I V : Type*} {k : ℕ} {before : I → V → V → Prop} (b : Bridge before k) :
    Fin (k + 2) → I := Fin.cases b.river b.arc

private theorem pathIndices_injective {I V : Type*} {k : ℕ} {before : I → V → V → Prop} (b : Bridge before k) :
    Function.Injective (pathIndices b) := by
  intro i j h
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rfl
  · exact (b.river_ne_arc j h).elim
  · exact (b.river_ne_arc i h.symm).elim
  · exact congrArg Fin.succ (b.distinctArcs h)

/-- A bridge of size `k + 2` requires that many distinct paths. -/
theorem bridge_path_count_le {I V : Type*} [Fintype I] {k : ℕ} {before : I → V → V → Prop}
    (b : Bridge before k) : k + 2 ≤ Fintype.card I := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (pathIndices b) (pathIndices_injective b)

/-- The original three paths have no bridge of any size. -/
theorem splitExample_bridge_free (k : ℕ) : IsEmpty (Bridge (BeforeIn splitExample) k) := by
  refine ⟨fun b => ?_⟩
  have hcard := bridge_path_count_le b
  simp only [Fintype.card_fin] at hcard
  exact absent_below_four k (by omega)
    ⟨b.vertex, b.arc, b.river, fun _ _ h => b.distinctVertices h, fun _ _ h => b.distinctArcs h,
      b.river_ne_arc, b.riverStep, b.arcStep⟩

/-- The two consecutive halves can have a forbidden bridge with the last arc earlier than the river. -/
theorem splitExample_creates_half_four :
    ∃ b : Bridge (BeforeIn splitExampleAfter) 2, b.arc (Fin.last 2) < b.river := by
  let v : Fin 4 → Fin 4 := ![2, 3, 0, 1]
  let a : Fin 3 → Fin 4 := ![1, 2, 0]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (3 : Fin 4) ≠ a i := by decide
  have hs : BeforeIn splitExampleAfter 3 (v 0) (v (Fin.last 3)) := by
    unfold BeforeIn
    decide
  have ht : ∀ i, BeforeIn splitExampleAfter (a i) (v i.castSucc) (v i.succ) := by
    unfold BeforeIn
    decide
  exact ⟨⟨v, a, 3, fun {_ _} => hv _ _, fun {_ _} => ha _ _, hr, hs, ht⟩, by change (0 : Fin 4) < 3; decide⟩

/-- The consecutive-edge overlay of the three paths in the split example. -/
def splitExampleOverlay : Arcs (Fin 4) :=
  (univ : Finset (Fin 3)).biUnion fun i =>
    ((splitExample i).zip ((splitExample i).drop 1)).toFinset

def splitExampleDemands : List (Fin 4 × Fin 4) :=
  (List.finRange 3).map fun i => ((splitExample i).headD 0,(splitExample i).getLastD 0)

private def cycleWithoutChord : Arcs (Fin 4) := {(0,1),(1,2),(2,3),(3,0)}

private theorem splitExampleOverlay_eq :
    splitExampleOverlay = {(0,1),(1,2),(2,3),(3,0),(2,1)} := by decide

/-- The consecutive-edge construction in Lemma 40 of Bridge Girth can lose
an edge even for a full bridge-free system of simple paths. -/
theorem lemma14_overlay_counterexample :
    (∀ k, IsEmpty (Bridge (BeforeIn splitExample) k)) ∧
    (∀ i, (splitExample i).Nodup) ∧ splitExampleDemands = [(0,3),(3,0),(2,1)] ∧
    splitExampleOverlay.card = 5 ∧
    ∃ H ⊆ splitExampleOverlay, H.card = 4 ∧ (2,1) ∉ H ∧
      Preserves splitExampleOverlay H splitExampleDemands := by
  refine ⟨splitExample_bridge_free,by decide,by decide,by rw [splitExampleOverlay_eq]; decide,
    cycleWithoutChord,?_,by decide,by decide,?_⟩
  · rw [splitExampleOverlay_eq]
    decide
  · have sub : cycleWithoutChord ⊆ splitExampleOverlay := by rw [splitExampleOverlay_eq]; decide
    have allPairs : ∀ u v : Fin 4, u ∈ reaches cycleWithoutChord v := by decide
    intro d _
    exact ⟨reach_mono sub,fun _ => mem_reaches.mp (allPairs d.1 d.2)⟩

/-- Three two-vertex paths forming a directed cycle. -/
def lemma35_cycle : Fin 3 → List (Fin 3) := ![[0, 1], [1, 2], [2, 0]]

private theorem lemma35_cycle_no_two :
    ∀ (x y : Fin 3) (a r : Fin 3), r ≠ a →
      BeforeIn lemma35_cycle a x y → BeforeIn lemma35_cycle r x y → False := by
  unfold BeforeIn
  decide

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 1000000 in
private theorem lemma35_cycle_no_three :
    ∀ (x y z : Fin 3) (a b r : Fin 3), a ≠ b → r ≠ a → r ≠ b →
      BeforeIn lemma35_cycle a x y → BeforeIn lemma35_cycle b y z →
      BeforeIn lemma35_cycle r x z → False := by
  unfold BeforeIn
  decide

set_option synthInstance.maxSize 512 in
/-- The source-restriction step of Lemma 35 can fail even with unique
intersections and full bridge-freeness. On the base path 0→1, its first
vertex is a successor of 2 and only its second vertex precedes 2. -/
theorem lemma35_cycle_counterexample :
    (∀ k, IsEmpty (Bridge (BeforeIn lemma35_cycle) k)) ∧
      (∀ i, (lemma35_cycle i).Nodup) ∧
      (∀ i j : Fin 3, i ≠ j → ∀ x y : Fin 3,
        x ∈ lemma35_cycle i → x ∈ lemma35_cycle j →
        y ∈ lemma35_cycle i → y ∈ lemma35_cycle j → x = y) ∧
      lemma35_cycle 0 = [0, 1] ∧ BeforeIn lemma35_cycle 1 1 2 ∧
      BeforeIn lemma35_cycle 2 2 0 ∧ ¬ ∃ i, BeforeIn lemma35_cycle i 0 2 := by
  refine ⟨?_, by decide, by decide, rfl, ?_, ?_, ?_⟩
  · intro k
    refine ⟨fun b => ?_⟩
    have bound := bridge_path_count_le b
    rw [Fintype.card_fin] at bound
    have small : k ≤ 1 := by omega
    interval_cases k
    · exact lemma35_cycle_no_two _ _ _ _ (b.river_ne_arc 0) (b.arcStep 0) b.riverStep
    · have distinct : b.arc 0 ≠ b.arc 1 := fun equal => (by decide : (0 : Fin 2) ≠ 1) (b.distinctArcs equal)
      exact lemma35_cycle_no_three _ _ _ _ _ _ distinct (b.river_ne_arc 0) (b.river_ne_arc 1)
        (b.arcStep 0) (b.arcStep 1) b.riverStep
  · unfold BeforeIn
    decide
  · unfold BeforeIn
    decide
  · unfold BeforeIn
    decide

end OnlineReachabilityPreservers.SourceAudit
