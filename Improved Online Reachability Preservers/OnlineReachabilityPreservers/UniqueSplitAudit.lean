import OnlineReachabilityPreservers.SplitAudit

/-! A longer cyclic obstruction to consecutive splitting with unique intersections. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

local instance decidableBeforeIn {V I : Type*} [DecidableEq V] (paths : I → List V)
    (i : I) (s t : V) : Decidable (BeforeIn paths i s t) := by
  unfold BeforeIn
  infer_instance

private def rainbowSearch {V I : Type*} [DecidableEq V] [DecidableEq I] (paths : I → List V) :
    ℕ → List I → V → V → Bool
  | 0, _, s, t => decide (s = t)
  | k+1, allowed, s, t =>
    decide (s = t) || allowed.any (fun i =>
      (paths i).any (fun v => decide (BeforeIn paths i s v) &&
        rainbowSearch paths k (allowed.filter (fun j => decide (j ≠ i))) v t))

private theorem rainbowSearch_of_chain {V I : Type*} [DecidableEq V] [DecidableEq I]
    (paths : I → List V) {k : ℕ} (v : Fin (k+1) → V) (a : Fin k → I)
    (distinct : Function.Injective a) (allowed : List I)
    (present : ∀ i, a i ∈ allowed) (steps : ∀ i, BeforeIn paths (a i) (v i.castSucc) (v i.succ)) :
    rainbowSearch paths k allowed (v 0) (v (Fin.last k)) = true := by
  induction k generalizing allowed with
  | zero =>
    have same : (Fin.last 0 : Fin 1) = 0 := by decide
    simp [rainbowSearch, same]
  | succ k ih =>
    rw [rainbowSearch, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a 0, present 0, List.any_eq_true.mpr ?_⟩
    have step := steps 0
    refine ⟨v 1, step.2.1, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true step, ?_⟩
    let v' (i : Fin (k+1)) := v i.succ
    let a' (i : Fin k) := a i.succ
    have inj : Function.Injective a' := distinct.comp (Fin.succ_injective _)
    have all (i : Fin k) : a' i ∈ allowed.filter (fun j => decide (j ≠ a 0)) := by
      apply List.mem_filter.mpr
      refine ⟨present i.succ, decide_eq_true ?_⟩
      exact fun eq => Fin.succ_ne_zero i (distinct eq)
    have follows (i : Fin k) : BeforeIn paths (a' i) (v' i.castSucc) (v' i.succ) := by
      simpa only [v', a', Fin.succ_castSucc] using steps i.succ
    simpa only [v', Fin.succ_last, Fin.succ_zero_eq_one] using ih v' a' inj _ all follows

/-- Paths overlaying a directed cycle, its two terminal attachments, and
a terminal-to-terminal demand. They intersect pairwise at most once. -/
def uniqueSplitExample : Fin 6 → List (Fin 7) :=
  ![[0,1,2,3], [3,4], [4,0], [5,2], [1,6], [5,6]]

/-- Every degree is two and the four-vertex path is the only path above
the original average length of 14/6. The printed deletion and
vertex-splitting stages therefore leave this family unchanged. -/
theorem uniqueSplitExample_original_sizes :
    (∑ i : Fin 6, (uniqueSplitExample i).length) = 14 ∧
      (∀ v : Fin 7, (occurrences (fun i => (uniqueSplitExample i).toFinset) v).card = 2) ∧
      (uniqueSplitExample 0).length = 4 ∧
      (∀ i : Fin 6, i ≠ 0 → (uniqueSplitExample i).length = 2) := by decide

def uniqueSplitExampleAfter : Fin 7 → List (Fin 7) :=
  ![[0,1], [2,3], [3,4], [4,0], [5,2], [1,6], [5,6]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 1024 in
private theorem uniqueSplitExample_search :
    ∀ (k : Fin 6) (r : Fin 6) (u v : Fin 7), BeforeIn uniqueSplitExample r u v →
      rainbowSearch uniqueSplitExample k.val ((List.finRange 6).filter (fun i => decide (i ≠ r))) u v = false := by
  decide

/-- The original family excludes every bridge, in spite of its directed cycle. -/
theorem uniqueSplitExample_bridge_free (k : ℕ) :
    IsEmpty (Bridge (BeforeIn uniqueSplitExample) k) := by
  refine ⟨fun b => ?_⟩
  have cap := bridge_path_count_le b
  rw [Fintype.card_fin] at cap
  let fuel : Fin 6 := ⟨k+1, by omega⟩
  let allowed := (List.finRange 6).filter (fun i => decide (i ≠ b.river))
  have all (i : Fin (k+1)) : b.arc i ∈ allowed :=
    List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true (b.river_ne_arc i).symm⟩
  have found := rainbowSearch_of_chain uniqueSplitExample b.vertex b.arc b.distinctArcs allowed all b.arcStep
  have absent := uniqueSplitExample_search fuel b.river _ _ b.riverStep
  change rainbowSearch uniqueSplitExample (k+1) allowed (b.vertex 0) (b.vertex (Fin.last (k+1))) = false at absent
  rw [absent] at found
  contradiction

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 1024 in
/-- Splitting the four-vertex path creates a half-7-bridge even with unique intersections. -/
theorem uniqueSplitExample_creates_half_seven :
    (∀ i, (uniqueSplitExample i).Nodup) ∧
    (∀ (i j : Fin 6), i ≠ j → ∀ x y : Fin 7, x ∈ uniqueSplitExample i → x ∈ uniqueSplitExample j →
      y ∈ uniqueSplitExample i → y ∈ uniqueSplitExample j → x = y) ∧
    ∃ b : Bridge (BeforeIn uniqueSplitExampleAfter) 5, b.arc (Fin.last 5) < b.river := by
  refine ⟨by decide, by decide, ?_⟩
  let v : Fin 7 → Fin 7 := ![5,2,3,4,0,1,6]
  let a : Fin 6 → Fin 7 := ![4,1,2,3,0,5]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (6 : Fin 7) ≠ a i := by decide
  have hs : BeforeIn uniqueSplitExampleAfter 6 (v 0) (v (Fin.last 6)) := by decide
  have ht : ∀ i, BeforeIn uniqueSplitExampleAfter (a i) (v i.castSucc) (v i.succ) := by decide
  exact ⟨⟨v, a, 6, fun {_ _} => hv _ _, fun {_ _} => ha _ _, hr, hs, ht⟩, by change (5 : Fin 7) < 6; decide⟩


/-- The consecutive-edge overlay for this unique-intersection family. -/
def uniqueSplitOverlay : Arcs (Fin 7) :=
  (univ : Finset (Fin 6)).biUnion fun i =>
    ((uniqueSplitExample i).zip ((uniqueSplitExample i).drop 1)).toFinset

def uniqueSplitDemands : List (Fin 7 × Fin 7) :=
  (List.finRange 6).map fun i => ((uniqueSplitExample i).headD 0, (uniqueSplitExample i).getLastD 0)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 1024 in
/-- The last demand has a route using both ends of the long path. Its own
edge is redundant even though the original paths share at most one vertex. -/
theorem uniqueSplitOverlay_redundant :
    uniqueSplitOverlay.card = 8 ∧
    ∃ H ⊆ uniqueSplitOverlay, H.card = 7 ∧ ((5,6) : Fin 7 × Fin 7) ∉ H ∧
      Preserves uniqueSplitOverlay H uniqueSplitDemands := by
  let H : Arcs (Fin 7) := {(0,1),(1,2),(2,3),(3,4),(4,0),(5,2),(1,6)}
  have sub : H ⊆ uniqueSplitOverlay := by decide
  have served : ∀ d ∈ uniqueSplitDemands, d.1 ∈ reaches H d.2 := by decide
  refine ⟨by decide, H, sub, by decide, by decide, ?_⟩
  intro d hd
  exact ⟨reach_mono sub, fun _ => mem_reaches.mp (served d hd)⟩

end OnlineReachabilityPreservers.SourceAudit
