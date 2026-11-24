import DirectedFlowCutGap.ConcurrentVertexBudgetGrid
import DirectedFlowCutGap.ConcurrentEdgeBudgetSelection

/-! Select a normalized vertex assignment and rounding mode by their
exact rational sparsity receipt. -/
namespace DirectedFlowCutGap.ConcurrentVertexBudgetSelection

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestVertexDistances (weights)
open SparsestVertexBridge (demandDistance)
open ConcurrentVertexBudget (raw raw_eq freeDemand)
open ConcurrentVertexBudgetGrid (candidates)
open ConcurrentEdgeBudgetSelection (score scale score_le_iff scale_bound)

variable {m n : ℕ}

def rawCost (c w : Row n) : ℚ≥0 := ∑ v, raw c v*raw w v
def rawMass (w : Row n) : ℚ≥0 := ∑ v, raw w v

theorem rawCost_eq (c w : Row n) : (rawCost c w : ℝ≥0) = weightedCost (weights c) (weights w) := by
  simp only [rawCost,NNRat.cast_sum,NNRat.cast_mul,raw_eq,weightedCost]

theorem rawMass_eq (w : Row n) : (rawMass w : ℝ≥0) = totalWeight (weights w) := by
  simp only [rawMass,NNRat.cast_sum,raw_eq,totalWeight]

structure Plan (n : ℕ) where
  lengths : Row n
  mode : ChargedVertexModes.Mode
  receipt : ℚ≥0

def plan (c w : Row n) (m : ℕ) : Plan n :=
  let fee := rawCost c w
  let mass := rawMass w
  let s := score n m fee mass .size
  let t := score n m fee mass .mass
  if t ≤ s then ⟨w,.mass,t⟩ else ⟨w,.size,s⟩

def choose (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) : Option (Plan n) :=
  ((candidates hn A c P).map (fun w => plan c w m)).argmin Plan.receipt

theorem plan_lengths (c w : Row n) (m : ℕ) : (plan c w m).lengths = w := by
  unfold plan
  dsimp only
  split <;> rfl

theorem plan_receipt (c w : Row n) (m : ℕ) :
    (plan c w m).receipt = score n m (rawCost c w) (rawMass w) (plan c w m).mode := by
  unfold plan
  dsimp only
  split <;> rfl

private theorem locally_best (c w : Row n) (m : ℕ) (mode : ChargedVertexModes.Mode) :
    (plan c w m).receipt ≤ score n m (rawCost c w) (rawMass w) mode := by
  unfold plan
  dsimp only
  split
  · cases mode
    · exact le_rfl
    · assumption
  · cases mode
    · exact le_of_not_ge ‹_›
    · exact le_rfl

theorem chosen_member (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {z : Plan n} (selected : choose hn A c P = some z) :
    ∃ w ∈ candidates hn A c P, plan c w m = z := by
  have member : z ∈ ((candidates hn A c P).map (fun w => plan c w m)).argmin Plan.receipt := by
    change z ∈ choose hn A c P
    simp only [selected,Option.mem_some_iff]
  exact List.mem_map.mp (List.argmin_mem member)

theorem chosen_le (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {z : Plan n} (selected : choose hn A c P = some z) (w : Row n) (member : w ∈ candidates hn A c P)
    (mode : ChargedVertexModes.Mode) :
    scale n m (weightedCost (weights c) (weights z.lengths)) (totalWeight (weights z.lengths)) z.mode ≤
      scale n m (weightedCost (weights c) (weights w)) (totalWeight (weights w)) mode := by
  obtain ⟨q,_,rfl⟩ := chosen_member hn A c P selected
  rw [plan_lengths,← rawCost_eq,← rawMass_eq,← rawCost_eq,← rawMass_eq]
  apply (score_le_iff n m ..).mp
  rw [← plan_receipt]
  let plans := (candidates hn A c P).map (fun p => plan c p m)
  have available : plan c w m ∈ plans := List.mem_map.mpr ⟨w,member,rfl⟩
  have found : plan c q m ∈ plans.argmin Plan.receipt := by
    change plan c q m ∈ choose hn A c P
    simp only [selected,Option.mem_some_iff]
  exact (List.le_of_mem_argmin available found).trans (locally_best c w m mode)

theorem chosen_normalized (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {z : Plan n} (selected : choose hn A c P = some z)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2) :
    (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) (weights z.lengths) (P.get i) := by
  obtain ⟨w,member,rfl⟩ := chosen_member hn A c P selected
  rw [plan_lengths]
  exact ConcurrentVertexBudgetGrid.normalized hn A c P reach d different noArc member

theorem chosen_comparison (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {z : Plan n} (selected : choose hn A c P = some z)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (noFree : freeDemand A c P = none)
    (w : Fin n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ i, demandDistance (graph A) w (P.get i))
    (mode : ChargedVertexModes.Mode) :
    scale n m (weightedCost (weights c) (weights z.lengths)) (totalWeight (weights z.lengths)) z.mode ≤
      48*scale n m (weightedCost (weights c) w) (totalWeight w) mode := by
  obtain ⟨near,member,fee,mass⟩ := ConcurrentVertexBudgetGrid.nearby hn A c P reach d different noArc noFree w normal
  exact (chosen_le hn A c P selected near member mode).trans (scale_bound n m _ _ _ _ fee mass mode)

theorem has_choice (hn : 0 < n) (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2)
    (noFree : freeDemand A c P = none) : ∃ z, choose hn A c P = some z := by
  have normalized := VertexNormalizedPotentials.normalized_of_nonadjacent (graph A) P.get
    (m : ℝ≥0) d (reach d) different noArc
  obtain ⟨w,found,_⟩ := ConcurrentVertexBudgetGrid.nearby hn A c P reach d different noArc noFree (fun _ => m) normalized
  cases selected : choose hn A c P with
  | some z => exact ⟨z,rfl⟩
  | none =>
    have member : plan c w m ∈ ((candidates hn A c P).map (fun p => plan c p m)) :=
      List.mem_map.mpr ⟨w,found,rfl⟩
    rw [choose] at selected
    rw [List.argmin_eq_none.mp selected] at member
    exact (List.not_mem_nil member).elim

end DirectedFlowCutGap.ConcurrentVertexBudgetSelection
