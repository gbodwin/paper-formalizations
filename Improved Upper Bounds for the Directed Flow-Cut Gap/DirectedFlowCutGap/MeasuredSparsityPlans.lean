import DirectedFlowCutGap.MeasuredGraphPlanTotals
import DirectedFlowCutGap.MeasuredBudgetCandidateLists
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-! Construct both scores on each candidate and compare their exact binary
values. The final argmin retains the first plan at equal score. -/
namespace DirectedFlowCutGap.MeasuredSparsityPlans

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open BinaryRational (StoredBounded)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open FractionalCoverRawCore (rational)
open ChargedVertexModes (Mode)
open MeasuredSparsitySelection (Scored modes uncode)

variable {n m : ℕ}

structure ScoredRow (α : Type*) where
  row : α
  scored : Scored

def decode {α β : Type*} (build : α → Mode → ℚ≥0 → β) (q : ScoredRow α) : β :=
  build q.row q.scored.mode q.scored.receipt.value

def scored (n m : ℕ) {α : Type*} (w : α) (h : Code) (t : MeasuredSparsitySelection.Totals) :
    ScoredRow α × ℕ :=
  let choice := modes n m t.price t.mass h
  (⟨w,choice.1⟩,t.charge+choice.2)

attribute [local irreducible] modes ConcurrentEdgeBudgetSelection.score in
theorem scored_value (n m : ℕ) {α β : Type*} (w : α) (h : Code) (t : MeasuredSparsitySelection.Totals)
    (build : α → Mode → ℚ≥0 → β) (harmonic : h.value = NormalizedOptimalMode.harmonic m) :
    let s := ConcurrentEdgeBudgetSelection.score n m t.price.value t.mass.value .size
    let u := ConcurrentEdgeBudgetSelection.score n m t.price.value t.mass.value .mass
    decode build (scored n m w h t).1 = if u ≤ s then build w .mass u else build w .size s := by
  change (fun q : Mode × ℚ≥0 => build w q.1 q.2) (uncode (modes n m t.price t.mass h).1) = _
  rw [MeasuredSparsitySelection.modes_value n m t.price t.mass h harmonic]
  dsimp only
  by_cases cheaper : ConcurrentEdgeBudgetSelection.score n m t.price.value t.mass.value .mass ≤
      ConcurrentEdgeBudgetSelection.score n m t.price.value t.mass.value .size
  · simp only [ite_eq_left cheaper]
  · simp only [ite_eq_right cheaper]

def edgePlan (A : Adjacency n) (c w : Weights n) (m : ℕ) (h : Code) : ScoredRow (Weights n) × ℕ :=
  scored n m w h (MeasuredGraphPlanTotals.edgeTotals A c w)

theorem edgePlan_value (A : Adjacency n) (c w : Weights n) (m : ℕ) (h : Code)
    (harmonic : h.value = NormalizedOptimalMode.harmonic m) :
    decode ConcurrentEdgeBudgetSelection.Plan.mk (edgePlan A c w m h).1 =
      ConcurrentEdgeBudgetSelection.plan A c w m := by
  obtain ⟨fee,mass⟩ := MeasuredGraphPlanTotals.edgeTotals_value A c w
  simpa only [edgePlan,ConcurrentEdgeBudgetSelection.plan,fee,mass] using
    scored_value n m w h (MeasuredGraphPlanTotals.edgeTotals A c w) ConcurrentEdgeBudgetSelection.Plan.mk harmonic

def vertexPlan (c w : BinaryFractionalRows.Row n) (m : ℕ) (h : Code) :
    ScoredRow (BinaryFractionalRows.Row n) × ℕ :=
  scored n m w h (MeasuredGraphPlanTotals.vertexTotals c w)

theorem vertexPlan_value (c w : BinaryFractionalRows.Row n) (m : ℕ) (h : Code)
    (harmonic : h.value = NormalizedOptimalMode.harmonic m) :
    decode ConcurrentVertexBudgetSelection.Plan.mk (vertexPlan c w m h).1 =
      ConcurrentVertexBudgetSelection.plan c w m := by
  obtain ⟨fee,mass⟩ := MeasuredGraphPlanTotals.vertexTotals_value c w
  simpa only [vertexPlan,ConcurrentVertexBudgetSelection.plan,fee,mass] using
    scored_value n m w h (MeasuredGraphPlanTotals.vertexTotals c w) ConcurrentVertexBudgetSelection.Plan.mk harmonic

def planWidth (r n m B W H : ℕ) : ℕ :=
  MeasuredSparsityScore.scoreWidth n m (r*(B+W+1)) (r*(W+1)) H

def planWork (r n m B W H : ℕ) : ℕ :=
  MeasuredGraphPlanTotals.totalsWork r B W+43*BinaryRawRational.budget (planWidth r n m B W H)

theorem edgePlan_bounds (A : Adjacency n) (c w : Weights n) (m : ℕ) (h : Code) {B W H : ℕ}
    (price : MatrixFits c B) (lengths : MatrixFits w W) (harmonic : h.Bounded H) :
    (edgePlan A c w m h).1.scored.receipt.Bounded (planWidth (n*n) n m B W H) ∧
      (edgePlan A c w m h).2 ≤ planWork (n*n) n m B W H := by
  obtain ⟨fee,mass,paid⟩ := MeasuredGraphPlanTotals.edgeTotals_bounds A c w price lengths
  obtain ⟨fields,work⟩ := MeasuredSparsitySelection.modes_bounds n m _ _ h fee mass harmonic
  exact ⟨fields,Nat.add_le_add paid work⟩

theorem vertexPlan_bounds (c w : BinaryFractionalRows.Row n) (m : ℕ) (h : Code) {B W H : ℕ}
    (price : ∀ i, StoredBounded (c.get i) B) (lengths : ∀ i, StoredBounded (w.get i) W)
    (harmonic : h.Bounded H) :
    (vertexPlan c w m h).1.scored.receipt.Bounded (planWidth n n m B W H) ∧
      (vertexPlan c w m h).2 ≤ planWork n n m B W H := by
  obtain ⟨fee,mass,paid⟩ := MeasuredGraphPlanTotals.vertexTotals_bounds c w price lengths
  obtain ⟨fields,work⟩ := MeasuredSparsitySelection.modes_bounds n m _ _ h fee mass harmonic
  exact ⟨fields,Nat.add_le_add paid work⟩

def minimum {α : Type*} (ys : List (ScoredRow α)) : Option (ScoredRow α) × ℕ :=
  BinaryFractionalGraphOracle.argmin (fun q => BinaryRawRational.encode q.scored.receipt) ys

theorem minimum_value {α : Type*} (ys : List (ScoredRow α)) :
    (minimum ys).1 = ys.argmin (fun q => rational q.scored.receipt) := by
  simp only [minimum,BinaryFractionalGraphOracle.argmin_decode,BinaryRawRational.encode_value,
    FractionalCoverRawGraph.argminCode_refines]

theorem minimum_charge {α : Type*} (ys : List (ScoredRow α)) {W : ℕ}
    (fit : ∀ q ∈ ys, q.scored.receipt.Bounded W) :
    (minimum ys).2 ≤ BinaryFractionalGraphBounds.argminBound ys.length (W+1) (40*(W+2)^2) := by
  exact BinaryFractionalGraphBounds.argmin_charge _ ys
    (fun i hi => ⟨BinaryRawRational.encode_width (fit i hi),BinaryRawRational.encode_paid (fit i hi)⟩)

end DirectedFlowCutGap.MeasuredSparsityPlans
