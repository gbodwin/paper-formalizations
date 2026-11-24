import DirectedFlowCutGap.MeasuredColumnBudgetCandidate
import DirectedFlowCutGap.MeasuredOriginalBudgetSelection

/-! Reuse the original grid and scoring with the column-counted candidates.
The selected row, exact score and tie-breaking are identical. -/
namespace DirectedFlowCutGap.MeasuredColumnBudgetSelection

open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open MeasuredSparsityPlans (ScoredRow minimum)
open MeasuredOriginalBudgetSelection (candidates)

variable {n m : ℕ}

private theorem candidates_preserve {α : Type*} (earlier later : Code → Code → α × ℕ)
    (same : ∀ p q, (later p q).1 = (earlier p q).1)
    {fee : ℕ} (paid : ∀ p q, (later p q).2 ≤ (earlier p q).2+fee) (pairs : List (Code × Code)) :
    (candidates later pairs).1 = (candidates earlier pairs).1 ∧
      (candidates later pairs).2 ≤ (candidates earlier pairs).2+pairs.length*fee := by
  induction pairs with
  | nil => simp [candidates]
  | cons p ps ih =>
    obtain ⟨outputs,work⟩ := ih
    have use := paid p.1 p.2
    simp only [candidates,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul,same] at *
    rw [outputs,eq_self,true_and]
    omega

private def select {α : Type*} (m : ℕ) (grid : List (Code × Code) × ℕ)
    (solve : Code → Code → α × ℕ) (score : α → Code → ScoredRow α × ℕ) :
    Option (ScoredRow α) × ℕ :=
  let batch := candidates solve grid.1
  let h := MeasuredSparsityScore.harmonic m
  let ranked := MeasuredBudgetPlanSelection.collect batch.1 (fun w => score w h.1)
  let best := minimum ranked.1
  (best.1,grid.2+batch.2+h.2+ranked.2+best.2)

private theorem select_preserves {α : Type*} (m : ℕ) (grid : List (Code × Code) × ℕ)
    (earlier later : Code → Code → α × ℕ) (score : α → Code → ScoredRow α × ℕ)
    (same : ∀ p q, (later p q).1 = (earlier p q).1)
    {fee : ℕ} (paid : ∀ p q, (later p q).2 ≤ (earlier p q).2+fee) :
    (select m grid later score).1 = (select m grid earlier score).1 ∧
      (select m grid later score).2 ≤ (select m grid earlier score).2+grid.1.length*fee := by
  obtain ⟨outputs,work⟩ := candidates_preserve earlier later same paid grid.1
  simp only [select,outputs,true_and]
  omega

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (ScoredRow (Weights n)) × ℕ :=
  select m (MeasuredGraphBudgetGrid.edge A c m) (MeasuredColumnBudgetCandidate.edge hn A c P)
    (MeasuredSparsityPlans.edgePlan A c · m)

theorem edge_preserves (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edge hn A c P).1 = (MeasuredOriginalBudgetSelection.edge hn A c P).1 ∧
      (edge hn A c P).2 ≤ (MeasuredOriginalBudgetSelection.edge hn A c P).2+
        (MeasuredGraphBudgetGrid.edge A c m).1.length*MeasuredColumnBudgetCandidate.edgeExtra n m :=
  select_preserves m (MeasuredGraphBudgetGrid.edge A c m)
    (MeasuredBudgetCoverCandidate.edge hn A c P) (MeasuredColumnBudgetCandidate.edge hn A c P)
    (MeasuredSparsityPlans.edgePlan A c · m)
    (fun p q => (MeasuredColumnBudgetCandidate.edge_preserves hn A c P p q).1)
    (fun p q => (MeasuredColumnBudgetCandidate.edge_preserves hn A c P p q).2)

def edgeWork (n m B : ℕ) : ℕ :=
  MeasuredOriginalBudgetSelection.edgeWork n m B+
    MeasuredOriginalBudgetSelection.edgeCount n m B*MeasuredColumnBudgetCandidate.edgeExtra n m

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) : (edge hn A c P).2 ≤ edgeWork n m B := by
  have count := congrArg List.length (MeasuredGraphBudgetGrid.edge_value A c m)
  simp only [List.length_map] at count
  have fits : (MeasuredGraphBudgetGrid.edge A c m).1.length ≤
      MeasuredOriginalBudgetSelection.edgeCount n m B := by
    rw [count]
    exact ConcurrentEdgeBudgetWidths.pair_count A c m fit
  exact (edge_preserves hn A c P).2.trans
    (Nat.add_le_add (MeasuredOriginalBudgetSelection.edge_charge hn A c P fit) (Nat.mul_le_mul_right _ fits))

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    Option (ScoredRow (BinaryFractionalRows.Row n)) × ℕ :=
  select m (MeasuredGraphBudgetGrid.vertex c m) (MeasuredColumnBudgetCandidate.vertex hn A c P)
    (MeasuredSparsityPlans.vertexPlan c · m)

theorem vertex_preserves (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) :
    (vertex hn A c P).1 = (MeasuredOriginalBudgetSelection.vertex hn A c P).1 ∧
      (vertex hn A c P).2 ≤ (MeasuredOriginalBudgetSelection.vertex hn A c P).2+
        (MeasuredGraphBudgetGrid.vertex c m).1.length*MeasuredColumnBudgetCandidate.vertexExtra n m :=
  select_preserves m (MeasuredGraphBudgetGrid.vertex c m)
    (MeasuredBudgetCoverCandidate.vertex hn A c P) (MeasuredColumnBudgetCandidate.vertex hn A c P)
    (MeasuredSparsityPlans.vertexPlan c · m)
    (fun p q => (MeasuredColumnBudgetCandidate.vertex_preserves hn A c P p q).1)
    (fun p q => (MeasuredColumnBudgetCandidate.vertex_preserves hn A c P p q).2)

def vertexWork (n m B : ℕ) : ℕ :=
  MeasuredOriginalBudgetSelection.vertexWork n m B+
    MeasuredBudgetCandidateLists.vertexCount n m B*MeasuredColumnBudgetCandidate.vertexExtra n m

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : ∀ i, StoredBounded (c.get i) B) : (vertex hn A c P).2 ≤ vertexWork n m B := by
  have count := congrArg List.length (MeasuredGraphBudgetGrid.vertex_value c m)
  simp only [List.length_map] at count
  have fits : (MeasuredGraphBudgetGrid.vertex c m).1.length ≤ MeasuredBudgetCandidateLists.vertexCount n m B := by
    rw [count]
    exact MeasuredBudgetCandidateLists.vertex_pair_count c m fit
  exact (vertex_preserves hn A c P).2.trans
    (Nat.add_le_add (MeasuredOriginalBudgetSelection.vertex_charge hn A c P fit) (Nat.mul_le_mul_right _ fits))

end DirectedFlowCutGap.MeasuredColumnBudgetSelection
