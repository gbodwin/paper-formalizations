import DirectedFlowCutGap.MeasuredSparsityPlans

/-! Compare every candidate's two exact scores and retain the same winning
plan. The harmonic sum is computed once per call. -/
namespace DirectedFlowCutGap.MeasuredBudgetPlanSelection

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open BinaryRational (StoredBounded)
open FractionalCoverRawCore (rational)
open RawNonnegativeRational (Code)
open ChargedVertexModes (Mode)
open MeasuredSparsityPlans (ScoredRow decode minimum minimum_value minimum_charge planWidth planWork)
open MeasuredSparsityScore (harmonic_value harmonic_bounds)

variable {n m : ℕ}

private theorem map_argmin {α β : Type*} (ys : List (ScoredRow α))
    (build : α → Mode → ℚ≥0 → β) (value : β → ℚ≥0)
    (reading : ∀ x mode q, value (build x mode q) = q) :
    (minimum ys).1.map (decode build) = (ys.map (decode build)).argmin value := by
  rw [minimum_value, FractionalCoverRawGraph.argmin_map
    (fun q : ScoredRow α => rational q.scored.receipt) (decode build)
    (fun b => (value b : ℚ)) (fun q => by
      simp only [decode,reading,rational])]
  rfl

def collect {α : Type*} (ys : List α) (f : α → ScoredRow α × ℕ) :
    List (ScoredRow α) × ℕ :=
  let reached := ys.map f
  (reached.map Prod.fst,(reached.map Prod.snd).sum)

theorem collect_charge {α : Type*} (ys : List α) (f : α → ScoredRow α × ℕ)
    {W : ℕ} (fits : ∀ q ∈ ys, (f q).2 ≤ W) : (collect ys f).2 ≤ ys.length*W := by
  induction ys with
  | nil => simp [collect]
  | cons a ys ih =>
    have first := fits a List.mem_cons_self
    have next := ih (fun q hq => fits q (List.mem_cons_of_mem _ hq))
    simpa only [collect,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using
      Nat.add_le_add first next

theorem collect_width {α : Type*} (ys : List α) (f : α → ScoredRow α × ℕ)
    {W : ℕ} (fits : ∀ q ∈ ys, (f q).1.scored.receipt.Bounded W) :
    ∀ q ∈ (collect ys f).1, q.scored.receipt.Bounded W := by
  intro q present
  simp only [collect,List.map_map,Function.comp_def,List.mem_map] at present
  obtain ⟨y,member,rfl⟩ := present
  exact fits y member

theorem collect_minimum_value {α β : Type*} (ys : List α) (f : α → ScoredRow α × ℕ)
    (build : α → Mode → ℚ≥0 → β) (receipt : β → ℚ≥0) (plan : α → β)
    (read : ∀ x mode q, receipt (build x mode q) = q) (correct : ∀ q, decode build (f q).1 = plan q) :
    (minimum (collect ys f).1).1.map (decode build) = (ys.map plan).argmin receipt := by
  rw [map_argmin _ build receipt read]
  simp only [collect,List.map_map,Function.comp_def,correct]

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (ScoredRow (Weights n)) × ℕ :=
  let candidates := MeasuredBudgetCandidateLists.edge hn A c P
  let h := MeasuredSparsityScore.harmonic m
  let plans := collect candidates.1 (fun w => MeasuredSparsityPlans.edgePlan A c w m h.1)
  let best := minimum plans.1
  (best.1,candidates.2+h.2+plans.2+best.2)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edge hn A c P).1.map (decode ConcurrentEdgeBudgetSelection.Plan.mk) =
      ConcurrentEdgeBudgetSelection.choose hn A c P := by
  simp only [edge,ConcurrentEdgeBudgetSelection.choose,MeasuredBudgetCandidateLists.edge_value]
  exact collect_minimum_value _ _ _ _ _ (fun _ _ _ => rfl)
    (fun w => MeasuredSparsityPlans.edgePlan_value A c w m _ (harmonic_value m))

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    Option (ScoredRow (BinaryFractionalRows.Row n)) × ℕ :=
  let candidates := MeasuredBudgetCandidateLists.vertex hn A c P
  let h := MeasuredSparsityScore.harmonic m
  let plans := collect candidates.1 (fun w => MeasuredSparsityPlans.vertexPlan c w m h.1)
  let best := minimum plans.1
  (best.1,candidates.2+h.2+plans.2+best.2)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) :
    (vertex hn A c P).1.map (decode ConcurrentVertexBudgetSelection.Plan.mk) =
      ConcurrentVertexBudgetSelection.choose hn A c P := by
  simp only [vertex,ConcurrentVertexBudgetSelection.choose,MeasuredBudgetCandidateLists.vertex_value]
  exact collect_minimum_value _ _ _ _ _ (fun _ _ _ => rfl)
    (fun w => MeasuredSparsityPlans.vertexPlan_value c w m _ (harmonic_value m))

def selectionWork (r n m B W K : ℕ) : ℕ :=
  let H := m*(m+1)
  let Q := planWidth r n m B W H
  m*BinaryRawRational.budget m+m*BinaryRawRational.budget H+
    K*planWork r n m B W H+BinaryFractionalGraphBounds.argminBound K (Q+1) (40*(Q+2)^2)

theorem paid_selection {α : Type*} (ys : List α) (f : α → ScoredRow α × ℕ)
    {r n m B W K : ℕ} (length : ys.length ≤ K)
    (fees : ∀ a ∈ ys, (f a).1.scored.receipt.Bounded (planWidth r n m B W (m*(m+1))) ∧
      (f a).2 ≤ planWork r n m B W (m*(m+1))) :
    (MeasuredSparsityScore.harmonic m).2+(collect ys f).2+(minimum (collect ys f).1).2 ≤ selectionWork r n m B W K := by
  have feesPaid := (collect_charge ys f (fun a ha => (fees a ha).2)).trans (Nat.mul_le_mul_right _ length)
  have sameSize : (collect ys f).1.length = ys.length := by simp [collect]
  have cost := minimum_charge (collect ys f).1 (collect_width ys f (fun a ha => (fees a ha).1))
  rw [sameSize] at cost
  exact Nat.add_le_add (Nat.add_le_add (harmonic_bounds m).2 feesPaid)
    (cost.trans (BinaryFractionalGraphBounds.argminBound_mono length))

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (input : MatrixFits c B) :
    let K := (n*n*B+(m+n*n*(B+1))+3)*(m+n*2+3)
    let W := ConcurrentEdgeBudgetWidths.candidateWidth n m B
    (edge hn A c P).2 ≤
      K*MeasuredBudgetCoverCandidate.edgeWork n m B
        (ConcurrentEdgeBudgetWidths.priceWidth n m B) (ConcurrentEdgeBudgetWidths.massWidth n m)+
      selectionWork (n*n) n m B W K := by
  let costs := MeasuredBudgetCandidateLists.edge hn A c P
  have length : costs.1.length ≤ (n*n*B+(m+n*n*(B+1))+3)*(m+n*2+3) := by
    simp only [costs,MeasuredBudgetCandidateLists.edge_value,ConcurrentEdgeBudgetGrid.candidates,List.length_map]
    exact ConcurrentEdgeBudgetWidths.pair_count A c m input
  have plan := paid_selection costs.1 (fun w => MeasuredSparsityPlans.edgePlan A c w m (MeasuredSparsityScore.harmonic m).1)
    length (fun w member =>
      MeasuredSparsityPlans.edgePlan_bounds A c w m _ input
        (ConcurrentEdgeBudgetWidths.candidate_fits hn A c P input
          (MeasuredBudgetCandidateLists.edge_value hn A c P ▸ member)) (harmonic_bounds m).1)
  simpa only [edge,costs,Nat.add_assoc] using Nat.add_le_add (MeasuredBudgetCandidateLists.edge_charge hn A c P input) plan

theorem vertex_charge_at_width (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B W : ℕ} (input : ∀ i, StoredBounded (c.get i) B)
    (fields : ∀ w ∈ ConcurrentVertexBudgetGrid.candidates hn A c P, ∀ i, StoredBounded (w.get i) W) :
    let K := MeasuredBudgetCandidateLists.vertexCount n m B
    (vertex hn A c P).2 ≤ K*MeasuredBudgetCoverCandidate.vertexWork n m B
      (MeasuredBudgetCandidateLists.vertexPriceWidth n m B) (MeasuredBudgetCandidateLists.vertexMassWidth n m)+
      selectionWork n n m B W K := by
  let costs := MeasuredBudgetCandidateLists.vertex hn A c P
  have length : costs.1.length ≤ MeasuredBudgetCandidateLists.vertexCount n m B := by
    simp only [costs,MeasuredBudgetCandidateLists.vertex_value,ConcurrentVertexBudgetGrid.candidates,List.length_map]
    exact MeasuredBudgetCandidateLists.vertex_pair_count c m input
  have plan := paid_selection costs.1 (fun w => MeasuredSparsityPlans.vertexPlan c w m (MeasuredSparsityScore.harmonic m).1)
    length (fun w member =>
      MeasuredSparsityPlans.vertexPlan_bounds c w m _ input
        (fields w (MeasuredBudgetCandidateLists.vertex_value hn A c P ▸ member)) (harmonic_bounds m).1)
  simpa only [vertex,costs,Nat.add_assoc] using Nat.add_le_add (MeasuredBudgetCandidateLists.vertex_charge hn A c P input) plan

def vertexWidth (n m B : ℕ) : ℕ :=
  let price := B+MeasuredBudgetCandidateLists.vertexPriceWidth n m B+MeasuredBudgetCandidateLists.vertexMassWidth n m+2
  m+MultiplicityCoverWidths.normalizedWidth n m
    (MultiplicityCoverWidths.weightWidth n price m (FractionalCover.fuel n))+1

theorem vertex_candidate_fits (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (input : ∀ i, StoredBounded (c.get i) B)
    {w : BinaryFractionalRows.Row n} (present : w ∈ ConcurrentVertexBudgetGrid.candidates hn A c P) (i : Fin n) :
    StoredBounded (w.get i) (vertexWidth n m B) := by
  obtain ⟨pair,member,rfl⟩ := List.mem_map.mp present
  let fee := Code.ofNNRat pair.1
  let mass := Code.ofNNRat pair.2
  obtain ⟨fFit,mFit⟩ := MeasuredBudgetCandidateLists.vertex_pair_fits c m input member
  have same := MeasuredBudgetCoverCandidate.vertex_value hn A c P fee mass
  simp only [fee,mass,Code.value_ofNNRat] at same
  change StoredBounded ((ConcurrentVertexBudget.candidate hn A c P pair.1 pair.2).get i) _
  rw [← same]
  let prices := MeasuredBudgetPrices.vertex c fee mass
  have pricesFit (j : Fin n) : StoredBounded (prices.1.get j)
      (B+MeasuredBudgetCandidateLists.vertexPriceWidth n m B+MeasuredBudgetCandidateLists.vertexMassWidth n m+2) := by
    change StoredBounded prices.1[j.val] _
    simp only [prices,MeasuredBudgetPrices.vertex,MeasuredBudgetPrices.tabulate_value]
    exact (MeasuredBudgetPrices.cell_bounds (c.get j) fee mass (input j) fFit mFit).1
  let cover := MeasuredCanonicalCover.vertexRun hn A prices.1 P (FractionalCover.fuel n)
  have fields := (MeasuredCanonicalCover.vertexRun_bounds hn A prices.1 P pricesFit (FractionalCover.fuel n)).1
  have scaled := (MeasuredCoverLengths.scale_bounds m cover.stored.best fields.best).1
  change StoredBounded (MeasuredCoverLengths.vertex m cover.stored.best).1[i.val] _
  simp only [MeasuredCoverLengths.vertex,MeasuredCoverLengths.canonicalRow,MeasuredBudgetPrices.tabulate_value]
  exact (MeasuredBudgetPrices.canonical_bounds (scaled i)).1

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (input : ∀ i, StoredBounded (c.get i) B) :
    let K := MeasuredBudgetCandidateLists.vertexCount n m B
    (vertex hn A c P).2 ≤ K*MeasuredBudgetCoverCandidate.vertexWork n m B
      (MeasuredBudgetCandidateLists.vertexPriceWidth n m B) (MeasuredBudgetCandidateLists.vertexMassWidth n m)+
      selectionWork n n m B (vertexWidth n m B) K :=
  vertex_charge_at_width hn A c P input (fun _ h => vertex_candidate_fits hn A c P input h)

end DirectedFlowCutGap.MeasuredBudgetPlanSelection
