import DirectedFlowCutGap.MeasuredColumnSparsestRound
import DirectedFlowCutGap.MeasuredFreeResources
import DirectedFlowCutGap.MeasuredThresholdScaling

/-! Count the original free-resource branches, selected optimizer, and
harmonic threshold before the amplified tape is executed. -/
namespace DirectedFlowCutGap.MeasuredPreparedSparsestRound

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open ConcurrentEdgeBudgetWidths (candidateWidth)
open RationalEdgeThresholds (Weights)
open ChargedVertexModes (Mode)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags)
open MeasuredSparsityPlans (decode)
open MeasuredSparsestDistances (distanceWidth)
open RawNonnegativeRational (Code)

variable {n m : ℕ}

private def finish {Shape Output : Type*} (plan : Option (Shape × Mode))
    (threshold : Shape → MeasuredSparsestThreshold.Selection m × ℕ)
    (round : Shape → Mode → Code → Option Output × ℕ) : Option Output × ℕ :=
  match plan with
  | none => (none,0)
  | some (w,mode) =>
    let selected := threshold w
    let result := match selected.1 with
      | .threshold _ q => round w mode q
      | _ => (none,0)
    (result.1,selected.2+result.2)

open scoped NNRat in
private theorem finish_value {Shape Output : Type*} (plan : Option (Shape × Mode))
    (threshold : Shape → MeasuredSparsestThreshold.Selection m × ℕ)
    (plain : Shape → RationalSparsestEdgeThreshold.Selection m)
    (round : Shape → Mode → Code → Option Output × ℕ) (plainRound : Shape → Mode → ℚ≥0 → Option Output)
    (equal : ∀ w, (threshold w).1.observe = plain w)
    (equalRound : ∀ w mode q, (round w mode q).1 = plainRound w mode q.value) :
    (finish plan threshold round).1 = plan.bind (fun z =>
      match plain z.1 with | .threshold _ q => plainRound z.1 z.2 q | _ => none) := by
  cases plan with
  | none => rfl
  | some pair =>
    rcases pair with ⟨w,mode⟩
    simp only [Option.bind_some]
    rw [← equal w]
    cases found : (threshold w).1 <;>
      simp only [finish,found,MeasuredSparsestThreshold.Selection.observe,equalRound]

private theorem finish_charge {Shape Output : Type*} (plan : Option (Shape × Mode))
    (threshold : Shape → MeasuredSparsestThreshold.Selection m × ℕ)
    (round : Shape → Mode → Code → Option Output × ℕ)
    {B C : ℕ} (fits : ∀ w mode, plan = some (w,mode) →
      (threshold w).2 ≤ B ∧ ∀ i q, (threshold w).1 = .threshold i q → (round w mode q).2 ≤ C) :
    (finish plan threshold round).2 ≤ B+C := by
  cases plan with
  | none => exact Nat.zero_le _
  | some pair =>
    rcases pair with ⟨w,mode⟩
    obtain ⟨price,scaled⟩ := fits w mode rfl
    cases found : (threshold w).1 with
    | unreachable _ => simp only [finish,found,Nat.add_zero]; omega
    | zero => simp only [finish,found,Nat.add_zero]; omega
    | threshold i q => simpa only [finish,found] using Nat.add_le_add price (scaled i q found)

private theorem edgePlan_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (MeasuredColumnBudgetSelection.edge hn A c P).1.map (decode ConcurrentEdgeBudgetSelection.Plan.mk) =
      ConcurrentEdgeBudgetSelection.choose hn A c P := by
  rw [(MeasuredColumnBudgetSelection.edge_preserves hn A c P).1]
  exact MeasuredOriginalBudgetSelection.edge_value hn A c P

private def edgeLengths (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (Weights n × Mode) × ℕ :=
  let checked := MeasuredFreeResources.edge A c P
  match checked.1 with
  | some _ =>
    let lengths := MeasuredFreeResources.freeLength c m
    (some (lengths.1,.mass),checked.2+lengths.2)
  | none =>
    let result := MeasuredColumnBudgetSelection.edge hn A c P
    (result.1.map (fun z => (z.row,z.scored.mode)),checked.2+result.2)

private theorem edgeLengths_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edgeLengths hn A c P).1 = ConcurrentEdgeBudgetRound.prepare hn A c P := by
  have plan := congrArg (Option.map (fun q : ConcurrentEdgeBudgetSelection.Plan n => (q.lengths,q.mode)))
    (edgePlan_value hn A c P)
  simp only [Option.map_map,Function.comp_def,decode] at plan
  cases found : ConcurrentEdgeZeroPrices.detect A c P
  · simpa only [edgeLengths,MeasuredFreeResources.edge_value,ConcurrentEdgeBudgetRound.prepare,found] using plan
  · simp only [edgeLengths,MeasuredFreeResources.edge_value,MeasuredFreeResources.freeLength_value,
      ConcurrentEdgeBudgetRound.prepare,found]

def edgeLengthWidth (n m B : ℕ) : ℕ := max (m.size+1) (candidateWidth n m B)

private theorem edgeLengths_bounds (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fits : MatrixFits c B) :
    (∀ w mode, (edgeLengths hn A c P).1 = some (w,mode) → MatrixFits w (edgeLengthWidth n m B)) ∧
    (edgeLengths hn A c P).2 ≤ MeasuredFreeResources.edgeWork n m B+
      MeasuredFreeResources.freeLengthWork n m B+MeasuredColumnBudgetSelection.edgeWork n m B := by
  have scan := MeasuredFreeResources.edge_charge A c P fits
  obtain ⟨freeWidth,freeWork⟩ := MeasuredFreeResources.freeLength_bounds c m fits
  have selectedWork := MeasuredColumnBudgetSelection.edge_charge hn A c P fits
  cases found : (MeasuredFreeResources.edge A c P).1 with
  | none =>
    refine ⟨?_,?_⟩
    · intro w mode h
      simp only [edgeLengths,found] at h
      obtain ⟨row,picked,eq⟩ := Option.map_eq_some_iff.mp h
      have original := edgePlan_value hn A c P
      rw [picked,Option.map_some] at original
      have shape := ConcurrentEdgeBudgetWidths.selected_fits hn A c P fits original.symm
      have emit : row.row = w := congrArg Prod.fst eq
      intro u v
      exact emit ▸ BinaryFractionalWalkBounds.stored_mono (shape u v) (le_max_right ..)
    · simp only [edgeLengths,found]
      omega
  | some i =>
    refine ⟨?_,?_⟩
    · intro w mode h
      simp only [edgeLengths,found,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,_⟩ := h
      exact fun u v => BinaryFractionalWalkBounds.stored_mono (freeWidth u v) (le_max_left ..)
    · simp only [edgeLengths,found]
      omega

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Mask n × Bits) × ℕ :=
  let lengths := edgeLengths hn A c P
  let cut := finish lengths.1 (fun w => MeasuredSparsestThreshold.edge A w P) (fun w mode q =>
    let scaled := MeasuredThresholdScaling.edge A w c q
    (AmplifiedSparsestEdgeTape.round A c P scaled.1 mode extra confidence bits,scaled.2))
  (cut.1,lengths.2+cut.2)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (edge hn A c P extra confidence bits).1 = AmplifiedBudgetedSparsestEdge.run hn A c P extra confidence bits := by
  simp only [edge,edgeLengths_value,AmplifiedBudgetedSparsestEdge.run]
  exact finish_value _ _ _ _
    (fun w mode q => AmplifiedSparsestEdgeTape.round A c P (RationalSparsestEdgeRound.scaled A w c q)
      mode extra confidence bits)
    (fun w => MeasuredSparsestThreshold.edge_value A w P)
    (fun w mode q => by simp only [MeasuredThresholdScaling.edge_value])

def edgeWork (n m B : ℕ) : ℕ :=
  let W := edgeLengthWidth n m B
  MeasuredFreeResources.edgeWork n m B+MeasuredFreeResources.freeLengthWork n m B+
    MeasuredColumnBudgetSelection.edgeWork n m B+(MeasuredSparsestThreshold.edgeWork n m W+
      MeasuredThresholdScaling.work (n*n) W B (distanceWidth n W))

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : MatrixFits c B) :
    (edge hn A c P extra confidence bits).2 ≤ edgeWork n m B := by
  obtain ⟨width,prep⟩ := edgeLengths_bounds hn A c P fits
  unfold edge edgeWork
  refine Nat.add_le_add prep (finish_charge _ _ _ fun w mode h => ?_)
  have lengths := width w mode h
  exact ⟨MeasuredSparsestThreshold.edge_charge A w P lengths,fun _ q found =>
    MeasuredThresholdScaling.edge_charge A w c q lengths fits (MeasuredSparsestThreshold.edge_threshold_fits A w P lengths found)⟩

private theorem vertexPlan_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) :
    (MeasuredColumnBudgetSelection.vertex hn A c P).1.map (decode ConcurrentVertexBudgetSelection.Plan.mk) =
      ConcurrentVertexBudgetSelection.choose hn A c P := by
  rw [(MeasuredColumnBudgetSelection.vertex_preserves hn A c P).1]
  exact MeasuredOriginalBudgetSelection.vertex_value hn A c P

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Flags n × Bits) × ℕ :=
  let checked := MeasuredFreeResources.vertex A c P
  match checked.1.2 with
  | some _ => (some (checked.1.1,bits),checked.2)
  | none =>
    let result := MeasuredColumnBudgetSelection.vertex hn A c P
    let cut := finish (result.1.map (fun z => (z.row,z.scored.mode)))
      (fun w => MeasuredSparsestThreshold.vertex A w P) (fun w mode q =>
        let scaled := MeasuredThresholdScaling.vertex A w c q
        (AmplifiedSparsestVertexTape.round A c P scaled.1 mode extra confidence bits,scaled.2))
    (cut.1,checked.2+result.2+cut.2)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (vertex hn A c P extra confidence bits).1 = ConcurrentVertexBudgetRound.run hn A c P extra confidence bits := by
  have plan := vertexPlan_value hn A c P
  cases found : ConcurrentVertexBudget.freeDemand A c P
  · simp only [vertex,MeasuredFreeResources.vertex_value,ConcurrentVertexBudgetRound.run,found]
    have run := finish_value ((MeasuredColumnBudgetSelection.vertex hn A c P).1.map (fun z => (z.row,z.scored.mode)))
      (fun w => MeasuredSparsestThreshold.vertex A w P) (fun w => RationalSparsestVertexThreshold.choose A w P)
      (fun w mode q =>
        let scaled := MeasuredThresholdScaling.vertex A w c q
        (AmplifiedSparsestVertexTape.round A c P scaled.1 mode extra confidence bits,scaled.2))
      (fun w mode q => AmplifiedSparsestVertexTape.round A c P (RationalSparsestVertexRound.scaled A w c q)
        mode extra confidence bits)
      (fun w => MeasuredSparsestThreshold.vertex_value A w P)
      (fun w mode q => by simp only [MeasuredThresholdScaling.vertex_value])
    rw [run,← plan]
    simp only [Option.bind_map,Function.comp_def,decode]
    congr 1
  · simp only [vertex,MeasuredFreeResources.vertex_value,ConcurrentVertexBudgetRound.run,found]

def vertexWork (n m B : ℕ) : ℕ :=
  let W := MeasuredBudgetPlanSelection.vertexWidth n m B
  MeasuredFreeResources.vertexWork n m B+MeasuredColumnBudgetSelection.vertexWork n m B+
    (MeasuredSparsestThreshold.vertexWork n m W+MeasuredThresholdScaling.work n W B (distanceWidth n (max 1 W)))

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : ∀ j, StoredBounded (c.get j) B) :
    (vertex hn A c P extra confidence bits).2 ≤ vertexWork n m B := by
  have detect := MeasuredFreeResources.vertex_charge A c P fits
  have optimize := MeasuredColumnBudgetSelection.vertex_charge hn A c P fits
  cases found : (MeasuredFreeResources.vertex A c P).1.2
  · simp only [vertex,found,vertexWork]
    refine Nat.add_le_add (Nat.add_le_add detect optimize) (finish_charge _ _ _ fun w mode h => ?_)
    obtain ⟨row,picked,eq⟩ := Option.map_eq_some_iff.mp h
    have original := vertexPlan_value hn A c P
    rw [picked,Option.map_some] at original
    obtain ⟨q,member,shape⟩ := ConcurrentVertexBudgetSelection.chosen_member hn A c P original.symm
    have same : row.row = q :=
      (congrArg ConcurrentVertexBudgetSelection.Plan.lengths shape.symm).trans
        (ConcurrentVertexBudgetSelection.plan_lengths c q m)
    have emit : row.row = w := congrArg Prod.fst eq
    have width := MeasuredBudgetPlanSelection.vertex_candidate_fits hn A c P fits member
    rw [← emit,same]
    exact ⟨MeasuredSparsestThreshold.vertex_charge A q P width,fun _ t found =>
      MeasuredThresholdScaling.vertex_charge A q c t width fits
        (MeasuredSparsestThreshold.vertex_threshold_fits A q P width found)⟩
  · simp only [vertex,found,vertexWork]
    omega

end DirectedFlowCutGap.MeasuredPreparedSparsestRound
