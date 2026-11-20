import DirectedFlowCutGap.AmplificationFrameLayout
import DirectedFlowCutGap.FramedEdgeTrials
import DirectedFlowCutGap.PaidFramedVertexCost

/-! The explicit-stack variants reserve only the frames of reached calls.
Bound both original sources, including rejection and partial tape walks. -/
namespace DirectedFlowCutGap.FramedSolverStackLayout

open BinaryArithmetic EncodedArrayStorage Polynomial
open AmplificationFrameLayout (Code)
open ChargedPhysicalVertexSolver (rowsCount rowsCount_le)
open PhysicalIntegerRoundingCost (eval_mono)

def vertex (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Code :=
  match (PhysicalSourceInputJoin.vertex source).1 with
  | none => []
  | some ⟨n,D⟩ =>
    match (PhysicalSourceReadback.runWithTerminalCharge D).1 with
    | none => []
    | some (plan,_,_) =>
      let controls := BinarySolverOuterControls.vertex n κ
      AmplificationFrameLayout.code D (PaidVertexRounding.runner mode) controls.draws controls.extra
        controls.confidence plan tape

def edge (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Code :=
  match (PhysicalSourceInputJoin.edge source).1 with
  | none => []
  | some ⟨n,D⟩ =>
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
    match (PhysicalSourceReadback.runWithTerminalCharge line).1 with
    | none => []
    | some (plan,_,_) =>
      let controls := BinarySolverOuterControls.edge n κ
      AmplificationFrameLayout.code line (PaidDirectEdgeWire.roundWithGadgetWork raw mode) controls.draws
        controls.extra controls.confidence plan tape

private noncomputable def sampleCount : Polynomial ℕ := (X+2)*X+1

private theorem samples_le (n κ x : ℕ) (dim : n≤x) (confidence : κ≤x) :
    EncodedVertexAmplification.confidenceExponent n κ+1 ≤ sampleCount.eval x := by
  simp only [sampleCount,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  exact Nat.add_le_add_right ((PhysicalSolverCostEnvelope.exponent_le n κ).trans
    (Nat.mul_le_mul (Nat.add_le_add_right dim 2) confidence)) 1

private theorem vertex_rows {n : ℕ} {D : BinaryFractionalGuesses.Input n} {source : Bits}
    (parsed : (PhysicalSourceInputJoin.vertex source).1=some ⟨n,D⟩) :
    rowsCount (PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1) ≤ 4*source.length+3 := by
  have original : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
    simpa only [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value] using parsed
  obtain ⟨size,_,fields⟩ := ChargedSourceAssembly.vertex_dimensions original
  have fits (i : Fin n) : BinaryRational.StoredBounded (BinaryFractionalRows.get D.costs i) source.length := by
    apply fields
    change D.costs[i.val] ∈ D.costs.toList
    have inside : i.val<D.costs.toList.length := by simp [i.isLt]
    simpa only [Vector.getElem_toList] using List.getElem_mem inside
  have cap := (rowsCount_le D).trans (PhysicalSolverCostEnvelope.rowLimit_le D fits)
  simp only [PhysicalSolverCostEnvelope.rowEnvelope] at cap
  omega

private theorem widen {n x : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits) (p : Polynomial ℕ)
    (rows : rowsCount plan ≤ p.eval x) (samples : extra+1≤ sampleCount.eval x) :
    let scheduled := AmplificationFrameLayout.code D round draw extra confidence plan tape
    fresh scheduled ≤ (sampleCount*(2*p+2)).eval x ∧ scheduled.length ≤ (sampleCount*(8*p+8)).eval x := by
  obtain ⟨space,work⟩ := AmplificationFrameLayout.bounds D round draw extra confidence plan tape
  simp only [eval_mul,eval_add,eval_ofNat]
  exact ⟨space.trans (Nat.mul_le_mul samples (by gcongr)),work.trans (Nat.mul_le_mul samples (by gcongr))⟩

set_option maxHeartbeats 1000000 in
theorem vertex_polynomial : ∃ cells steps : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (source tape : Bits), fresh (vertex κ mode source tape) ≤ cells.eval (source.length+κ) ∧
      (vertex κ mode source tape).length ≤ steps.eval (source.length+κ) := by
  let p : Polynomial ℕ := 4*X+3
  refine ⟨sampleCount*(2*p+2),sampleCount*(8*p+8),fun κ mode source tape => ?_⟩
  unfold vertex
  cases parsed : (PhysicalSourceInputJoin.vertex source).1 with
  | none => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | some accepted =>
    obtain ⟨n,D⟩ := accepted
    let x := source.length+κ
    let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
    let controls := BinarySolverOuterControls.vertex n κ
    obtain ⟨dispatch,_,reader,_,actual,_⟩ := PhysicalSourceReadback.terminal_headers D
    simp only [actual]
    have original : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
      simpa only [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value] using parsed
    have dims : n≤x := (ChargedSourceAssembly.vertex_dimensions original).1.trans (Nat.le_add_right _ _)
    have row : rowsCount plan ≤ p.eval x := by
      simp only [p,eval_add,eval_mul,eval_ofNat,eval_X]
      exact (vertex_rows parsed).trans (by dsimp only [x]; omega)
    have sample : controls.extra+1≤ sampleCount.eval x := by
      rw [BinarySolverOuterControls.vertex_extra]
      exact samples_le n κ x dims (Nat.le_add_left _ _)
    exact widen D (PaidVertexRounding.runner mode) controls.draws controls.extra controls.confidence plan tape p row sample

set_option maxHeartbeats 1000000 in
theorem edge_polynomial : ∃ cells steps : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (source tape : Bits), fresh (edge κ mode source tape) ≤ cells.eval (source.length+κ) ∧
      (edge κ mode source tape).length ≤ steps.eval (source.length+κ) := by
  obtain ⟨p,cap⟩ := FramedEdgeTrials.rows_polynomial
  refine ⟨sampleCount*(2*p+2),sampleCount*(8*p+8),fun κ mode source tape => ?_⟩
  unfold edge
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | some accepted =>
    obtain ⟨n,D⟩ := accepted
    let x := source.length+κ
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
    let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput line).1
    let controls := BinarySolverOuterControls.edge n κ
    obtain ⟨dispatch,_,reader,_,actual,_⟩ := PhysicalSourceReadback.terminal_headers line
    have returned : (PhysicalSourceReadback.runWithTerminalCharge
      (PhysicalAmplifiedBinaryEdge.lineWithCost (PhysicalBinaryEdgeWire.decodeWithCost D).1).1).1=
        some (plan,dispatch,reader) := actual
    simp only [returned]
    have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
      simpa only [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value] using parsed
    have dims : n≤x := (ChargedSourceAssembly.edge_dimensions original).1.trans (Nat.le_add_right _ _)
    have row : rowsCount plan ≤ p.eval x := (cap parsed).trans (eval_mono _ (Nat.le_add_right _ _))
    have sample : controls.extra+1≤ sampleCount.eval x := by
      rw [BinarySolverOuterControls.edge_extra]
      exact samples_le n κ x dims (Nat.le_add_left _ _)
    exact widen line (PaidDirectEdgeWire.roundWithGadgetWork raw mode) controls.draws controls.extra controls.confidence plan tape p row sample

end DirectedFlowCutGap.FramedSolverStackLayout
