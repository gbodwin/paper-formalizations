import DirectedFlowCutGap.PaidFramedEdgeCost
import DirectedFlowCutGap.PaidFramedVertexCost

/-! Carry the modeled framer record count through the paid edge and vertex
source solvers. The record count survives rejection and tape exhaustion. -/
namespace DirectedFlowCutGap.FramedSolverRecords

open BinaryArithmetic Polynomial
open PhysicalCoverAccess (Read)
open PhysicalAmplifiedVertexSolver (Result)
open PhysicalAmplifiedEdgeSolver (EdgeResult)

def vertex (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,Result n) × ℕ :=
  let parsed := PhysicalSourceInputJoin.vertexWithFramingRecords source
  let result := Read.bind parsed.1 fun input =>
    let r := PaidFramedVertexWire.run κ mode input.2 tape
    (r.1.map (fun out => ⟨input.1,out⟩),r.2)
  (result,parsed.2)

def edge (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,EdgeResult n) × ℕ :=
  let parsed := PhysicalSourceInputJoin.edgeWithFramingRecords source
  let result := Read.bind parsed.1 fun input =>
    let r := PaidDirectEdgeWire.runOn κ mode input.2 tape
    (r.1.map (fun out => ⟨input.1,out⟩),r.2)
  (result,parsed.2)

theorem vertex_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertex κ mode source tape).1=PaidFramedVertexWire.vertexWithCost κ mode source tape := by
  unfold vertex PaidFramedVertexWire.vertexWithCost
  dsimp only
  rw [PhysicalSourceInputJoin.vertex_framing_records_value]
  congr 1

theorem edge_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edge κ mode source tape).1=PaidDirectEdgeWire.edgeWithCost κ mode source tape := by
  unfold edge PaidDirectEdgeWire.edgeWithCost
  dsimp only
  rw [PhysicalSourceInputJoin.edge_framing_records_value]
  congr 1

theorem records_bound (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertex κ mode source tape).2 ≤ PhysicalSourceInputJoin.framingBudget source.length ∧
      (edge κ mode source tape).2 ≤ PhysicalSourceInputJoin.framingBudget source.length :=
  PhysicalSourceInputJoin.framing_records_bound source

private theorem framingBudget_eval (s : ℕ) :
    (PhysicalSourceInputJoin.framingBudget (X : Polynomial ℕ)).eval s =
      PhysicalSourceInputJoin.framingBudget s := by
  simp only [PhysicalSourceInputJoin.framingBudget,eval_X,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

theorem vertex_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    let r := vertex κ mode source tape
    r.1.2+r.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p, paid⟩ := PaidFramedVertexWire.wire_polynomial
  refine ⟨p+PhysicalSourceInputJoin.framingBudget X,?_⟩
  intro κ mode source tape
  have frame := ((records_bound κ mode source tape).1.trans_eq (framingBudget_eval source.length).symm).trans
    (PhysicalIntegerRoundingCost.eval_mono _ (Nat.le_add_right source.length κ))
  simp only [eval_add,vertex_reference]
  exact Nat.add_le_add (paid κ mode source tape) frame

theorem edge_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    let r := edge κ mode source tape
    r.1.2+r.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p, paid⟩ := PaidDirectEdgeWire.wire_polynomial
  refine ⟨p+PhysicalSourceInputJoin.framingBudget X,?_⟩
  intro κ mode source tape
  have frame := ((records_bound κ mode source tape).2.trans_eq (framingBudget_eval source.length).symm).trans
    (PhysicalIntegerRoundingCost.eval_mono _ (Nat.le_add_right source.length κ))
  simp only [eval_add,edge_reference]
  exact Nat.add_le_add (paid κ mode source tape) frame

end DirectedFlowCutGap.FramedSolverRecords
