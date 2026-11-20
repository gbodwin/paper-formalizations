import DirectedFlowCutGap.DirectBinaryEdgeWireCost
import DirectedFlowCutGap.PhysicalSourceInputJoin

/-! Parse on the physical source heap, then use the existing direct edge
solver. This joins the successful-run recorded work. -/
namespace DirectedFlowCutGap.FramedDirectEdgeWire

open BinaryArithmetic Polynomial
open PhysicalAmplifiedEdgeSolver (EdgeResult)
open PhysicalIntegerRoundingCost (eval_mono)

def edgeWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n, EdgeResult n) :=
  let parsed := PhysicalSourceInputJoin.edge source
  (PhysicalVertexSolver.prepareOn (fun _ input => DirectBinaryEdgeWire.runOn κ mode input tape) parsed.1,
    parsed.2)

theorem edge_result (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithCost κ mode source tape).1=(DirectBinaryEdgeWire.edgeWithCost κ mode source tape).1 := by
  simp only [edgeWithCost,DirectBinaryEdgeWire.edgeWithCost,PhysicalSourceInputJoin.edge_value,
    ChargedSourceAssembly.edge_value]

theorem recorded_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (source tape : Bits) {n : ℕ} {r : EdgeResult n}, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ →
    (edgeWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection ≤
      p.eval (source.length+κ) := by
  obtain ⟨q,hq⟩ := DirectBinaryEdgeCost.wire_polynomial
  refine ⟨PhysicalSourceInputJoin.parsePolynomial+q,?_⟩
  intro κ mode source tape n r ran
  have directRan := (edge_result κ mode source tape).symm.trans ran
  have solve := hq κ mode source tape directRan
  have framing := ((PhysicalSourceInputJoin.edge_paid source).trans_eq
    (PhysicalSourceInputJoin.parsePolynomial_eval _).symm).trans
      (eval_mono PhysicalSourceInputJoin.parsePolynomial (Nat.le_add_right source.length κ))
  change (edgeWithCost κ mode source tape).2 ≤ _ at framing
  rw [eval_add]
  omega

theorem complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (source tape : Bits) (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used≤EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
        EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  rw [edge_result]
  exact DirectBinaryEdgeWire.complete κ mode D source tape parsed enough

end DirectedFlowCutGap.FramedDirectEdgeWire
