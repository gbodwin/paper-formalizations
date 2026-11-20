import DirectedFlowCutGap.PaidDirectEdgeWire
import DirectedFlowCutGap.PaidVertexRoundingCost
namespace DirectedFlowCutGap.PaidDirectEdgeWire

open BinaryArithmetic BinaryRational Polynomial EncodedEdgeLineInput
open PhysicalBinaryEdgeCost (roundPolynomial widthPolynomial roundPad)
open BinaryEdgeProjection (pullbackBudget roundingBudget)
open PhysicalAmplifiedBinaryVertex (arithmeticPolynomial)

set_option maxHeartbeats 1600000 in
theorem round_paid (q : Polynomial ℕ)
    (cert : ∀ {n b T y : ℕ}, n ≤ y → T ≤ y → b ≤ y+1+PhysicalSourceDispatch.instructionPolynomial.eval y →
      ∀ (mode : ChargedVertexModes.Mode) (D : EncodedUnitCostReplication.Input n),
      VertexReductionWidths.InputFits D b → ∀ tape, (PaidVertexRounding.runner mode T D tape).2 ≤ q.eval y)
    {n b T z : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode)
    (dimensions : BinaryEdgeGadget.dimension n ≤ z) (hn : n ≤ z) (trials : T ≤ z)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits)
    (fits : BinaryEdgeGadget.InputFits (roundingInput D r.weights) b) (width : b ≤ widthPolynomial.eval z) :
    (round D mode T r tape).2 ≤ (roundPolynomial q).eval z := by
  let p := BinaryEdgeGadget.build (roundingInput D r.weights)
  let g := p.1
  let y := roundPad.eval z
  let w := widthPolynomial.eval z
  change (roundOn (BinaryEdgeProjection.roundingInput D r.weights).1
    (BinaryEdgeProjection.roundingInput D r.weights).2 mode T tape).2 ≤ _
  rw [BinaryEdgeProjection.roundingInput_value]
  refine (roundOn_paid (roundingInput D r.weights) (BinaryEdgeProjection.roundingInput D r.weights).2 mode T tape).trans ?_
  have dim : g.size ≤ z := (BinaryEdgeGadget.size_le _).trans dimensions
  have hy : y=z+z^2*(w+1)+z+1 := by
    simp only [y,roundPad,w,eval_add,eval_X,eval_pow,eval_mul,eval_one]
  have more : z ≤ y := by omega
  have fields := BinaryEdgeGadget.fields_fit (roundingInput D r.weights) fits
  have small : n^2*(b+1) ≤ z^2*(w+1) := by gcongr
  have bytes : n^2*(b+1)+n+1 ≤ y+1+PhysicalSourceDispatch.instructionPolynomial.eval y := by omega
  have inner : (PaidVertexRounding.runner mode T g.data tape).2 ≤ q.eval y :=
    cert (dim.trans more) (trials.trans more) bytes mode _ fields tape
  have assembly : p.2 ≤ BinaryEdgeGadget.budget z w :=
    (BinaryEdgeGadget.build_paid _ fits).trans (BinaryEdgeGadget.budget_mono hn width)
  have project := (BinaryEdgeProjection.roundingInput_paid D r.weights).trans
    (show roundingBudget n ≤ roundingBudget z by unfold roundingBudget BinaryEdgeProjection.readbackBudget; gcongr)
  have liftPull : pullbackBudget n g.size ≤ pullbackBudget z (BinaryEdgeGadget.dimension z) := by
    have larger : g.size ≤ BinaryEdgeGadget.dimension z := by
      apply (BinaryEdgeGadget.size_le (roundingInput D r.weights)).trans
      unfold BinaryEdgeGadget.dimension
      gcongr
    unfold pullbackBudget
    apply Nat.add_le_add _ (BinaryEdgeProjection.lineMaskBudget_mono hn)
    unfold BinaryEdgeProjection.maskBudget BinaryEdgeGadget.incidentBudget
    gcongr
  simp only [roundPolynomial,BinaryEdgeProjection.pullbackBudget_eval,roundingBudget,BinaryEdgeProjection.readbackBudget,
    BinaryEdgeGadget.dimension,eval_add,eval_comp,eval_X,eval_ofNat,eval_mul,eval_pow,BinaryEdgeGadget.budget_eval]
  change p.2+(BinaryEdgeProjection.roundingInput D r.weights).2+(PaidVertexRounding.runner mode T g.data tape).2+
      pullbackBudget n g.size ≤ (q.eval y+arithmeticPolynomial.eval y)+BinaryEdgeGadget.budget z w+
        pullbackBudget z (BinaryEdgeGadget.dimension z)+roundingBudget z
  omega

end DirectedFlowCutGap.PaidDirectEdgeWire
