import DirectedFlowCutGap.PaidVertexRounding
import DirectedFlowCutGap.PaidVertexAmplification
import DirectedFlowCutGap.PhysicalSourceInputJoin

/-! Preserve the original fixed-instruction fractional dispatch, its terminal
readback, and the work of all reached rounds of the framed vertex solver. -/
namespace DirectedFlowCutGap.PaidFramedVertexWire

open BinaryArithmetic
open PhysicalCoverAccess (Read)
open PhysicalAmplifiedVertexSolver (Result)

private def addControls {n : ℕ} (paid : ℕ) (r : Result n) : Result n :=
  { r with roundingAndSelection := r.roundingAndSelection+paid }

def run {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Read (Result n) :=
  let controls := BinarySolverOuterControls.vertex n κ
  match PhysicalSourceReadback.run D with
  | none => (none,controls.paid)
  | some (plan,dispatch,reader) =>
      let r := PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode) controls.draws controls.extra
        controls.confidence plan dispatch reader tape
      (r.1.map (addControls controls.paid),controls.paid+dispatch+reader+r.2)

theorem run_value {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : (run κ mode D tape).1=PhysicalAmplifiedBinaryVertex.vertex κ mode D tape := by
  unfold run PhysicalAmplifiedBinaryVertex.vertex PhysicalAmplifiedVertexSolver.run
  dsimp only
  cases sourceResult : PhysicalSourceReadback.run D with
  | none => rfl
  | some phases =>
      obtain ⟨plan,dispatch,reader⟩ := phases
      simp only [Option.bind_some,PaidVertexAmplification.runWithPlan_value,PaidVertexRounding.runner_value]
      rfl

theorem run_paid {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) :
    let inputLength := (PhysicalSourceDispatch.input D).length
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval inputLength
    let controls := BinarySolverOuterControls.vertex n κ
    ∃ dispatch reader, dispatch ≤ PhysicalSourceDispatch.paidPolynomial.eval inputLength ∧
      reader ≤ PhysicalSourceReadback.planBound (1+bound) bound ∧
        (run κ mode D tape).2=controls.paid+dispatch+reader+
          (PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode) controls.draws controls.extra
            controls.confidence (PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1) dispatch reader tape).2 := by
  obtain ⟨dispatch,reader,program,hd,hr⟩ := PhysicalSourceReadback.run_eq D
  exact ⟨dispatch,reader,hd,hr,by simp only [run,program]⟩

def vertexWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n, Result n) := do
  let ⟨n,D⟩ ← PhysicalSourceInputJoin.vertex source
  let r := run κ mode D tape
  (r.1.map (fun cut => ⟨n,cut⟩),r.2)

attribute [local irreducible] run PhysicalAmplifiedBinaryVertex.vertex in
set_option maxHeartbeats 1100000 in
theorem vertex_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (vertexWithCost κ mode source tape).1=(PhysicalAmplifiedBinaryVertex.vertexWithCost κ mode source tape).1 := by
  have same : (ChargedSourceAssembly.vertex source).1=(PhysicalSourceInputJoin.vertex source).1 :=
    (ChargedSourceAssembly.vertex_value source).trans (PhysicalSourceInputJoin.vertex_value source).symm
  simp only [vertexWithCost,PhysicalAmplifiedBinaryVertex.vertexWithCost,Read.bind_value,PhysicalVertexSolver.prepareOn,same]
  generalize (PhysicalSourceInputJoin.vertex source).1=parsed
  cases parsed with
  | none => rfl
  | some input =>
      obtain ⟨n,D⟩ := input
      change (run κ mode D tape).1.map (fun cut => (⟨n,cut⟩ : Σ i, Result i)) =
        (PhysicalAmplifiedBinaryVertex.vertex κ mode D tape).map (fun cut => (⟨n,cut⟩ : Σ i, Result i))
      rw [run_value]

theorem complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (source tape : Bits) (parsed : EncodedVertexInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    ∃ r used, (vertexWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) r.output := by
  rw [vertex_value]
  exact PhysicalAmplifiedBinaryVertex.vertex_complete κ mode D source tape parsed enough

end DirectedFlowCutGap.PaidFramedVertexWire
