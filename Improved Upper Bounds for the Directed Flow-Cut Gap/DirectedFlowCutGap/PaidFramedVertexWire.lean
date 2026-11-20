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

private def runFromSource {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (source : Option (PhysicalCoverReader.Plan n × ℕ × ℕ)) (tape : Bits) : Read (Result n) :=
  let controls := BinarySolverOuterControls.vertex n κ
  match source with
  | none => (none,controls.paid)
  | some (plan,dispatch,reader) =>
      let r := PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode) controls.draws controls.extra
        controls.confidence plan dispatch reader tape
      (r.1.map (addControls controls.paid),controls.paid+dispatch+reader+r.2)

def run {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Read (Result n) := runFromSource κ mode D (PhysicalSourceReadback.run D) tape

def runWithCacheWork {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Read (Result n) × ℕ :=
  let source := PhysicalSourceReadback.runWithCacheCharge D
  (runFromSource κ mode D source.1 tape,source.2)

theorem runWithCacheWork_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    (runWithCacheWork κ mode D tape).1=run κ mode D tape := by
  simp only [runWithCacheWork,run,PhysicalSourceReadback.cache_readout_value]

theorem run_cache_work {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    (runWithCacheWork κ mode D tape).2=(PhysicalSourceReadback.runWithCacheCharge D).2 := rfl

def runWithTerminalWork {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) : Read (Result n) × ℕ :=
  let source := PhysicalSourceReadback.runWithTerminalCharge D
  (runFromSource κ mode D source.1 tape,source.2)

def runWithTerminalScalarWork {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) : Read (Result n) × ℕ :=
  let source := PhysicalSourceReadback.runWithTerminalCharge D
  let controls := BinarySolverOuterControls.vertex n κ
  match source.1 with
  | none => ((none,controls.paid),source.2)
  | some (plan,dispatch,reader) =>
      let r := PaidVertexAmplification.runWithPlanScalarWork D (PaidVertexRounding.runner mode)
        controls.draws controls.extra controls.confidence plan dispatch reader tape
      ((r.1.1.map (addControls controls.paid),controls.paid+dispatch+reader+r.1.2),source.2+r.2)

theorem run_terminal_scalar_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    (runWithTerminalScalarWork κ mode D tape).1=(runWithTerminalWork κ mode D tape).1 := by
  simp only [runWithTerminalScalarWork,runWithTerminalWork,runFromSource]
  cases (PhysicalSourceReadback.runWithTerminalCharge D).1 with
  | none => rfl
  | some input =>
    obtain ⟨plan,dispatch,reader⟩ := input
    simp only [PaidVertexAmplification.runWithPlanScalarWork_reference]

theorem run_terminal_scalar_paid {n B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits)
    (width : ((runWithTerminalWork κ mode D tape).1.2+4).size ≤ B) :
    (runWithTerminalScalarWork κ mode D tape).2 ≤ (runWithTerminalWork κ mode D tape).2+
      (((BinarySolverOuterControls.vertex n κ).extra+2)*PaidVertexAmplification.sampleControlBudget B+1) := by
  let controls := BinarySolverOuterControls.vertex n κ
  simp only [runWithTerminalScalarWork,runWithTerminalWork,runFromSource] at width ⊢
  cases h : (PhysicalSourceReadback.runWithTerminalCharge D).1 with
  | none => exact Nat.le_add_right _ _
  | some input =>
    obtain ⟨plan,dispatch,reader⟩ := input
    rw [h] at width
    let old := PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape
    change (controls.paid+dispatch+reader+old.2+4).size ≤ B at width
    have amp : (old.2+4).size ≤ B :=
      (Nat.size_le_size (Nat.add_le_add_right (Nat.le_add_left _ _) 4)).trans width
    exact Nat.add_le_add_left (PaidVertexAmplification.runWithPlanScalarWork_paid D
      (PaidVertexRounding.runner mode) controls.draws controls.extra controls.confidence plan
      dispatch reader tape amp) _

theorem runWithTerminalWork_comparison {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) :
    let raw := PhysicalSourceReadback.runWithTerminalCharge D
    let measured := runWithTerminalWork κ mode D tape
    measured.1.1.map Result.observe=(run κ mode D tape).1.map Result.observe ∧
      measured.1.2+measured.2 ≤ (run κ mode D tape).2+
        (((raw.1.map (fun p => p.2.2)).getD 0)+raw.2) := by
  let controls := BinarySolverOuterControls.vertex n κ
  let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  obtain ⟨dispatch,oldReader,reader,old,measured,_⟩ := PhysicalSourceReadback.terminal_headers D
  let before := PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode)
    controls.draws controls.extra controls.confidence plan dispatch oldReader tape
  let after := PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode)
    controls.draws controls.extra controls.confidence plan dispatch reader tape
  let cached := (PhysicalSourceReadback.runWithTerminalCharge D).2
  have same := PaidVertexAmplification.runWithPlan_headers D (PaidVertexRounding.runner mode)
    controls.draws controls.extra controls.confidence plan dispatch oldReader dispatch reader tape
  have paid : after.2=before.2 :=
    congrArg (fun q : Option (EncodedVertexSolver.Output n × Bits) × ℕ => q.2) same
  have observed : after.1.map Result.observe=before.1.map Result.observe :=
    congrArg (fun q : Option (EncodedVertexSolver.Output n × Bits) × ℕ => q.1) same
  have unchanged : Result.observe ∘ addControls (n := n) controls.paid=Result.observe := rfl
  simp only [runWithTerminalWork,run,runFromSource,old,measured,Option.map_some,Option.getD_some]
  change _ ∧ _ + _ ≤ _ + (reader + _)
  constructor
  · change (after.1.map (addControls controls.paid)).map Result.observe =
      (before.1.map (addControls controls.paid)).map Result.observe
    simpa only [Option.map_map,unchanged] using observed
  · change controls.paid+dispatch+reader+after.2+cached ≤
      controls.paid+dispatch+oldReader+before.2+(reader+cached)
    rw [paid]
    omega

theorem run_value {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : (run κ mode D tape).1=PhysicalAmplifiedBinaryVertex.vertex κ mode D tape := by
  unfold run runFromSource PhysicalAmplifiedBinaryVertex.vertex PhysicalAmplifiedVertexSolver.run
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
  exact ⟨dispatch,reader,hd,hr,by simp only [run,runFromSource,program]⟩

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
