import DirectedFlowCutGap.PaidVertexRounding
import DirectedFlowCutGap.PaidVertexAmplification
import DirectedFlowCutGap.FramedDirectEdgeWire

/-! Keep the incurred work across the original framed edge entry. Output,
failure, old successful charge fields, and the unread tape agree pointwise
with the existing direct edge entry. -/
namespace DirectedFlowCutGap.PaidDirectEdgeWire

open BinaryArithmetic EncodedEdgeLineInput
open RetainedGridState (Flags)
open PhysicalCoverAccess (Read)
open PhysicalAmplifiedEdgeSolver (EdgeResult)
open PhysicalIntegerRounding (Result)

def roundOn {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Read (Result (lineSize n)) :=
  let graph := BinaryEdgeGadget.build D
  let r := PaidVertexRounding.runner mode T graph.1.data tape
  let setup := graph.2+prepared
  match r.1 with
  | none => (none,setup+r.2)
  | some cut =>
      let output := BinaryEdgeProjection.pullback graph.1 cut.mask
      (some ⟨output.1,cut.suffix,setup+cut.paid+output.2⟩,setup+r.2+output.2)

theorem roundOn_value {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    (roundOn D prepared mode T tape).1=PhysicalAmplifiedBinaryEdge.roundOn D prepared mode T tape := by
  unfold roundOn PhysicalAmplifiedBinaryEdge.roundOn
  dsimp only
  rw [← PaidVertexRounding.runner_value]
  cases (PaidVertexRounding.runner mode T (BinaryEdgeGadget.build D).1.data tape).1 <;> rfl

theorem roundOn_paid {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    let g := BinaryEdgeGadget.build D
    (roundOn D prepared mode T tape).2 ≤ g.2+prepared+(PaidVertexRounding.runner mode T g.1.data tape).2+
      BinaryEdgeProjection.pullbackBudget n g.1.size := by
  let graph := BinaryEdgeGadget.build D
  let inner := PaidVertexRounding.runner mode T graph.1.data tape
  unfold roundOn
  change (match inner.1 with
    | none => (none,graph.2+prepared+inner.2)
    | some cut =>
        let output := BinaryEdgeProjection.pullback graph.1 cut.mask
        (some (⟨output.1,cut.suffix,graph.2+prepared+cut.paid+output.2⟩ : Result (lineSize n)),
          graph.2+prepared+inner.2+output.2)).2 ≤ _
  cases inner.1 with
  | none => exact Nat.le_add_right _ _
  | some cut => exact Nat.add_le_add_left (BinaryEdgeProjection.pullback_paid graph.1 cut.mask) _

def round {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PaidVertexSampling.Runner (lineSize n) :=
  fun T r tape =>
    let input := BinaryEdgeProjection.roundingInput D r.weights
    roundOn input.1 input.2 mode T tape

theorem round_value {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) :
    (fun T r bits => (round D mode T r bits).1)=PhysicalAmplifiedBinaryEdge.round D mode := by
  funext T r tape
  exact roundOn_value _ _ _ _ _

private def finish {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) : Read (EdgeResult n) :=
  match r.1 with
  | none => (none,sunk+r.2)
  | some result =>
      let decoded := BinaryEdgeProjection.output D result.output
      (some ⟨decoded.1,result.suffix,result.dispatch,result.readback,result.roundingAndSelection+setup+decoded.2⟩,
        sunk+r.2+decoded.2)

private theorem finish_value {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finish D setup sunk r).1=r.1.map (PhysicalAmplifiedBinaryEdge.finish D setup) := by
  unfold finish
  cases r.1 <;> rfl

private theorem finish_paid {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finish D setup sunk r).2 ≤ sunk+r.2+BinaryEdgeProjection.outputBudget n := by
  unfold finish
  cases r.1 with
  | none => exact Nat.le_add_right _ _
  | some out => exact Nat.add_le_add_left (BinaryEdgeProjection.output_paid D out.output) _

private def runWithLineControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    Read (EdgeResult n) × ℕ :=
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let input := line.1
  let cover := BinaryFractionalGuesses.solveInput input.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := input.2+controls.paid
  let followed := PaidVertexAmplification.runWithPlan input.1 (round D mode) controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  (finish D setup (setup+cover.2+reader.2) followed,line.2)

def run {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Read (EdgeResult n) :=
  (runWithLineControl κ D mode tape).1

theorem run_value {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (run κ D mode tape).1=DirectBinaryEdgeWire.run κ D mode tape := by
  simp only [run,runWithLineControl,DirectBinaryEdgeWire.run,PhysicalAmplifiedBinaryEdge.lineWithCost,
    finish_value,PaidVertexAmplification.runWithPlan_value,round_value]

theorem phase_paid {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let controls := BinarySolverOuterControls.edge n κ
    let input := PhysicalAmplifiedBinaryEdge.lineWithCost D
    let cover := BinaryFractionalGuesses.solveInput input.1
    let reader := DirectBinaryEdgeWire.read cover.1
    (run κ D mode tape).2 ≤ input.2+controls.paid+cover.2+reader.2+
      (PaidVertexAmplification.runWithPlan input.1 (round D mode) controls.draws controls.extra
        controls.confidence reader.1 cover.2 reader.2 tape).2+BinaryEdgeProjection.outputBudget n := by
  unfold run runWithLineControl
  exact finish_paid D _ _ _

def runOnWithLineControl {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) × ℕ :=
  let input := PhysicalBinaryEdgeWire.decodeWithCost D
  let (r, line) := runWithLineControl κ input.1 mode tape
  ((r.1.map (fun out => { out with roundingAndSelection := out.roundingAndSelection+input.2 }),input.2+r.2),line)

def runOn {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) := (runOnWithLineControl κ mode D tape).1

theorem runOn_line_work {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : (runOnWithLineControl κ mode D tape).2 =
      (PhysicalAmplifiedBinaryEdge.lineWithControl (PhysicalBinaryEdgeWire.decodeWithCost D).1).2 := rfl

theorem runOn_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : runOn κ mode D tape =
      let input := PhysicalBinaryEdgeWire.decodeWithCost D
      let r := run κ input.1 mode tape
      (r.1.map (fun out => { out with roundingAndSelection := out.roundingAndSelection+input.2 }),input.2+r.2) := rfl

theorem runOn_value {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOn κ mode D tape).1=DirectBinaryEdgeWire.runOn κ mode D tape := by
  simp only [runOn_reference,DirectBinaryEdgeWire.runOn,run_value]

def edgeWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,EdgeResult n) := do
  let ⟨n,D⟩ ← PhysicalSourceInputJoin.edge source
  let r := runOn κ mode D tape
  (r.1.map (fun out => ⟨n,out⟩),r.2)

def edgeWithLineControl (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × ℕ :=
  let input := PhysicalSourceInputJoin.edge source
  match input.1 with
  | none => ((none,input.2),0)
  | some ⟨n,D⟩ =>
      let (r, line) := runOnWithLineControl κ mode D tape
      ((r.1.map (fun out => ⟨n,out⟩),input.2+r.2),line)

theorem edgeWithLineControl_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithLineControl κ mode source tape).1=edgeWithCost κ mode source tape := by
  change (edgeWithLineControl κ mode source tape).1 =
    Read.bind (PhysicalSourceInputJoin.edge source) (fun data =>
      let r := runOn κ mode data.2 tape
      (r.1.map (fun out => ⟨data.1,out⟩),r.2))
  unfold edgeWithLineControl Read.bind
  dsimp only
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some input =>
      obtain ⟨n,D⟩ := input
      rfl

theorem edge_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithCost κ mode source tape).1=(FramedDirectEdgeWire.edgeWithCost κ mode source tape).1 := by
  simp only [edgeWithCost,FramedDirectEdgeWire.edgeWithCost,PhysicalVertexSolver.prepareOn,Read.bind_value]
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some data =>
      rcases data with ⟨n,D⟩
      simp only [Option.bind_some,runOn_value]

theorem complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (source tape : Bits) (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used≤EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
        EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  rw [edge_value]
  exact FramedDirectEdgeWire.complete κ mode D source tape parsed enough

end DirectedFlowCutGap.PaidDirectEdgeWire
