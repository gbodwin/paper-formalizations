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

private def roundOnUsing {n : ℕ} {D : EncodedEdgeGadget.Input n}
    (graph : EncodedEdgeGadget.Prepared D × ℕ) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Read (Result (lineSize n)) × ℕ :=
  let r := PaidVertexRounding.runner mode T graph.1.data tape
  let setup := graph.2+prepared
  match r.1 with
  | none => ((none,setup+r.2),0)
  | some cut =>
      let output := BinaryEdgeProjection.pullbackWithControl graph.1 cut.mask
      ((some ⟨output.1.1,cut.suffix,setup+cut.paid+output.1.2⟩,setup+r.2+output.1.2),output.2)

def roundOnWithControl {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Read (Result (lineSize n)) × ℕ :=
  roundOnUsing (BinaryEdgeGadget.build D) prepared mode T tape

def roundOn {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Read (Result (lineSize n)) :=
  (roundOnWithControl D prepared mode T tape).1

theorem roundOn_control_paid {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    (roundOnWithControl D prepared mode T tape).2 ≤
      BinaryEdgeProjection.pullbackControlBudget n (BinaryEdgeGadget.dimension n) := by
  let graph := BinaryEdgeGadget.build D
  unfold roundOnWithControl roundOnUsing
  dsimp only
  cases (PaidVertexRounding.runner mode T graph.1.data tape).1 with
  | none => exact Nat.zero_le _
  | some cut =>
      exact (BinaryEdgeProjection.pullback_control_paid graph.1 cut.mask).trans
        (BinaryEdgeProjection.pullbackControlBudget_mono le_rfl (BinaryEdgeGadget.size_le D))

theorem roundOn_value {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) :
    (roundOn D prepared mode T tape).1=PhysicalAmplifiedBinaryEdge.roundOn D prepared mode T tape := by
  unfold roundOn roundOnWithControl roundOnUsing PhysicalAmplifiedBinaryEdge.roundOn
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
  unfold roundOn roundOnWithControl roundOnUsing
  dsimp only
  cases inner.1 with
  | none => exact Nat.le_add_right _ _
  | some cut => exact Nat.add_le_add_left (BinaryEdgeProjection.pullback_paid graph.1 cut.mask) _

def roundWithControl {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) : Read (Result (lineSize n)) × ℕ :=
  let input := BinaryEdgeProjection.roundingInputWithControl D r.weights
  let result := roundOnWithControl input.1.1 input.1.2 mode T tape
  (result.1,input.2+result.2)

def round {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PaidVertexSampling.Runner (lineSize n) :=
  fun T r tape => (roundWithControl D mode T r tape).1

def roundControlBudget {R : Type*} [Semiring R] (n : R) : R :=
  BinaryEdgeProjection.gridControlBudget n 4 (BinaryVectorAccess.budget (n*2+n*n))+
    BinaryEdgeProjection.pullbackControlBudget n (BinaryEdgeGadget.dimension n)

theorem round_control_paid {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) :
    (roundWithControl D mode T r tape).2 ≤ roundControlBudget n :=
  Nat.add_le_add (BinaryEdgeProjection.roundingInput_control_paid D r.weights) (roundOn_control_paid _ _ _ _ _)

def roundWithGadgetControl {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) : Read (Result (lineSize n)) × ℕ :=
  let input := BinaryEdgeProjection.roundingInputWithControl D r.weights
  let graph := BinaryEdgeGadget.buildWithControl input.1.1
  let result := roundOnUsing graph.1 input.1.2 mode T tape
  (result.1,input.2+result.2+graph.2)

theorem roundWithGadgetControl_reference {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) :
    (roundWithGadgetControl D mode T r tape).1=round D mode T r tape := by
  simp only [roundWithGadgetControl,round,roundWithControl,roundOnWithControl,BinaryEdgeGadget.build_control_projection]

theorem roundWithGadget_control_paid {n b : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits)
    (fits : BinaryEdgeGadget.InputFits (roundingInput D r.weights) b) :
    (roundWithGadgetControl D mode T r tape).2 ≤ roundControlBudget n+BinaryEdgeGadget.controlBudget n b := by
  let input := BinaryEdgeProjection.roundingInputWithControl D r.weights
  have raw : input.1.1=roundingInput D r.weights := BinaryEdgeProjection.roundingInput_value D r.weights
  have paid := BinaryEdgeGadget.build_control_paid input.1.1 (raw ▸ fits)
  unfold roundWithGadgetControl
  dsimp only
  rw [BinaryEdgeGadget.build_control_projection]
  exact Nat.add_le_add (round_control_paid D mode T r tape) paid

theorem round_value {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) :
    (fun T r bits => (round D mode T r bits).1)=PhysicalAmplifiedBinaryEdge.round D mode := by
  funext T r tape
  exact roundOn_value _ _ _ _ _

private def finishWithControl {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) : Read (EdgeResult n) × ℕ :=
  match r.1 with
  | none => ((none,sunk+r.2),0)
  | some result =>
      let output := BinaryEdgeProjection.outputWithControl D result.output
      let decoded := output.1
      ((some ⟨decoded.1,result.suffix,result.dispatch,result.readback,result.roundingAndSelection+setup+decoded.2⟩,
        sunk+r.2+decoded.2),output.2)

private def finish {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) : Read (EdgeResult n) :=
  (finishWithControl D setup sunk r).1

private theorem finish_control_paid {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finishWithControl D setup sunk r).2 ≤ BinaryEdgeProjection.outputControlBudget n := by
  unfold finishWithControl
  cases r.1 with
  | none => exact Nat.zero_le _
  | some result => exact BinaryEdgeProjection.output_control_paid D result.output

private theorem finish_value {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finish D setup sunk r).1=r.1.map (PhysicalAmplifiedBinaryEdge.finish D setup) := by
  unfold finish finishWithControl
  cases r.1 <;> rfl

private theorem finish_control_value {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finishWithControl D setup sunk r).1.1=r.1.map (PhysicalAmplifiedBinaryEdge.finish D setup) :=
  finish_value D setup sunk r

private theorem finish_paid {n : ℕ} (D : Input n) (setup sunk : ℕ)
    (r : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))) :
    (finish D setup sunk r).2 ≤ sunk+r.2+BinaryEdgeProjection.outputBudget n := by
  unfold finish finishWithControl
  cases r.1 with
  | none => exact Nat.le_add_right _ _
  | some out => exact Nat.add_le_add_left (BinaryEdgeProjection.output_paid D out.output) _

private def runWithRunner {n : ℕ} (κ : ℕ) (D : Input n) (runner : PaidVertexSampling.Runner (lineSize n))
    (tape : Bits) :
    Read (EdgeResult n) × (ℕ × ℕ) :=
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let input := line.1
  let cover := BinaryFractionalGuesses.solveInput input.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := input.2+controls.paid
  let followed := PaidVertexAmplification.runWithPlan input.1 runner controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  let output := finishWithControl D setup (setup+cover.2+reader.2) followed
  (output.1,(line.2,output.2))

private def runWithBoundaryControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    Read (EdgeResult n) × (ℕ × ℕ) := runWithRunner κ D (round D mode) tape

private def runWithLineControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    Read (EdgeResult n) × ℕ :=
  let result := runWithBoundaryControl κ D mode tape
  (result.1,result.2.1)

def run {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Read (EdgeResult n) :=
  (runWithLineControl κ D mode tape).1

theorem run_value {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (run κ D mode tape).1=DirectBinaryEdgeWire.run κ D mode tape := by
  simp only [run,runWithLineControl,runWithBoundaryControl,runWithRunner,DirectBinaryEdgeWire.run,
    PhysicalAmplifiedBinaryEdge.lineWithCost,finish_control_value,PaidVertexAmplification.runWithPlan_value,round_value]

theorem phase_paid {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let controls := BinarySolverOuterControls.edge n κ
    let input := PhysicalAmplifiedBinaryEdge.lineWithCost D
    let cover := BinaryFractionalGuesses.solveInput input.1
    let reader := DirectBinaryEdgeWire.read cover.1
    (run κ D mode tape).2 ≤ input.2+controls.paid+cover.2+reader.2+
      (PaidVertexAmplification.runWithPlan input.1 (round D mode) controls.draws controls.extra
        controls.confidence reader.1 cover.2 reader.2 tape).2+BinaryEdgeProjection.outputBudget n := by
  unfold run runWithLineControl runWithBoundaryControl runWithRunner
  exact finish_paid D _ _ _

structure BoundaryWork where
  prices : ℕ
  line : ℕ
  output : ℕ
  deriving Repr

def BoundaryWork.total (w : BoundaryWork) : ℕ := w.prices+w.line+w.output

private def runOnWithRoundRunner {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (choose : Input n → PaidVertexSampling.Runner (lineSize n)) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  let measured := PhysicalBinaryEdgeWire.decodeWithControl D
  let input := measured.1
  let r := runWithRunner κ input.1 (choose input.1) tape
  ((r.1.1.map (fun out => { out with roundingAndSelection := out.roundingAndSelection+input.2 }),input.2+r.1.2),
    ⟨measured.2,r.2.1,r.2.2⟩)

def runOnWithBoundaryControl {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) × BoundaryWork := runOnWithRoundRunner κ D (fun input => round input mode) tape

theorem runOn_prices_work {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : (runOnWithBoundaryControl κ mode D tape).2.prices =
      (PhysicalBinaryEdgeWire.decodeWithControl D).2 := rfl

theorem runOn_output_paid {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : (runOnWithBoundaryControl κ mode D tape).2.output ≤ BinaryEdgeProjection.outputControlBudget n :=
  finish_control_paid _ _ _ _

def runOnWithLineControl {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) × ℕ :=
  let result := runOnWithBoundaryControl κ mode D tape
  (result.1,result.2.line)

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

def edgeWithBoundaryControl (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × BoundaryWork :=
  let input := PhysicalSourceInputJoin.edge source
  match input.1 with
  | none => ((none,input.2),⟨0,0,0⟩)
  | some ⟨n,D⟩ =>
      let r := runOnWithBoundaryControl κ mode D tape
      ((r.1.1.map (fun out => ⟨n,out⟩),input.2+r.1.2),r.2)

def edgeWithLineControl (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × ℕ :=
  let r := edgeWithBoundaryControl κ mode source tape
  (r.1,r.2.line)

theorem edgeWithLineControl_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithLineControl κ mode source tape).1=edgeWithCost κ mode source tape := by
  change (edgeWithLineControl κ mode source tape).1 =
    Read.bind (PhysicalSourceInputJoin.edge source) (fun data =>
      let r := runOn κ mode data.2 tape
      (r.1.map (fun out => ⟨data.1,out⟩),r.2))
  unfold edgeWithLineControl edgeWithBoundaryControl Read.bind
  dsimp only
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some input =>
      obtain ⟨n,D⟩ := input
      rfl

theorem edgeWithBoundaryControl_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithBoundaryControl κ mode source tape).1=edgeWithCost κ mode source tape :=
  edgeWithLineControl_value κ mode source tape

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

private def roundWithWork {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PaidVertexSampling.Runner (lineSize n) :=
  fun T input tape =>
    let r := roundWithControl D mode T input tape
    (r.1.1,r.1.2+r.2)

def runWithRoundWork {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Read (EdgeResult n) :=
  (runWithRunner κ D (roundWithWork D mode) tape).1

theorem runWithRoundWork_value {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (runWithRoundWork κ D mode tape).1=(run κ D mode tape).1 := by
  simp only [runWithRoundWork,run,runWithLineControl,runWithBoundaryControl,runWithRunner,
    finish_control_value,PaidVertexAmplification.runWithPlan_value,roundWithWork,round]

private theorem finish_extra {n : ℕ} (D : Input n) (setup sunk : ℕ)
    {a b : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))} {cap : ℕ}
    (same : b.1=a.1) (extra : b.2≤a.2+cap) : (finish D setup sunk b).2≤(finish D setup sunk a).2+cap := by
  unfold finish finishWithControl
  rw [same]
  cases a.1 <;> dsimp only <;> omega

theorem runWithRoundWork_extra {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let controls := BinarySolverOuterControls.edge n κ
    let input := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    let cover := BinaryFractionalGuesses.solveInput input
    let reader := DirectBinaryEdgeWire.read cover.1
    (runWithRoundWork κ D mode tape).2 ≤ (run κ D mode tape).2+
      (controls.extra+1)*(ChargedPhysicalVertexSolver.rowsCount reader.1*roundControlBudget n) := by
  let controls := BinarySolverOuterControls.edge n κ
  let input := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let cover := BinaryFractionalGuesses.solveInput input.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := input.2+controls.paid
  let old := PaidVertexAmplification.runWithPlan input.1 (round D mode) controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  let measured := PaidVertexAmplification.runWithPlan input.1 (roundWithWork D mode) controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  have same : measured.1=old.1 := by
    simp only [measured,old,PaidVertexAmplification.runWithPlan_value,roundWithWork,round]
  have extra := PaidVertexAmplification.runWithPlan_extra input.1 (round D mode) (roundWithWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 (roundControlBudget n) tape
    (fun _ _ _ => rfl)
    (fun T row suffix => Nat.add_le_add_left (round_control_paid D mode T row suffix) _)
  change (finish D setup (setup+cover.2+reader.2) measured).2 ≤
    (finish D setup (setup+cover.2+reader.2) old).2+
      (controls.extra+1)*(ChargedPhysicalVertexSolver.rowsCount reader.1*roundControlBudget n)
  exact finish_extra D _ _ same extra

abbrev Runner := ∀ {n : ℕ}, ℕ → Input n → ChargedVertexModes.Mode → Bits → Read (EdgeResult n)

def runOnWithRunner {n : ℕ} (runner : Runner) (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) :=
  let raw := PhysicalBinaryEdgeWire.decodeWithCost D
  let r := runner κ raw.1 mode tape
  (r.1.map (fun out => {out with roundingAndSelection := out.roundingAndSelection+raw.2}),raw.2+r.2)

def runOnWithRoundWork {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Read (EdgeResult n) := runOnWithRunner runWithRoundWork κ mode D tape

def edgeWithRunner (runner : Runner) (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) := do
  let ⟨n,D⟩ ← PhysicalSourceInputJoin.edge source
  let r := runOnWithRunner runner κ mode D tape
  (r.1.map (fun out => ⟨n,out⟩),r.2)

def edgeWithRoundWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,EdgeResult n) :=
  edgeWithRunner runWithRoundWork κ mode source tape

theorem edgeWithRunner_value (runner : Runner)
    (value : ∀ {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits),
      (runner κ D mode tape).1=(run κ D mode tape).1)
    (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithRunner runner κ mode source tape).1=(edgeWithCost κ mode source tape).1 := by
  simp only [edgeWithRunner,edgeWithCost,Read.bind_value]
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some input =>
      rcases input with ⟨n,D⟩
      simp only [Option.bind_some,runOnWithRunner,runOn_reference,value]

theorem edgeWithRoundWork_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithRoundWork κ mode source tape).1=(edgeWithCost κ mode source tape).1 :=
  edgeWithRunner_value runWithRoundWork runWithRoundWork_value κ mode source tape

private def roundWithGadgetWork {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PaidVertexSampling.Runner (lineSize n) :=
  fun T input tape =>
    let r := roundWithGadgetControl D mode T input tape
    (r.1.1,r.1.2+r.2)

def runWithGadgetWork {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Read (EdgeResult n) :=
  (runWithRunner κ D (roundWithGadgetWork D mode) tape).1

theorem runWithGadgetWork_value {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (runWithGadgetWork κ D mode tape).1=(run κ D mode tape).1 := by
  simp only [runWithGadgetWork,run,runWithLineControl,runWithBoundaryControl,runWithRunner,
    finish_control_value,PaidVertexAmplification.runWithPlan_value,roundWithGadgetWork,roundWithGadgetControl_reference]

theorem runWithGadgetWork_extra {n b : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits)
    (fits : let input := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
      let cover := BinaryFractionalGuesses.solveInput input
      let reader := DirectBinaryEdgeWire.read cover.1
      ∀ rows, reader.1=.covers rows → ∀ y ∈ rows, BinaryEdgeGadget.InputFits (roundingInput D y) b) :
    let controls := BinarySolverOuterControls.edge n κ
    let input := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    let cover := BinaryFractionalGuesses.solveInput input
    let reader := DirectBinaryEdgeWire.read cover.1
    (runWithGadgetWork κ D mode tape).2 ≤ (run κ D mode tape).2+
      (controls.extra+1)*(ChargedPhysicalVertexSolver.rowsCount reader.1*
        (roundControlBudget n+BinaryEdgeGadget.controlBudget n b)) := by
  let controls := BinarySolverOuterControls.edge n κ
  let input := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let cover := BinaryFractionalGuesses.solveInput input.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := input.2+controls.paid
  let old := PaidVertexAmplification.runWithPlan input.1 (round D mode) controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  let measured := PaidVertexAmplification.runWithPlan input.1 (roundWithGadgetWork D mode) controls.draws controls.extra
    controls.confidence reader.1 cover.2 reader.2 tape
  let cap := roundControlBudget n+BinaryEdgeGadget.controlBudget n b
  have same : measured.1=old.1 := by
    simp only [measured,old,PaidVertexAmplification.runWithPlan_value,roundWithGadgetWork,roundWithGadgetControl_reference]
  have extra := PaidVertexAmplification.runWithPlan_extra_on_rows input.1 (round D mode) (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 cap tape
    (fun T y bits => by
      change (roundWithGadgetControl D mode T y bits).1.1=(round D mode T y bits).1
      rw [roundWithGadgetControl_reference])
    (fun rows got y member bits => by
      unfold roundWithGadgetWork
      dsimp only
      rw [roundWithGadgetControl_reference]
      exact Nat.add_le_add_left (roundWithGadget_control_paid D mode _ _ bits (fits rows got y member)) _)
  change (finish D setup (setup+cover.2+reader.2) measured).2 ≤
    (finish D setup (setup+cover.2+reader.2) old).2+
      (controls.extra+1)*(ChargedPhysicalVertexSolver.rowsCount reader.1*cap)
  exact finish_extra D _ _ same extra

def edgeWithGadgetWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,EdgeResult n) :=
  edgeWithRunner runWithGadgetWork κ mode source tape

theorem edgeWithGadgetWork_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithGadgetWork κ mode source tape).1=(edgeWithCost κ mode source tape).1 :=
  edgeWithRunner_value runWithGadgetWork runWithGadgetWork_value κ mode source tape

private theorem finish_output_work_same {n : ℕ} (D : Input n) (setup sunk : ℕ)
    {a b : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))} (same : b.1=a.1) :
    (finishWithControl D setup sunk b).2=(finishWithControl D setup sunk a).2 := by
  unfold finishWithControl
  rw [same]
  cases a.1 <;> rfl

private theorem runWithRunner_boundaries_same {n : ℕ} (κ : ℕ) (D : Input n)
    (old newer : PaidVertexSampling.Runner (lineSize n)) (tape : Bits)
    (same : ∀ T input bits, (newer T input bits).1=(old T input bits).1) :
    (runWithRunner κ D newer tape).2=(runWithRunner κ D old tape).2 := by
  have observed : (fun T input bits => (newer T input bits).1)=(fun T input bits => (old T input bits).1) :=
    funext fun T => funext fun input => funext fun bits => same T input bits
  unfold runWithRunner
  dsimp only
  congr 1
  apply finish_output_work_same
  simp only [PaidVertexAmplification.runWithPlan_value,observed]

private def runOnWithGadgetBoundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  runOnWithRoundRunner κ D (fun input => roundWithGadgetWork input mode) tape

private theorem runOn_gadgetBoundary_paid_value {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOnWithGadgetBoundary κ mode D tape).1=runOnWithRunner runWithGadgetWork κ mode D tape := rfl

private theorem runOn_gadgetBoundary_work {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOnWithGadgetBoundary κ mode D tape).2=(runOnWithBoundaryControl κ mode D tape).2 := by
  let raw := (PhysicalBinaryEdgeWire.decodeWithControl D).1.1
  have parts := runWithRunner_boundaries_same κ raw (round raw mode) (roundWithGadgetWork raw mode) tape
    (fun T row bits => by
      change (roundWithGadgetControl raw mode T row bits).1.1=(round raw mode T row bits).1
      rw [roundWithGadgetControl_reference])
  unfold runOnWithGadgetBoundary runOnWithBoundaryControl runOnWithRoundRunner
  dsimp only
  change (⟨(PhysicalBinaryEdgeWire.decodeWithControl D).2,
    (runWithRunner κ raw (roundWithGadgetWork raw mode) tape).2.1,
    (runWithRunner κ raw (roundWithGadgetWork raw mode) tape).2.2⟩ : BoundaryWork) =
    ⟨(PhysicalBinaryEdgeWire.decodeWithControl D).2,(runWithRunner κ raw (round raw mode) tape).2.1,
      (runWithRunner κ raw (round raw mode) tape).2.2⟩
  rw [parts]

/-- The same literal execution carries the modeled framer records, the
edge boundary work, and the paid gadget and projection work of reached rounds. -/
def edgeWithJoinedWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  let parsed := PhysicalSourceInputJoin.edgeWithFramingRecords source
  let result : Read (Σ n,EdgeResult n) × BoundaryWork := match parsed.1.1 with
    | none => ((none,parsed.1.2),⟨0,0,0⟩)
    | some ⟨n,D⟩ =>
        let executed := runOnWithGadgetBoundary κ mode D tape
        ((executed.1.1.map (fun out => ⟨n,out⟩),parsed.1.2+executed.1.2),executed.2)
  (result.1,(result.2,parsed.2))

theorem edgeWithJoinedWork_paid_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithJoinedWork κ mode source tape).1=edgeWithGadgetWork κ mode source tape := by
  unfold edgeWithJoinedWork edgeWithGadgetWork edgeWithRunner
  dsimp only
  rw [PhysicalSourceInputJoin.edge_framing_records_value]
  change _ = Read.bind (PhysicalSourceInputJoin.edge source) _
  unfold Read.bind
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    simp only [runOn_gadgetBoundary_paid_value]

theorem edgeWithJoinedWork_boundary (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithJoinedWork κ mode source tape).2.1=(edgeWithBoundaryControl κ mode source tape).2 := by
  unfold edgeWithJoinedWork edgeWithBoundaryControl
  dsimp only
  rw [PhysicalSourceInputJoin.edge_framing_records_value]
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    exact runOn_gadgetBoundary_work κ mode D tape

theorem edgeWithJoinedWork_frames (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithJoinedWork κ mode source tape).2.2=(PhysicalSourceInputJoin.edgeWithFramingRecords source).2 := rfl

theorem edgeWithJoinedWork_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithJoinedWork κ mode source tape).1.1=(edgeWithCost κ mode source tape).1 := by
  rw [edgeWithJoinedWork_paid_value,edgeWithGadgetWork_value]

end DirectedFlowCutGap.PaidDirectEdgeWire
