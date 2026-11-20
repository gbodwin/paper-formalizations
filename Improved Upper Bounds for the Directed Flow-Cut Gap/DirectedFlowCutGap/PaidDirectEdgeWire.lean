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

private def edgeWithFramedRun
    (runner : {n : ℕ} → ℕ → ChargedVertexModes.Mode → EncodedEdgeInput.Input n → Bits →
      Read (EdgeResult n) × BoundaryWork)
    (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  let parsed := PhysicalSourceInputJoin.edgeWithFramingRecords source
  let result : Read (Σ n,EdgeResult n) × BoundaryWork := match parsed.1.1 with
    | none => ((none,parsed.1.2),⟨0,0,0⟩)
    | some ⟨n,D⟩ =>
        let executed := runner κ mode D tape
        ((executed.1.1.map (fun out => ⟨n,out⟩),parsed.1.2+executed.1.2),executed.2)
  (result.1,(result.2,parsed.2))

/-- The same literal execution carries the modeled framer records, the
edge boundary work, and the paid gadget and projection work of reached rounds. -/
def edgeWithJoinedWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  edgeWithFramedRun runOnWithGadgetBoundary κ mode source tape

theorem edgeWithJoinedWork_paid_value (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithJoinedWork κ mode source tape).1=edgeWithGadgetWork κ mode source tape := by
  unfold edgeWithJoinedWork edgeWithFramedRun edgeWithGadgetWork edgeWithRunner
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
  unfold edgeWithJoinedWork edgeWithFramedRun edgeWithBoundaryControl
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

private theorem finish_headers {n : ℕ} (D : Input n) (setup oldSunk newSunk extra : ℕ)
    {a b : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))}
    (same : b.1.map PhysicalAmplifiedVertexSolver.Result.observe=a.1.map PhysicalAmplifiedVertexSolver.Result.observe)
    (fee : b.2=a.2) (sunk : newSunk≤oldSunk+extra) :
    (finish D setup newSunk b).1.map EdgeResult.observe=(finish D setup oldSunk a).1.map EdgeResult.observe ∧
      (finish D setup newSunk b).2 ≤ (finish D setup oldSunk a).2+extra ∧
      (finishWithControl D setup newSunk b).2=(finishWithControl D setup oldSunk a).2 := by
  unfold finish finishWithControl
  cases first : a.1 <;> cases second : b.1 <;>
    simp only [first,second,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at same ⊢
  · exact ⟨True.intro,by omega,True.intro⟩
  · rename_i earlier later
    obtain ⟨output,tape⟩ := Prod.mk.inj same
    simp only [EdgeResult.observe,output,tape]
    exact ⟨True.intro,by omega,True.intro⟩

private theorem finish_phase {n setup oldSunk newSunk : ℕ} (D : Input n)
    {a b : Read (PhysicalAmplifiedVertexSolver.Result (lineSize n))}
    (same : b.1.map PhysicalAmplifiedVertexSolver.Result.observe=a.1.map PhysicalAmplifiedVertexSolver.Result.observe)
    (phase : b.1.map PhysicalAmplifiedVertexSolver.Result.roundingAndSelection=
      a.1.map PhysicalAmplifiedVertexSolver.Result.roundingAndSelection) :
    (finish D setup newSunk b).1.map EdgeResult.roundingAndSelection=
      (finish D setup oldSunk a).1.map EdgeResult.roundingAndSelection := by
  unfold finish finishWithControl
  cases first : a.1 <;> cases second : b.1 <;>
    simp only [first,second,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at same phase ⊢
  obtain ⟨output,_⟩ := Prod.mk.inj same
  simp only [output,phase]

/-- The physical fractional controller runs on the actual encoded line
input. Dispatch and readback fees describe that execution. -/
private def runWithPhysicalControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    Read (EdgeResult n) × ((ℕ × ℕ) × ℕ) :=
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let physical := PhysicalSourceReadback.runWithTerminalCharge line.1.1
  let setup := line.1.2+controls.paid
  let r := match physical.1 with
    | none => ((none,setup),0)
    | some (plan,dispatch,readback) =>
        let sample := PaidVertexAmplification.runWithPlan line.1.1 (roundWithGadgetWork D mode)
          controls.draws controls.extra controls.confidence plan dispatch readback tape
        finishWithControl D setup (setup+dispatch+readback) sample
  (r.1,((line.2,r.2),physical.2))

def runWithPhysicalGadgetWork {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    Read (EdgeResult n) × ℕ :=
  let r := runWithPhysicalControl κ D mode tape
  (r.1,r.2.2)

private theorem runWithPhysicalControl_comparison {n : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let binary := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    let size := (PhysicalSourceDispatch.input binary).length
    let raw := PhysicalSourceReadback.runWithTerminalCharge binary
    let new := runWithPhysicalControl κ D mode tape
    let old := runWithGadgetWork κ D mode tape
    new.1.1.map EdgeResult.observe=old.1.map EdgeResult.observe ∧
      new.1.2 ≤ old.2+PhysicalSourceDispatch.paidPolynomial.eval size+
        ((raw.1.map (fun p => p.2.2)).getD 0) ∧
      new.2.1=(runWithRunner κ D (roundWithGadgetWork D mode) tape).2 := by
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let cover := BinaryFractionalGuesses.solveInput line.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := line.2+controls.paid
  obtain ⟨dispatch,_,readback,_,known,dispatchPaid⟩ := PhysicalSourceReadback.terminal_headers line.1
  have observed := DirectBinaryEdgeWire.read_value cover.1
  change (PhysicalSourceReadback.runWithTerminalCharge line.1).1 =
    some (PhysicalCoverReader.plan cover.1,dispatch,readback) at known
  rw [← observed] at known
  let old := PaidVertexAmplification.runWithPlan line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 tape
  let fresh := PaidVertexAmplification.runWithPlan line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 dispatch readback tape
  have aligned := PaidVertexAmplification.runWithPlan_headers line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 dispatch readback tape
  change (fresh.1.map PhysicalAmplifiedVertexSolver.Result.observe,fresh.2)=
    (old.1.map PhysicalAmplifiedVertexSolver.Result.observe,old.2) at aligned
  have sunk : setup+dispatch+readback ≤ setup+cover.2+reader.2+(dispatch+readback) := by omega
  have fee : fresh.2=old.2 := congrArg (fun (p : Option (EncodedVertexSolver.Output (lineSize n) × Bits) × ℕ) => p.2) aligned
  have result := finish_headers D setup (setup+cover.2+reader.2) (setup+dispatch+readback)
    (dispatch+readback) (congrArg Prod.fst aligned) fee sunk
  have knownControl :
      (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 =
        some (reader.1,dispatch,readback) := known
  unfold runWithPhysicalControl
  dsimp only
  rw [knownControl,known]
  simp only [Option.map_some,Option.getD_some]
  refine ⟨result.1,result.2.1.trans ?_,?_⟩
  · exact (Nat.add_le_add_left (Nat.add_le_add_right dispatchPaid readback) _).trans_eq (Nat.add_assoc ..).symm
  · exact Prod.ext rfl result.2.2

theorem runWithPhysicalGadgetWork_comparison {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let binary := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    let size := (PhysicalSourceDispatch.input binary).length
    let raw := PhysicalSourceReadback.runWithTerminalCharge binary
    let new := runWithPhysicalGadgetWork κ D mode tape
    let old := runWithGadgetWork κ D mode tape
    new.1.1.map EdgeResult.observe=old.1.map EdgeResult.observe ∧
      new.1.2 ≤ old.2+PhysicalSourceDispatch.paidPolynomial.eval size+
        ((raw.1.map (fun p => p.2.2)).getD 0) :=
  let compared := runWithPhysicalControl_comparison κ D mode tape
  ⟨compared.1,compared.2.1⟩

theorem physical_line_cache_work {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (runWithPhysicalGadgetWork κ D mode tape).2 =
      (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithCost D).1).2 := rfl

private theorem runWithPhysicalControl_phase {n : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (runWithPhysicalControl κ D mode tape).1.1.map EdgeResult.roundingAndSelection=
      (run κ D mode tape).1.map EdgeResult.roundingAndSelection := by
  rw [← runWithGadgetWork_value]
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let cover := BinaryFractionalGuesses.solveInput line.1
  let reader := DirectBinaryEdgeWire.read cover.1
  let setup := line.2+controls.paid
  obtain ⟨dispatch,_,readback,_,known,_⟩ := PhysicalSourceReadback.terminal_headers line.1
  have observed := DirectBinaryEdgeWire.read_value cover.1
  change (PhysicalSourceReadback.runWithTerminalCharge line.1).1=
    some (PhysicalCoverReader.plan cover.1,dispatch,readback) at known
  rw [← observed] at known
  let old := PaidVertexAmplification.runWithPlan line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 tape
  let fresh := PaidVertexAmplification.runWithPlan line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 dispatch readback tape
  have aligned := PaidVertexAmplification.runWithPlan_headers line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 dispatch readback tape
  change (fresh.1.map PhysicalAmplifiedVertexSolver.Result.observe,fresh.2)=
    (old.1.map PhysicalAmplifiedVertexSolver.Result.observe,old.2) at aligned
  have phase := PaidVertexAmplification.runWithPlan_phase line.1 (roundWithGadgetWork D mode)
    controls.draws controls.extra controls.confidence reader.1 cover.2 reader.2 dispatch readback tape
  have knownControl :
      (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1=
        some (reader.1,dispatch,readback) := known
  simp only [runWithPhysicalControl,knownControl,runWithGadgetWork,runWithRunner]
  exact finish_phase D (oldSunk := setup+cover.2+reader.2) (newSunk := setup+dispatch+readback)
    (congrArg Prod.fst aligned) phase

def runWithPhysicalWork : Runner := fun κ D mode tape =>
  let result := runWithPhysicalGadgetWork κ D mode tape
  (result.1.1,result.1.2+result.2)

def edgeWithPhysicalWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Read (Σ n,EdgeResult n) :=
  edgeWithRunner runWithPhysicalWork κ mode source tape

def observeWireEdge (r : Σ n,EdgeResult n) : Σ n,EncodedEdgeSolver.Output n × Bits := ⟨r.1,r.2.observe⟩

theorem edgeWithPhysicalWork_observe (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithPhysicalWork κ mode source tape).1.map observeWireEdge=
      (edgeWithCost κ mode source tape).1.map observeWireEdge := by
  rw [← edgeWithGadgetWork_value κ mode source tape]
  simp only [edgeWithPhysicalWork,edgeWithGadgetWork,edgeWithRunner,Read.bind_value]
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    simp only [Option.bind_some,runOnWithRunner,Option.map_map,Function.comp_def]
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    have same := (runWithPhysicalGadgetWork_comparison κ raw mode tape).1
    have lifted := congrArg (Option.map (fun v : EncodedEdgeSolver.Output n × Bits =>
      (⟨n,v⟩ : Σ m,EncodedEdgeSolver.Output m × Bits))) same
    simp only [Option.map_map,Function.comp_def] at lifted
    exact lifted

private def runOnWithPhysicalBoundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  let r := runWithPhysicalControl κ prices.1.1 mode tape
  ((r.1.1.map (fun out => { out with roundingAndSelection := out.roundingAndSelection+prices.1.2 }),
    prices.1.2+(r.1.2+r.2.2)), ⟨prices.2,r.2.1.1,r.2.1.2⟩)

private theorem runOn_physical_boundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOnWithPhysicalBoundary κ mode D tape).2=(runOnWithGadgetBoundary κ mode D tape).2 := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  have h := (runWithPhysicalControl_comparison κ prices.1.1 mode tape).2.2
  exact congrArg (fun a : ℕ × ℕ => (⟨prices.2,a.1,a.2⟩ : BoundaryWork)) h

/-- Keep the original framer and edge boundary work with the measured
fractional terminal pass and all reached gadget rounds on one source run. -/
def edgeWithTerminalWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  edgeWithFramedRun runOnWithPhysicalBoundary κ mode source tape

theorem edgeWithTerminalWork_paid (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithTerminalWork κ mode source tape).1=edgeWithPhysicalWork κ mode source tape := by
  unfold edgeWithTerminalWork edgeWithFramedRun edgeWithPhysicalWork edgeWithRunner
  dsimp only
  rw [PhysicalSourceInputJoin.edge_framing_records_value]
  change _ = Read.bind (PhysicalSourceInputJoin.edge source) _
  unfold Read.bind
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some encoded => obtain ⟨n,D⟩ := encoded; rfl

theorem edgeWithTerminalWork_boundary (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithTerminalWork κ mode source tape).2=(edgeWithJoinedWork κ mode source tape).2 := by
  unfold edgeWithTerminalWork edgeWithJoinedWork edgeWithFramedRun
  dsimp only
  cases (PhysicalSourceInputJoin.edgeWithFramingRecords source).1.1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    exact congrArg (fun a => (a,(PhysicalSourceInputJoin.edgeWithFramingRecords source).2))
      (runOn_physical_boundary κ mode D tape)

theorem edgeWithTerminalWork_observe (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithTerminalWork κ mode source tape).1.1.map observeWireEdge =
      (edgeWithCost κ mode source tape).1.map observeWireEdge := by
  rw [edgeWithTerminalWork_paid,edgeWithPhysicalWork_observe]

private abbrev MeasuredAmplifier (m : ℕ) :=
  BinaryFractionalGuesses.Input m → PaidVertexSampling.Runner m →
    ℕ → ℕ → ℕ → PhysicalCoverReader.Plan m → ℕ → ℕ → Bits → Read (PhysicalAmplifiedVertexSolver.Result m) × ℕ

private def runWithPhysicalAmplificationControl {n : ℕ} (amplify : MeasuredAmplifier (lineSize n)) (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode)
    (tape : Bits) : Read (EdgeResult n) × ((ℕ × ℕ) × ℕ) :=
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let physical := PhysicalSourceReadback.runWithTerminalCharge line.1.1
  let setup := line.1.2+controls.paid
  let r : Read (EdgeResult n) × (ℕ × ℕ) := match physical.1 with
    | none => ((none,setup),(0,0))
    | some (plan,dispatch,readback) =>
      let amplified := amplify line.1.1 (roundWithGadgetWork D mode)
        controls.draws controls.extra controls.confidence plan dispatch readback tape
      let out := finishWithControl D setup (setup+dispatch+readback) amplified.1
      (out.1,(out.2,amplified.2))
  (r.1,((line.2,r.2.1),physical.2+r.2.2))

private def runWithPhysicalScalarControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode)
    (tape : Bits) : Read (EdgeResult n) × ((ℕ × ℕ) × ℕ) :=
  runWithPhysicalAmplificationControl (@PaidVertexAmplification.runWithPlanScalarWork (lineSize n)) κ D mode tape

private def runWithPhysicalSelectionControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode)
    (tape : Bits) : Read (EdgeResult n) × ((ℕ × ℕ) × ℕ) :=
  runWithPhysicalAmplificationControl (@PaidVertexAmplification.runWithPlanSelectionWork (lineSize n)) κ D mode tape

private def runWithPhysicalStreamControl {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode)
    (tape : Bits) : Read (EdgeResult n) × ((ℕ × ℕ) × ℕ) :=
  runWithPhysicalAmplificationControl (@PaidVertexAmplification.runWithPlanStreamWork (lineSize n)) κ D mode tape

private theorem run_physical_scalar_reference {n : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let new := runWithPhysicalScalarControl κ D mode tape
    let old := runWithPhysicalControl κ D mode tape
    new.1=old.1 ∧ new.2.1=old.2.1 := by
  simp only [runWithPhysicalScalarControl,runWithPhysicalAmplificationControl,runWithPhysicalControl]
  cases (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 with
  | none => exact ⟨rfl,rfl⟩
  | some input =>
    obtain ⟨plan,dispatch,readback⟩ := input
    constructor <;> simp only [PaidVertexAmplification.runWithPlanScalarWork_reference]

private theorem run_physical_scalar_paid {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits)
    (wide : ((runWithPhysicalControl κ D mode tape).1.2+4).size≤B) :
    (runWithPhysicalScalarControl κ D mode tape).2.2≤(runWithPhysicalControl κ D mode tape).2.2+
      (((BinarySolverOuterControls.edge n κ).extra+2)*PaidVertexAmplification.sampleControlBudget B+1) := by
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let setup := line.1.2+controls.paid
  simp only [runWithPhysicalScalarControl,runWithPhysicalAmplificationControl,runWithPhysicalControl] at wide ⊢
  cases h : (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 with
  | none => simpa only [Nat.add_zero] using Nat.le_add_right _ _
  | some input =>
    obtain ⟨plan,dispatch,reader⟩ := input
    rw [h] at wide
    let old := PaidVertexAmplification.runWithPlan line.1.1 (roundWithGadgetWork D mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape
    let out := finishWithControl D setup (setup+dispatch+reader) old
    change (out.1.2+4).size≤B at wide
    have included : old.2≤out.1.2 := by
      unfold out finishWithControl
      cases old.1 with
      | none => exact Nat.le_add_left _ _
      | some r => exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    have cap : (old.2+4).size≤B := (Nat.size_le_size (Nat.add_le_add_right included 4)).trans wide
    exact Nat.add_le_add_left (PaidVertexAmplification.runWithPlanScalarWork_paid line.1.1
      (roundWithGadgetWork D mode) controls.draws controls.extra controls.confidence
      plan dispatch reader tape cap) _

private def runOnWithTerminalAmplificationBoundary {n : ℕ} (amplify : MeasuredAmplifier (lineSize n))
    (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  let r := runWithPhysicalAmplificationControl amplify κ prices.1.1 mode tape
  ((r.1.1.map (fun out => { out with roundingAndSelection := out.roundingAndSelection+prices.1.2 }),
    prices.1.2+(r.1.2+r.2.2)), ⟨prices.2,r.2.1.1,r.2.1.2⟩)

private def runOnWithTerminalScalarBoundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  runOnWithTerminalAmplificationBoundary (@PaidVertexAmplification.runWithPlanScalarWork (lineSize n)) κ mode D tape

private def runOnWithTerminalSelectionBoundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  runOnWithTerminalAmplificationBoundary (@PaidVertexAmplification.runWithPlanSelectionWork (lineSize n)) κ mode D tape

private def runOnWithTerminalStreamBoundary {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) : Read (EdgeResult n) × BoundaryWork :=
  runOnWithTerminalAmplificationBoundary (@PaidVertexAmplification.runWithPlanStreamWork (lineSize n)) κ mode D tape

private theorem runOn_terminal_scalar_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    let new := runOnWithTerminalScalarBoundary κ mode D tape
    let old := runOnWithPhysicalBoundary κ mode D tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  have same := run_physical_scalar_reference κ prices.1.1 mode tape
  simp only [runOnWithTerminalScalarBoundary,runOnWithTerminalAmplificationBoundary,runOnWithPhysicalBoundary]
  change ((runWithPhysicalScalarControl κ prices.1.1 mode tape).1.1.map _ =
    (runWithPhysicalControl κ prices.1.1 mode tape).1.1.map _) ∧ _
  constructor
  · rw [same.1]
  · exact congrArg (fun a : ℕ × ℕ => (⟨prices.2,a.1,a.2⟩ : BoundaryWork)) same.2

private theorem runOn_terminal_scalar_paid {n B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits)
    (wide : ((runOnWithPhysicalBoundary κ mode D tape).1.2+4).size≤B) :
    (runOnWithTerminalScalarBoundary κ mode D tape).1.2≤(runOnWithPhysicalBoundary κ mode D tape).1.2+
      (((BinarySolverOuterControls.edge n κ).extra+2)*PaidVertexAmplification.sampleControlBudget B+1) := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  let old := runWithPhysicalControl κ prices.1.1 mode tape
  let new := runWithPhysicalScalarControl κ prices.1.1 mode tape
  let reward := ((BinarySolverOuterControls.edge n κ).extra+2)*PaidVertexAmplification.sampleControlBudget B+1
  have h : (old.1.2+4).size≤B := (Nat.size_le_size (Nat.add_le_add_right
    ((Nat.le_add_right old.1.2 old.2.2).trans (Nat.le_add_left _ _)) 4)).trans wide
  have paid : new.2.2≤old.2.2+reward := run_physical_scalar_paid κ prices.1.1 mode tape h
  have identity : new.1=old.1 := (run_physical_scalar_reference κ prices.1.1 mode tape).1
  change prices.1.2+(new.1.2+new.2.2)≤prices.1.2+(old.1.2+old.2.2)+reward
  rw [identity]
  omega

def edgeWithTerminalScalarWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  edgeWithFramedRun runOnWithTerminalScalarBoundary κ mode source tape

theorem edge_terminal_scalar_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := edgeWithTerminalScalarWork κ mode source tape
    let old := edgeWithTerminalWork κ mode source tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  simp only [edgeWithTerminalScalarWork,edgeWithTerminalWork,edgeWithFramedRun]
  cases (PhysicalSourceInputJoin.edgeWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,rfl⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    have same := runOn_terminal_scalar_reference κ mode D tape
    refine ⟨?_,?_⟩
    · exact congrArg (Option.map (fun out => (⟨n,out⟩ : Σ i,EdgeResult i))) same.1
    · exact congrArg (fun a => (a,(PhysicalSourceInputJoin.edgeWithFramingRecords source).2)) same.2

theorem edge_terminal_scalar_paid {B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    (wide : ((edgeWithTerminalWork κ mode source tape).1.2+4).size≤B) :
    let n := ((PhysicalSourceInputJoin.edge source).1.map Sigma.fst).getD 0
    (edgeWithTerminalScalarWork κ mode source tape).1.2≤(edgeWithTerminalWork κ mode source tape).1.2+
      (((BinarySolverOuterControls.edge n κ).extra+2)*
        PaidVertexAmplification.sampleControlBudget B+1) := by
  unfold edgeWithTerminalWork edgeWithFramedRun at wide
  unfold edgeWithTerminalScalarWork edgeWithTerminalWork edgeWithFramedRun
  dsimp only at wide ⊢
  rw [PhysicalSourceInputJoin.edge_framing_records_value] at wide ⊢
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact Nat.le_add_right _ _
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    rw [parsed] at wide
    let old := runOnWithPhysicalBoundary κ mode D tape
    let new := runOnWithTerminalScalarBoundary κ mode D tape
    let parse := (PhysicalSourceInputJoin.edge source).2
    let extra := (((BinarySolverOuterControls.edge n κ).extra+2)*PaidVertexAmplification.sampleControlBudget B+1)
    change (parse+old.1.2+4).size≤B at wide
    have inner : (old.1.2+4).size≤B :=
      (Nat.size_le_size (Nat.add_le_add_right (Nat.le_add_left _ _) 4)).trans wide
    have step : new.1.2≤old.1.2+extra := runOn_terminal_scalar_paid κ mode D tape inner
    change parse+new.1.2≤parse+old.1.2+extra
    simpa only [Nat.add_assoc] using Nat.add_le_add_left step parse

private theorem run_physical_selection_reference {n : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let new := runWithPhysicalSelectionControl κ D mode tape
    let old := runWithPhysicalScalarControl κ D mode tape
    new.1=old.1 ∧ new.2.1=old.2.1 := by
  simp only [runWithPhysicalSelectionControl,runWithPhysicalScalarControl,runWithPhysicalAmplificationControl]
  cases (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 with
  | none => exact ⟨rfl,rfl⟩
  | some input =>
    obtain ⟨plan,dispatch,readback⟩ := input
    constructor <;> simp only [PaidVertexAmplification.runWithPlanSelectionWork_reference]

private theorem run_physical_stream_reference {n : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits) :
    let new := runWithPhysicalStreamControl κ D mode tape
    let old := runWithPhysicalSelectionControl κ D mode tape
    new.1=old.1 ∧ new.2.1=old.2.1 := by
  simp only [runWithPhysicalStreamControl,runWithPhysicalSelectionControl,runWithPhysicalAmplificationControl]
  cases (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 with
  | none => exact ⟨rfl,rfl⟩
  | some input =>
    obtain ⟨plan,dispatch,readback⟩ := input
    constructor <;> simp only [PaidVertexAmplification.runWithPlanStreamWork_reference]

private theorem run_physical_stream_paid {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits)
    (wide : ∀ out ∈ (runWithPhysicalSelectionControl κ D mode tape).1.1, out.roundingAndSelection.size≤B) :
    (runWithPhysicalStreamControl κ D mode tape).2.2≤(runWithPhysicalSelectionControl κ D mode tape).2.2+
      ((BinarySolverOuterControls.edge n κ).extra+1)*PaidVertexAmplification.retainedFeeBudget B := by
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let setup := line.1.2+controls.paid
  simp only [runWithPhysicalStreamControl,runWithPhysicalSelectionControl,runWithPhysicalAmplificationControl] at wide ⊢
  cases h : (PhysicalSourceReadback.runWithTerminalCharge line.1.1).1 with
  | none => exact Nat.le_add_right _ _
  | some input =>
    obtain ⟨plan,dispatch,reader⟩ := input
    rw [h] at wide
    let old := PaidVertexAmplification.runWithPlanSelectionWork line.1.1 (roundWithGadgetWork D mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape
    have fits : ∀ out ∈ old.1.1, out.roundingAndSelection.size≤B := by
      intro out present
      let answer := PhysicalAmplifiedBinaryEdge.finish D setup out
      have seen : answer ∈ (finish D setup (setup+dispatch+reader) old.1).1 := by
        rw [finish_value,Option.mem_def.mp present]
        exact Option.mem_some_iff.mpr rfl
      have bound := wide answer seen
      have included : out.roundingAndSelection≤answer.roundingAndSelection :=
        (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      exact (Nat.size_le_size included).trans bound
    have bound := PaidVertexAmplification.runWithPlanStreamWork_paid line.1.1 (roundWithGadgetWork D mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape fits
    simpa only [Nat.add_assoc] using Nat.add_le_add_left bound (PhysicalSourceReadback.runWithTerminalCharge line.1.1).2

private theorem run_physical_selection_paid {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits)
    (wide : (runWithPhysicalScalarControl κ D mode tape).1.2.size ≤ B) :
    (runWithPhysicalSelectionControl κ D mode tape).2.2 ≤ (runWithPhysicalScalarControl κ D mode tape).2.2+
      BinaryCutPriceSelection.minimumControlBudget (BinarySolverOuterControls.edge n κ).extra
        (BinaryCutPriceSelection.fieldControlBudget (lineSize n)) B := by
  let controls := BinarySolverOuterControls.edge n κ
  let line := PhysicalAmplifiedBinaryEdge.lineWithControl D
  let setup := line.1.2+controls.paid
  rw [(run_physical_scalar_reference κ D mode tape).1] at wide
  simp only [runWithPhysicalSelectionControl,runWithPhysicalScalarControl,runWithPhysicalAmplificationControl]
  cases h : (PhysicalSourceReadback.runWithTerminalCharge (PhysicalAmplifiedBinaryEdge.lineWithControl D).1.1).1 with
  | none => simpa only [Nat.add_zero] using Nat.le_add_right _ _
  | some input =>
    obtain ⟨plan,dispatch,reader⟩ := input
    simp only [runWithPhysicalControl,h] at wide
    let prior := PaidVertexAmplification.runWithPlan line.1.1 (roundWithGadgetWork D mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape
    let out := finishWithControl D setup (setup+dispatch+reader) prior
    change out.1.2.size≤B at wide
    have included : prior.2≤out.1.2 := by
      unfold out finishWithControl
      cases prior.1 with
      | none => exact Nat.le_add_left _ _
      | some r => exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    have cap : prior.2.size≤B := (Nat.size_le_size included).trans wide
    have addition := PaidVertexAmplification.runWithPlanSelectionWork_paid line.1.1 (roundWithGadgetWork D mode)
      controls.draws controls.extra controls.confidence plan dispatch reader tape cap
    simpa only [Nat.add_assoc] using Nat.add_le_add_left addition
      (PhysicalSourceReadback.runWithTerminalCharge line.1.1).2

private theorem runOn_terminal_selection_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    let new := runOnWithTerminalSelectionBoundary κ mode D tape
    let old := runOnWithTerminalScalarBoundary κ mode D tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  have same := run_physical_selection_reference κ prices.1.1 mode tape
  simp only [runOnWithTerminalSelectionBoundary,runOnWithTerminalScalarBoundary,runOnWithTerminalAmplificationBoundary]
  change ((runWithPhysicalSelectionControl κ prices.1.1 mode tape).1.1.map _ =
    (runWithPhysicalScalarControl κ prices.1.1 mode tape).1.1.map _) ∧ _
  constructor
  · rw [same.1]
  · exact congrArg (fun a : ℕ × ℕ => (⟨prices.2,a.1,a.2⟩ : BoundaryWork)) same.2

private theorem runOn_terminal_selection_phase {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOnWithTerminalSelectionBoundary κ mode D tape).1.1.map EdgeResult.roundingAndSelection=
      (runOn κ mode D tape).1.map EdgeResult.roundingAndSelection := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  have first := (run_physical_selection_reference κ prices.1.1 mode tape).1
  have second := (run_physical_scalar_reference κ prices.1.1 mode tape).1
  have paid := runWithPhysicalControl_phase κ prices.1.1 mode tape
  simp only [runOnWithTerminalSelectionBoundary,runOnWithTerminalAmplificationBoundary,runOn_reference,
    PhysicalBinaryEdgeWire.decodeWithCost]
  change ((runWithPhysicalSelectionControl κ prices.1.1 mode tape).1.1.map _).map _ = _
  rw [first,second]
  simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map fun x => x+prices.1.2) paid

private theorem runOn_terminal_stream_reference {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) :
    let new := runOnWithTerminalStreamBoundary κ mode D tape
    let old := runOnWithTerminalSelectionBoundary κ mode D tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  have same := run_physical_stream_reference κ prices.1.1 mode tape
  simp only [runOnWithTerminalStreamBoundary,runOnWithTerminalSelectionBoundary,runOnWithTerminalAmplificationBoundary]
  change ((runWithPhysicalStreamControl κ prices.1.1 mode tape).1.1.map _ =
    (runWithPhysicalSelectionControl κ prices.1.1 mode tape).1.1.map _) ∧ _
  constructor
  · rw [same.1]
  · exact congrArg (fun a : ℕ × ℕ => (⟨prices.2,a.1,a.2⟩ : BoundaryWork)) same.2

private theorem runOn_terminal_stream_paid {n B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits)
    (width : ∀ out ∈ (runOnWithTerminalSelectionBoundary κ mode D tape).1.1,
      out.roundingAndSelection.size≤B) :
    (runOnWithTerminalStreamBoundary κ mode D tape).1.2≤(runOnWithTerminalSelectionBoundary κ mode D tape).1.2+
      ((BinarySolverOuterControls.edge n κ).extra+1)*PaidVertexAmplification.retainedFeeBudget B := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  let old := runWithPhysicalSelectionControl κ prices.1.1 mode tape
  let new := runWithPhysicalStreamControl κ prices.1.1 mode tape
  let extra := ((BinarySolverOuterControls.edge n κ).extra+1)*PaidVertexAmplification.retainedFeeBudget B
  have raw : ∀ out ∈ old.1.1, out.roundingAndSelection.size≤B := by
    intro out present
    let result := {out with roundingAndSelection := out.roundingAndSelection+prices.1.2}
    have found : result ∈ (runOnWithTerminalSelectionBoundary κ mode D tape).1.1 := by
      change result ∈ old.1.1.map _
      rw [Option.mem_def.mp present]
      exact Option.mem_some_iff.mpr rfl
    exact (Nat.size_le_size (Nat.le_add_right _ _)).trans (width result found)
  have paid : new.2.2≤old.2.2+extra := run_physical_stream_paid κ prices.1.1 mode tape raw
  have identity : new.1=old.1 := (run_physical_stream_reference κ prices.1.1 mode tape).1
  change prices.1.2+(new.1.2+new.2.2)≤prices.1.2+(old.1.2+old.2.2)+extra
  rw [identity]
  omega

private theorem runOn_terminal_selection_paid {n B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits)
    (wide : (runOnWithTerminalScalarBoundary κ mode D tape).1.2.size≤B) :
    (runOnWithTerminalSelectionBoundary κ mode D tape).1.2≤(runOnWithTerminalScalarBoundary κ mode D tape).1.2+
      BinaryCutPriceSelection.minimumControlBudget (BinarySolverOuterControls.edge n κ).extra
        (BinaryCutPriceSelection.fieldControlBudget (lineSize n)) B := by
  let prices := PhysicalBinaryEdgeWire.decodeWithControl D
  let old := runWithPhysicalScalarControl κ prices.1.1 mode tape
  let new := runWithPhysicalSelectionControl κ prices.1.1 mode tape
  let extra := BinaryCutPriceSelection.minimumControlBudget (BinarySolverOuterControls.edge n κ).extra
    (BinaryCutPriceSelection.fieldControlBudget (lineSize n)) B
  have h : old.1.2.size≤B := (Nat.size_le_size
    ((Nat.le_add_right old.1.2 old.2.2).trans (Nat.le_add_left _ _))).trans wide
  have paid : new.2.2≤old.2.2+extra := run_physical_selection_paid κ prices.1.1 mode tape h
  have identity : new.1=old.1 := (run_physical_selection_reference κ prices.1.1 mode tape).1
  change prices.1.2+(new.1.2+new.2.2)≤prices.1.2+(old.1.2+old.2.2)+extra
  rw [identity]
  omega

def edgeWithTerminalSelectionWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  edgeWithFramedRun runOnWithTerminalSelectionBoundary κ mode source tape

theorem edge_terminal_selection_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := edgeWithTerminalSelectionWork κ mode source tape
    let old := edgeWithTerminalScalarWork κ mode source tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  simp only [edgeWithTerminalSelectionWork,edgeWithTerminalScalarWork,edgeWithFramedRun]
  cases (PhysicalSourceInputJoin.edgeWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,rfl⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    have same := runOn_terminal_selection_reference κ mode D tape
    exact ⟨congrArg (Option.map (fun out => (⟨n,out⟩ : Σ i,EdgeResult i))) same.1,
      congrArg (fun a => (a,(PhysicalSourceInputJoin.edgeWithFramingRecords source).2)) same.2⟩

theorem edge_terminal_selection_phase (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    (edgeWithTerminalSelectionWork κ mode source tape).1.1.map (fun out => out.2.roundingAndSelection)=
      (edgeWithCost κ mode source tape).1.map (fun out => out.2.roundingAndSelection) := by
  simp only [edgeWithTerminalSelectionWork,edgeWithFramedRun,edgeWithCost,Read.bind_value,
    PhysicalSourceInputJoin.edge_framing_records_value]
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    simp only [Option.bind_some,Option.map_map,Function.comp_def]
    exact runOn_terminal_selection_phase κ mode D tape

theorem edge_terminal_selection_paid {B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    (wide : (edgeWithTerminalScalarWork κ mode source tape).1.2.size≤B) :
    let n := ((PhysicalSourceInputJoin.edge source).1.map Sigma.fst).getD 0
    (edgeWithTerminalSelectionWork κ mode source tape).1.2≤(edgeWithTerminalScalarWork κ mode source tape).1.2+
      BinaryCutPriceSelection.minimumControlBudget (BinarySolverOuterControls.edge n κ).extra
        (BinaryCutPriceSelection.fieldControlBudget (lineSize n)) B := by
  unfold edgeWithTerminalScalarWork edgeWithFramedRun at wide
  unfold edgeWithTerminalSelectionWork edgeWithTerminalScalarWork edgeWithFramedRun
  dsimp only at wide ⊢
  rw [PhysicalSourceInputJoin.edge_framing_records_value] at wide ⊢
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact Nat.le_add_right _ _
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    rw [parsed] at wide
    let old := runOnWithTerminalScalarBoundary κ mode D tape
    let new := runOnWithTerminalSelectionBoundary κ mode D tape
    let parse := (PhysicalSourceInputJoin.edge source).2
    let extra := BinaryCutPriceSelection.minimumControlBudget (BinarySolverOuterControls.edge n κ).extra
      (BinaryCutPriceSelection.fieldControlBudget (lineSize n)) B
    change (parse+old.1.2).size≤B at wide
    have inner : old.1.2.size≤B := (Nat.size_le_size (Nat.le_add_left _ _)).trans wide
    have step : new.1.2≤old.1.2+extra := runOn_terminal_selection_paid κ mode D tape inner
    change parse+new.1.2≤parse+old.1.2+extra
    simpa only [Nat.add_assoc] using Nat.add_le_add_left step parse

def edgeWithTerminalStreamWork (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    Read (Σ n,EdgeResult n) × (BoundaryWork × ℕ) :=
  edgeWithFramedRun runOnWithTerminalStreamBoundary κ mode source tape

theorem edge_terminal_stream_reference (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let new := edgeWithTerminalStreamWork κ mode source tape
    let old := edgeWithTerminalSelectionWork κ mode source tape
    new.1.1=old.1.1 ∧ new.2=old.2 := by
  simp only [edgeWithTerminalStreamWork,edgeWithTerminalSelectionWork,edgeWithFramedRun]
  cases (PhysicalSourceInputJoin.edgeWithFramingRecords source).1.1 with
  | none => exact ⟨rfl,rfl⟩
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    have same := runOn_terminal_stream_reference κ mode D tape
    exact ⟨congrArg (Option.map (fun out => (⟨n,out⟩ : Σ i,EdgeResult i))) same.1,
      congrArg (fun a => (a,(PhysicalSourceInputJoin.edgeWithFramingRecords source).2)) same.2⟩

theorem edge_terminal_stream_paid {B : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    (width : ∀ out ∈ (edgeWithTerminalSelectionWork κ mode source tape).1.1, out.2.roundingAndSelection.size≤B) :
    let n := ((PhysicalSourceInputJoin.edge source).1.map Sigma.fst).getD 0
    (edgeWithTerminalStreamWork κ mode source tape).1.2≤(edgeWithTerminalSelectionWork κ mode source tape).1.2+
      ((BinarySolverOuterControls.edge n κ).extra+1)*PaidVertexAmplification.retainedFeeBudget B := by
  unfold edgeWithTerminalStreamWork edgeWithTerminalSelectionWork edgeWithFramedRun
  dsimp only
  rw [PhysicalSourceInputJoin.edge_framing_records_value]
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact Nat.le_add_right _ _
  | some encoded =>
    obtain ⟨n,D⟩ := encoded
    let old := runOnWithTerminalSelectionBoundary κ mode D tape
    let new := runOnWithTerminalStreamBoundary κ mode D tape
    let parse := (PhysicalSourceInputJoin.edge source).2
    let extra := ((BinarySolverOuterControls.edge n κ).extra+1)*PaidVertexAmplification.retainedFeeBudget B
    have inner : ∀ out ∈ old.1.1, out.roundingAndSelection.size≤B := by
      intro out present
      have existsOnWire : (⟨n,out⟩ : Σ i,EdgeResult i) ∈ (edgeWithTerminalSelectionWork κ mode source tape).1.1 := by
        simp only [edgeWithTerminalSelectionWork,edgeWithFramedRun,PhysicalSourceInputJoin.edge_framing_records_value,parsed]
        change (⟨n,out⟩ : Σ i,EdgeResult i) ∈ old.1.1.map _
        rw [Option.mem_def.mp present]
        exact Option.mem_some_iff.mpr rfl
      exact width ⟨n,out⟩ existsOnWire
    have step : new.1.2≤old.1.2+extra := runOn_terminal_stream_paid κ mode D tape inner
    change parse+new.1.2≤parse+old.1.2+extra
    simpa only [Nat.add_assoc] using Nat.add_le_add_left step parse

end DirectedFlowCutGap.PaidDirectEdgeWire
