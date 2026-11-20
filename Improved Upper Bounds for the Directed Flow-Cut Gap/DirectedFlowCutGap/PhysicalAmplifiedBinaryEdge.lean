import DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex
import DirectedFlowCutGap.BinaryEdgeProjection

/-! The original edge solver with binary line prices, dyadic gadgets, and
binary scalar vertex preparation on each actual fractional row. -/

namespace DirectedFlowCutGap.PhysicalAmplifiedBinaryEdge

open BinaryArithmetic BinaryRational RawNonnegativeRational FiniteDrawTrees Polynomial
open EncodedVertexAmplification EncodedEdgeLineInput
open PhysicalEdgeSolver (binaryLineInput decode_binaryLineInput)
open PhysicalAmplifiedEdgeSolver (EdgeResult model)
open PhysicalIntegerRounding (Result)
open RetainedGridState (Flags)
open LiteralTapeComposition (execute execute_map)
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)

def lineWithCost {n : ℕ} (D : Input n) : BinaryFractionalGuesses.Input (lineSize n) × ℕ :=
  let line := BinaryLineLabels.prepare D
  let c := batch fun i => BinaryRawRational.encode line.1.costs[i.val]
  (⟨line.1.adjacency,line.1.demands,c.1⟩,c.2+line.2+4)

@[simp] theorem line_value {n : ℕ} (D : Input n) : (lineWithCost D).1=binaryLineInput D := by
  have costs : (batch (fun i : Fin (lineSize n) => BinaryRawRational.encode (lineInput D).costs[i.val])).1 =
      (binaryLineInput D).costs := by
    apply Vector.ext
    intro i hi
    simp only [batch_value,Vector.getElem_ofFn,binaryLineInput,Vector.getElem_map,BinaryRawRational.encode_eq]
    rfl
  simp only [lineWithCost,BinaryLineLabels.prepare_value,costs]
  rfl

def lineBudget {R : Type*} [Semiring R] (m demands b : R) : R :=
  m*(40*(b+2)^2)+8*m+4+(BinaryLineLabels.budget m m+BinaryLineLabels.demandBudget m demands+
    BinaryLineLabels.assemblyBudget m)+4

theorem line_paid {n b : ℕ} (D : Input n) (positive : 1 ≤ b)
    (fits : ∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ b ∧ D.costs[u.val][v.val].den.size ≤ b) :
    (lineWithCost D).2 ≤ lineBudget (lineSize n) D.demands.length b := by
  let line := BinaryLineLabels.prepare D
  have paid : (batch fun i : Fin (lineSize n) => BinaryRawRational.encode line.1.costs[i.val]).2 ≤
      lineSize n*(40*(b+2)^2)+8*lineSize n+4 := by
    apply batch_paid
    intro i
    obtain ⟨a,c⟩ := lineInput_cost_width D positive fits i
    have fields : (lineInput D).costs[i.val].Bounded b :=
      ⟨(Nat.size_le.mp a).le,(Nat.size_le.mp c).le⟩
    rw [show line.1=lineInput D from BinaryLineLabels.prepare_value D]
    exact BinaryRawRational.encode_paid fields
  have layout : line.2 ≤ BinaryLineLabels.budget (lineSize n) (lineSize n)+
      BinaryLineLabels.demandBudget (lineSize n) D.demands.length+
      BinaryLineLabels.assemblyBudget (lineSize n) := BinaryLineLabels.prepare_paid D
  change (batch fun i : Fin (lineSize n) => BinaryRawRational.encode line.1.costs[i.val]).2+line.2+4 ≤
    lineBudget (lineSize n) D.demands.length b
  unfold lineBudget
  omega

def roundOn {n : ℕ} (D : EncodedEdgeGadget.Input n) (prepared : ℕ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (Result (lineSize n)) :=
  let g := BinaryEdgeGadget.build D
  (PhysicalAmplifiedBinaryVertex.runner mode T g.1.data tape).map
    (PhysicalVertexRounding.project (BinaryEdgeProjection.pullback g.1) (g.2+prepared))

def round {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PhysicalVertexSampling.Runner (lineSize n) :=
  fun T r tape =>
    let input := BinaryEdgeProjection.roundingInput D r.weights
    roundOn input.1 input.2 mode T tape

theorem round_observe {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) :
    (round D mode T r tape).map PhysicalIntegerRounding.Result.observe =
      execute T (EncodedEdgeSolver.round D (model mode) r) tape := by
  let p := BinaryEdgeGadget.build (roundingInput D r.weights)
  let g := p.1
  rw [round,BinaryEdgeProjection.roundingInput_value]
  change ((PhysicalAmplifiedBinaryVertex.runner mode T g.data tape).map
    (PhysicalVertexRounding.project (BinaryEdgeProjection.pullback g)
      (p.2+(BinaryEdgeProjection.roundingInput D r.weights).2))).map
      PhysicalIntegerRounding.Result.observe = _
  rw [PhysicalVertexRounding.project_observe _ _ (BinaryEdgeProjection.pullback_value g),
    PhysicalAmplifiedBinaryVertex.runner_observe,
    ← execute_map T (fun cut => toLine (EncodedEdgeRounding.pullback g cut))
      (ChargedVertexModes.round g.size mode g.data) tape]
  unfold EncodedEdgeSolver.round EncodedEdgeRounding.tree
  have h : g=EncodedEdgeGadget.build (roundingInput D r.weights) := BinaryEdgeGadget.build_value _
  let solution (g' : EncodedEdgeGadget.Prepared (roundingInput D r.weights)) :=
    execute T (map (fun cut => toLine (EncodedEdgeRounding.pullback g' cut))
      (ChargedVertexModes.round g'.size mode g'.data)) tape
  change solution g = _
  rw [h]
  cases mode <;> simp only [solution,model,ChargedVertexModes.round,EncodedEdgeSolver.massMode,
    EncodedEdgeSolver.sizeMode,execute_map,Option.map_map,Function.comp_def]

def finish {n : ℕ} (D : Input n) (setup : ℕ) (r : PhysicalAmplifiedVertexSolver.Result (lineSize n)) : EdgeResult n :=
  let output := BinaryEdgeProjection.output D r.output
  ⟨output.1,r.suffix,r.dispatch,r.readback,r.roundingAndSelection+setup+output.2⟩

def run {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Option (EdgeResult n) :=
  let controls := BinarySolverOuterControls.edge n κ
  let packed := lineWithCost D
  (PhysicalAmplifiedVertexSolver.run packed.1 (round D mode) controls.draws controls.extra controls.confidence tape).map
    (finish D (packed.2+controls.paid))

theorem run_controls {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    run κ D mode tape =
      (PhysicalAmplifiedVertexSolver.run (lineWithCost D).1 (round D mode) (EncodedEdgeSolver.drawBound n)
        (confidenceExponent n κ) (confidenceExponent n κ+1) tape).map
          (finish D ((lineWithCost D).2+(BinarySolverOuterControls.edge n κ).paid)) := by
  simp only [run,BinarySolverOuterControls.edge_draws,BinarySolverOuterControls.edge_extra,
    BinarySolverOuterControls.edge_confidence]

theorem run_observe {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (run κ D mode tape).map EdgeResult.observe =
      (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ D (model mode)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  let e := confidenceExponent n κ
  let ref := EncodedEdgeSolver.round D (model mode)
  let actual := PhysicalAmplifiedVertexSolver.run (lineWithCost D).1 (round D mode)
    (EncodedEdgeSolver.drawBound n) e (e+1) tape
  let abstract := boundedBitTree (EncodedEdgeSolver.drawBound n) e (e+1) (lineInput D) ref
  have law := PhysicalAmplifiedVertexSolver.run_observe (lineWithCost D).1 (round D mode) ref
    (EncodedEdgeSolver.drawBound n) e (e+1) tape (round_observe D mode)
  have decode : BinaryFractionalGuesses.decodeInput (lineWithCost D).1=lineInput D := by
    rw [line_value,decode_binaryLineInput]
  change actual.map PhysicalAmplifiedVertexSolver.Result.observe =
    (EncodedSolverBits.run (boundedBitTree (EncodedEdgeSolver.drawBound n) e (e+1)
      (BinaryFractionalGuesses.decodeInput (lineWithCost D).1) ref) tape).map (fun (out,(rest,_)) => (out,rest)) at law
  rw [decode] at law
  have eq : EncodedEdgeSolver.bitTree κ D (model mode)=map (EncodedEdgeSolver.outputFor D) abstract := rfl
  rw [eq,EncodedSolverBits.run_map]
  have readout : (run κ D mode tape).map EdgeResult.observe =
      (actual.map PhysicalAmplifiedVertexSolver.Result.observe).map
        (fun (out,rest) => (EncodedEdgeSolver.outputFor D out,rest)) := by
    simp only [run_controls,actual,e,Option.map_map,Function.comp_def,finish,EdgeResult.observe,
      PhysicalAmplifiedVertexSolver.Result.observe,BinaryEdgeProjection.output_value]
  rw [readout,law]
  simp only [Option.map_map,Function.comp_def,abstract]

theorem run_fairTape {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) :
    (EncodedSolverBits.fairTape (EncodedSolverBits.edgeBudget κ D)).map
      (fun tape => (run κ D mode tape).map EdgeResult.output) =
      (ideal (EncodedEdgeSolver.bitTree κ D (model mode))).map some := by
  have same : (fun tape => (run κ D mode tape).map EdgeResult.output) =
      (fun tape => (PhysicalAmplifiedEdgeSolver.run κ D mode tape).map EdgeResult.output) := by
    funext tape
    have eq := (run_observe κ D mode tape).trans (PhysicalAmplifiedEdgeSolver.run_observe κ D mode tape).symm
    simpa only [Option.map_map,Function.comp_def,EdgeResult.observe] using congrArg (Option.map Prod.fst) eq
  rw [same]
  exact PhysicalOriginalInputSolvers.edge_fairTape κ D mode

end DirectedFlowCutGap.PhysicalAmplifiedBinaryEdge
