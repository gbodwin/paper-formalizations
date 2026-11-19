import DirectedFlowCutGap.PhysicalAmplifiedVertexSolver
import DirectedFlowCutGap.PhysicalEdgeSolver

/-! Execute line-graph fractional covers and round their actual dyadic gadgets. -/

namespace DirectedFlowCutGap.PhysicalAmplifiedEdgeSolver

open BinaryArithmetic FiniteDrawTrees EncodedVertexAmplification
open EncodedEdgeLineInput (Input lineSize lineInput toLine)
open PhysicalEdgeSolver (binaryLineInput decode_binaryLineInput)
open PhysicalIntegerRounding (Result)
open LiteralTapeComposition (execute execute_map)

def model (mode : ChargedVertexModes.Mode) : EncodedEdgeSolver.Mode :=
  match mode with
  | .mass => EncodedEdgeSolver.massMode
  | .size => EncodedEdgeSolver.sizeMode

def rounding {n : ℕ} (mode : ChargedVertexModes.Mode) : PhysicalVertexSampling.Runner n :=
  match mode with
  | .mass => PhysicalVertexRounding.weighted
  | .size => PhysicalVertexRounding.size

private theorem rounding_observe {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ)
    (D : EncodedUnitCostReplication.Input n) (tape : Bits) :
    (rounding mode T D tape).map Result.observe = execute T (model mode n D) tape := by
  cases mode
  · exact PhysicalVertexRounding.weighted_observe T D tape
  · exact PhysicalVertexRounding.size_observe T D tape

def round {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) : PhysicalVertexSampling.Runner (lineSize n) :=
  fun T r tape =>
    let gadget := EncodedEdgeGadget.build (EncodedEdgeLineInput.roundingInput D r.weights)
    (rounding mode T gadget.data tape).map
      (PhysicalVertexRounding.project (fun mask => (toLine (EncodedEdgeRounding.pullback gadget mask),0)) 0)

theorem round_observe {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) :
    (round D mode T r tape).map Result.observe = execute T (EncodedEdgeSolver.round D (model mode) r) tape := by
  unfold round EncodedEdgeSolver.round EncodedEdgeRounding.tree
  dsimp only
  rw [PhysicalVertexRounding.project_observe _ _ (fun _ => rfl),rounding_observe,execute_map,execute_map]
  simp only [Option.map_map,Function.comp_def]

structure EdgeResult (n : ℕ) where
  output : EncodedEdgeSolver.Output n
  suffix : Bits
  dispatch : ℕ
  readback : ℕ
  roundingAndSelection : ℕ

def EdgeResult.observe {n : ℕ} (r : EdgeResult n) : EncodedEdgeSolver.Output n × Bits := (r.output,r.suffix)

def run {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) : Option (EdgeResult n) :=
  let e := confidenceExponent n κ
  (PhysicalAmplifiedVertexSolver.run (binaryLineInput D) (round D mode)
    (EncodedEdgeSolver.drawBound n) e (e+1) tape).map fun r =>
      ⟨EncodedEdgeSolver.outputFor D r.output,r.suffix,r.dispatch,r.readback,r.roundingAndSelection⟩

theorem run_observe {n : ℕ} (κ : ℕ) (D : Input n) (mode : ChargedVertexModes.Mode) (tape : Bits) :
    (run κ D mode tape).map EdgeResult.observe =
      (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ D (model mode)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  let e := confidenceExponent n κ
  let ref := EncodedEdgeSolver.round D (model mode)
  let runVertex := PhysicalAmplifiedVertexSolver.run (binaryLineInput D) (round D mode)
    (EncodedEdgeSolver.drawBound n) e (e+1) tape
  let abstract := boundedBitTree (EncodedEdgeSolver.drawBound n) e (e+1) (lineInput D) ref
  have vertex := PhysicalAmplifiedVertexSolver.run_observe (binaryLineInput D) (round D mode) ref
    (EncodedEdgeSolver.drawBound n) e (e+1) tape (round_observe D mode)
  rw [decode_binaryLineInput] at vertex
  change runVertex.map PhysicalAmplifiedVertexSolver.Result.observe =
    (EncodedSolverBits.run abstract tape).map (fun (out,(rest,_)) => (out,rest)) at vertex
  have eq : EncodedEdgeSolver.bitTree κ D (model mode) = map (EncodedEdgeSolver.outputFor D) abstract := rfl
  rw [eq,EncodedSolverBits.run_map]
  have resultEq : (run κ D mode tape).map EdgeResult.observe =
      (runVertex.map PhysicalAmplifiedVertexSolver.Result.observe).map
        (fun (out,rest) => (EncodedEdgeSolver.outputFor D out,rest)) := by
    cases h : runVertex <;> simp [run,runVertex,e,h,EdgeResult.observe,PhysicalAmplifiedVertexSolver.Result.observe] at *
  rw [resultEq,vertex]
  simp only [Option.map_map,Function.comp_def]

end DirectedFlowCutGap.PhysicalAmplifiedEdgeSolver
