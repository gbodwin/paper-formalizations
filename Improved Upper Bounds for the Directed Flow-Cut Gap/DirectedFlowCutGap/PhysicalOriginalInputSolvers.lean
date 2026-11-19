import DirectedFlowCutGap.PhysicalAmplifiedEdgeSolver

/-! Original bitstrings and finite fair tapes for the vertex and edge entries. -/

namespace DirectedFlowCutGap.PhysicalOriginalInputSolvers

open BinaryArithmetic FiniteDrawTrees

def vertex (κ : ℕ) (mode : ChargedVertexModes.Mode) (graph tape : Bits) :
    Option (Σ n,PhysicalAmplifiedVertexSolver.Result n) :=
  PhysicalVertexSolver.prepareOn
    (fun _ input => PhysicalAmplifiedVertexSolver.vertex κ mode input tape) (EncodedVertexInput.parse graph)

theorem vertex_encoded_success {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) {r : PhysicalAmplifiedVertexSolver.Result n}
    (ran : PhysicalAmplifiedVertexSolver.vertex κ mode D tape=some r) :
    vertex κ mode (PhysicalSourceDispatch.input D) tape=some ⟨n,r⟩ :=
  PhysicalVertexSolver.prepareOn_eq (fun _ input => PhysicalAmplifiedVertexSolver.vertex κ mode input tape)
    (EncodedVertexInput.parse_encode D) ran

theorem vertex_fairTape {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n) :
    let G := BinaryFractionalGuesses.decodeInput D
    (EncodedSolverBits.fairTape (EncodedSolverBits.vertexBudget κ G)).map
      (fun tape => (PhysicalAmplifiedVertexSolver.vertex κ mode D tape).map
        PhysicalAmplifiedVertexSolver.Result.output) =
      (ideal (EncodedVertexAmplification.polynomialBitTree κ G (ChargedVertexModes.round n mode))).map some := by
  dsimp only
  have h : (fun tape => (PhysicalAmplifiedVertexSolver.vertex κ mode D tape).map
      PhysicalAmplifiedVertexSolver.Result.output) =
      (fun tape => (EncodedSolverBits.run (EncodedVertexAmplification.polynomialBitTree κ
        (BinaryFractionalGuesses.decodeInput D) (ChargedVertexModes.round n mode)) tape).map Prod.fst) := by
    funext tape
    have h := congrArg (Option.map Prod.fst) (PhysicalAmplifiedVertexSolver.vertex_observe κ mode D tape)
    simpa only [Option.map_map,Function.comp_def,PhysicalAmplifiedVertexSolver.Result.observe] using h
  rw [h]
  have within : Within (EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D))
      (EncodedVertexAmplification.polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (ChargedVertexModes.round n mode)) := by
    cases mode
    · exact EncodedSolverBits.vertex_mass_within κ _
    · exact EncodedSolverBits.vertex_size_within κ _
  exact EncodedSolverBits.run_fairTape within (EncodedAmplification.bitTree_binary ..)

def edge (κ : ℕ) (mode : ChargedVertexModes.Mode) (graph tape : Bits) :
    Option (Σ n,PhysicalAmplifiedEdgeSolver.EdgeResult n) :=
  PhysicalVertexSolver.prepareOn
    (fun _ input => PhysicalAmplifiedEdgeSolver.run κ (EncodedEdgeInput.decodeInput input) mode tape)
    (EncodedEdgeInput.parse graph)

theorem edge_encoded_success {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : EncodedEdgeInput.Input n) (tape : Bits) {r : PhysicalAmplifiedEdgeSolver.EdgeResult n}
    (ran : PhysicalAmplifiedEdgeSolver.run κ (EncodedEdgeInput.decodeInput D) mode tape=some r) :
    edge κ mode (EncodedEdgeInput.encode D) tape=some ⟨n,r⟩ :=
  PhysicalVertexSolver.prepareOn_eq
    (fun _ input => PhysicalAmplifiedEdgeSolver.run κ (EncodedEdgeInput.decodeInput input) mode tape)
    (EncodedEdgeInput.parse_encode D) ran

theorem edge_fairTape {n : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n) (mode : ChargedVertexModes.Mode) :
    (EncodedSolverBits.fairTape (EncodedSolverBits.edgeBudget κ D)).map
      (fun tape => (PhysicalAmplifiedEdgeSolver.run κ D mode tape).map PhysicalAmplifiedEdgeSolver.EdgeResult.output) =
      (ideal (EncodedEdgeSolver.bitTree κ D (PhysicalAmplifiedEdgeSolver.model mode))).map some := by
  have h : (fun tape => (PhysicalAmplifiedEdgeSolver.run κ D mode tape).map
      PhysicalAmplifiedEdgeSolver.EdgeResult.output) =
      (fun tape => (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ D (PhysicalAmplifiedEdgeSolver.model mode)) tape).map
        Prod.fst) := by
    funext tape
    have h := congrArg (Option.map Prod.fst) (PhysicalAmplifiedEdgeSolver.run_observe κ D mode tape)
    simpa only [Option.map_map,Function.comp_def,PhysicalAmplifiedEdgeSolver.EdgeResult.observe] using h
  rw [h]
  have within : Within (EncodedSolverBits.edgeBudget κ D) (EncodedEdgeSolver.bitTree κ D (PhysicalAmplifiedEdgeSolver.model mode)) := by
    cases mode
    · exact EncodedSolverBits.edge_mass_within κ D
    · exact EncodedSolverBits.edge_size_within κ D
  exact EncodedSolverBits.run_fairTape within (EncodedEdgeSolver.bitTree_binary κ D _)

end DirectedFlowCutGap.PhysicalOriginalInputSolvers
