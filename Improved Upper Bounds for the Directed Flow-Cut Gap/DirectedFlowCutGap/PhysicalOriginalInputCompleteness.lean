import DirectedFlowCutGap.PhysicalOriginalInputSolvers

/-! Completeness of the physical entries on any parse-accepted original source. -/

namespace DirectedFlowCutGap.PhysicalOriginalInputCompleteness

open BinaryArithmetic FiniteDrawTrees EncodedSolverBits

private theorem returns {A R : Type} (output : R → A) (suffix : R → Bits)
    {tree : FiniteDrawTrees.Tree A} {tape : Bits} (physical : Option R) (valid : A → Prop)
    (observed : physical.map (fun r => (output r,suffix r)) =
      (run tree tape).map (fun (a,(rest,_)) => (a,rest)))
    (correct : ∀ a ∈ (ideal tree).support, valid a) {bound : ℕ}
    (within : Within bound tree) (binary : LazyFairBitTrees.Binary tree) (enough : bound ≤ tape.length) :
    ∃ r used, physical=some r ∧ suffix r=tape.drop used ∧ used ≤ bound ∧ valid (output r) := by
  obtain ⟨a,k,reference,used⟩ := EncodedSolverBits.complete within binary tape enough
  have legal := correct a (run_support binary reference)
  rw [reference] at observed
  cases h : physical with
  | none => simp [h] at observed
  | some r =>
    simp only [h,Option.map_some,Option.some.injEq,Prod.mk.injEq] at observed
    exact ⟨r,k,rfl,observed.2,used,observed.1.symm ▸ legal⟩

theorem vertex_complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (source tape : Bits) (parsed : EncodedVertexInput.parse source=some ⟨n,D⟩)
    (enough : vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    ∃ r used, PhysicalOriginalInputSolvers.vertex κ mode source tape=some ⟨n,r⟩ ∧
      r.suffix=tape.drop used ∧ used ≤ vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) r.output := by
  let G := BinaryFractionalGuesses.decodeInput D
  let t := EncodedVertexAmplification.polynomialBitTree κ G (ChargedVertexModes.round n mode)
  have legal : ∀ a ∈ (ideal t).support, EncodedVertexSolver.Valid G a := by
    cases mode
    · exact fun _ h => EncodedVertexAmplification.massBit_support_valid _ _ _ h
    · exact fun _ h => EncodedVertexAmplification.sizeBit_support_valid _ _ _ h
  have within : Within (vertexBudget κ G) t := by
    cases mode
    · exact vertex_mass_within κ G
    · exact vertex_size_within κ G
  obtain ⟨r,k,ran,rest,used,ok⟩ := returns PhysicalAmplifiedVertexSolver.Result.output
    PhysicalAmplifiedVertexSolver.Result.suffix _ (EncodedVertexSolver.Valid G)
    (PhysicalAmplifiedVertexSolver.vertex_observe κ mode D tape) legal within
    (EncodedVertexAmplification.bitTree_binary ..) enough
  exact ⟨r,k,PhysicalOriginalInputSolvers.vertex_of_parse κ mode D source tape parsed ran,rest,used,ok⟩

theorem edge_complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (source tape : Bits) (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, PhysicalOriginalInputSolvers.edge κ mode source tape=some ⟨n,r⟩ ∧
      r.suffix=tape.drop used ∧ used ≤ edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  let G := EncodedEdgeInput.decodeInput D
  let t := EncodedEdgeSolver.bitTree κ G (PhysicalAmplifiedEdgeSolver.model mode)
  have legal : ∀ a ∈ (ideal t).support, EncodedEdgeSolver.Valid G a := by
    cases mode
    · exact fun _ h => EncodedEdgeSolver.mass_support_valid _ _ h
    · exact fun _ h => EncodedEdgeSolver.size_support_valid _ _ h
  have within : Within (edgeBudget κ G) t := by
    cases mode
    · exact edge_mass_within κ G
    · exact edge_size_within κ G
  obtain ⟨r,k,ran,rest,used,ok⟩ := returns PhysicalAmplifiedEdgeSolver.EdgeResult.output
    PhysicalAmplifiedEdgeSolver.EdgeResult.suffix _ (EncodedEdgeSolver.Valid G)
    (PhysicalAmplifiedEdgeSolver.run_observe κ G mode tape) legal within (EncodedEdgeSolver.bitTree_binary ..) enough
  exact ⟨r,k,PhysicalOriginalInputSolvers.edge_of_parse κ mode D source tape parsed ran,rest,used,ok⟩

end DirectedFlowCutGap.PhysicalOriginalInputCompleteness
