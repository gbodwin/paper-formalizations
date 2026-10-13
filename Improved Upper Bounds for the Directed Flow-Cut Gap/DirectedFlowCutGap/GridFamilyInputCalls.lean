import DirectedFlowCutGap.GridFamilyInputCallLift

namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem grid_call {heap : NaturalHeap} {a : ℕ} {rows : List BinaryRational.Fraction}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 10760)
    (stack : List (Frame ℕ 10760)) (source : Bits) :
    ∃ ext root,NaturalRun program (GridInputProgram.steps rows+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10722) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GridInputProgram.Prepared (heap++ext) root rows := by
  obtain ⟨ext,root,_len,run,rep⟩ := GridInputProgram.prepare table next b c d dense [] source
  have lift := child_return gridLabel GridInputProgram.program grid_slots run rfl rfl .r3 .r3 saved pc stack
    (by simp only [GridInputProgram.state];simp [program,gridLabel,callable,GridInputProgram.program])
  refine ⟨ext,root,?_,rep⟩
  simpa [state,GridInputProgram.state,gridLabel,Registers.get,Registers.set,Nat.add_assoc] using lift

theorem family_call {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c : ℕ} {exponent fuel : Bits}
    (context : GridFamily.Context heap a adjacency costs xs) (exp : BoolList heap b exponent)
    (input : BoolList heap c fuel) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10760) (stack : List (Frame ℕ 10760)) (source : Bits) :
    ∃ k ext root,k ≤ GridFamily.instructionBound ds.length costs.toList exponent fuel+2 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10178) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GridFamily.StateList (heap++ext) root (GridFamily.values adjacency ds costs exponent fuel) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := GridFamily.compute adjacency costs encoded context exp input next d dense source
  have lift := child_return familyLabel GridFamily.program family_slots run rfl rfl .r3 .r3 saved pc stack
    (by simp only [GridFamily.state];simp [program,familyLabel,callable,GridFamily.program])
  refine ⟨k+1,ext,root,by omega,?_,rep⟩
  simpa [state,GridFamily.state,familyLabel,Registers.get,Registers.set] using lift
end DirectedFlowCutGap.GridFamilyInput
