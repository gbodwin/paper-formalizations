import DirectedFlowCutGap.GridFamilyCallLift
import DirectedFlowCutGap.GridFamilyData

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem guess_call {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap b exponent)
    (graph : GraphAdjacencyProgram.Matrix heap c (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap d xs)
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 10180)
    (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ k ext root,k ≤ MinimumGuess.inputSteps ds.length costs.toList exponent+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 9998) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      MinimumGuess.Result (heap++ext) root (MinimumGuess.result adjacency ds costs exponent) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := MinimumGuess.compute adjacency costs encoded table exp graph pairs next dense [] source
  have lift := child_return guessLabel MinimumGuess.program guess_slots run rfl rfl .r3 .r3
    saved pc stack (by simp only [MinimumGuess.state];simp [program,guessLabel,callable,MinimumGuess.program])
  refine ⟨k+1,ext,root,by omega,?_,rep⟩
  simpa [state,MinimumGuess.state,guessLabel,Registers.get,Registers.set] using lift

theorem guess_helper {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b : ℕ} {exponent : Bits}
    (context : Context heap a adjacency costs xs) (exp : BoolList heap b exponent)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 10180)
    (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ k ext root,k ≤ MinimumGuess.inputSteps ds.length costs.toList exponent+8 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10110) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      MinimumGuess.Result (heap++ext) root (MinimumGuess.result adjacency ds costs exponent) := by
  cases context with
  | @intro cr gr dr tail look inner table graph pairs =>
    let frame : Frame ℕ 10180 := ⟨pc,.r3,saved⟩
    have t0 : tickNatural program (state heap next a b c d (frame::stack) source 10110)=
        some ⟨state heap next a b c a (frame::stack) source 10111,[],0⟩ := by rfl
    have t1 : tickNatural program (state heap next a b c a (frame::stack) source 10111)=
        some ⟨state heap next cr b c a (frame::stack) source 10112,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,look]
    have t2 : tickNatural program (state heap next cr b c a (frame::stack) source 10112)=
        some ⟨state heap next cr b c tail (frame::stack) source 10113,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,look]
    have t3 : tickNatural program (state heap next cr b c tail (frame::stack) source 10113)=
        some ⟨state heap next cr b gr tail (frame::stack) source 10114,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,inner]
    have t4 : tickNatural program (state heap next cr b gr tail (frame::stack) source 10114)=
        some ⟨state heap next cr b gr dr (frame::stack) source 10115,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,inner]
    have t5 : tickNatural program (state heap next cr b gr dr (frame::stack) source 10115)=
        some ⟨state heap next cr b gr dr (⟨10116,.r3,⟨cr,b,gr,dr⟩⟩::frame::stack) source 9998,[],0⟩ := by rfl
    obtain ⟨k,ext,root,bound,run,rep⟩ := guess_call adjacency costs encoded table exp graph pairs next dense
      ⟨cr,b,gr,dr⟩ 10116 (frame::stack) source
    have ret : tickNatural program (state (heap++ext) (next+ext.length) cr b gr root (frame::stack) source 10116)=
        some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frame,Registers.get,Registers.set]
    refine ⟨k+7,ext,root,by omega,?_,rep⟩
    have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5
      (run_append run (.step ret (.done _))))))))
    simpa [frame,Nat.add_assoc] using whole
end DirectedFlowCutGap.GridFamily
