import DirectedFlowCutGap.GridFamilyGuard
import DirectedFlowCutGap.GridFamilyGuessCall

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
set_option maxRecDepth 32768

theorem head_run {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c : ℕ} {exponent fuel : Bits}
    (context : Context heap a adjacency costs xs) (exp : BoolList heap b exponent)
    (input : BoolList heap c fuel) (nonzero : (isZero fuel).1=false)
    (next d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ k ext root,k ≤ BinaryZeroProgram.steps fuel+MinimumGuess.inputSteps ds.length costs.toList exponent+16 ∧
      NaturalRun program k (state heap next a b c d stack source 10130) []
        (state (heap++ext) (next+ext.length) a b c root stack source 10133) ∧
      MinimumGuess.Result (heap++ext) root (MinimumGuess.result adjacency ds costs exponent) := by
  have front : NaturalRun program (BinaryZeroProgram.steps fuel+6)
      (state heap next a b c d stack source 10130) []
      (state (heap++[.flag false]) (next+1) a b c next stack source 10131) := by
    simpa [nonzero] using guard_prefix input next a b d dense stack source
  have t0 : tickNatural program
      (state (heap++[.flag false]) (next+1) a b c next stack source 10131)=
      some ⟨state (heap++[.flag false]) (next+1) a b c next stack source 10132,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,dense]
  have t1 : tickNatural program
      (state (heap++[.flag false]) (next+1) a b c next stack source 10132)=
      some ⟨state (heap++[.flag false]) (next+1) a b c next
        (⟨10133,.r3,⟨a,b,c,next⟩⟩::stack) source 10110,[],0⟩ := by rfl
  obtain ⟨k,ext,root,bound,run,rep⟩ := guess_helper adjacency costs encoded
    (context_extend context [.flag false]) (boolList_extend exp [.flag false])
    (next+1) c next (by simp [dense]) ⟨a,b,c,next⟩ 10133 stack source
  refine ⟨BinaryZeroProgram.steps fuel+6+(1+(1+k)),[.flag false]++ext,root,by omega,?_,?_⟩
  · simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run_append front (.step t0 (.step t1 run))
  · simpa [List.append_assoc] using rep
end DirectedFlowCutGap.GridFamily
