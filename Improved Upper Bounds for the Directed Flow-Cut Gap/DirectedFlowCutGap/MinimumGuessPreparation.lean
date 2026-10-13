import DirectedFlowCutGap.MinimumGuessCalls

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem prepare_return {n : ℕ} (costs : BinaryFractionalRows.Row n) {heap : NaturalHeap}
    {a b : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap b exponent) (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10000) (stack : List (Frame ℕ 10000)) (source : Bits) :
    ∃ k ext root,k ≤ MinimumShift.inputSteps costs.toList exponent+4 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r1,saved⟩::stack) source 9980) []
        (state (heap++ext) (next+ext.length) saved.a root saved.c saved.d stack source pc) ∧
      MinimumShift.Result (heap++ext) root (MinimumShift.result costs exponent) := by
  let frames := ⟨pc,.r1,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 9980)=
      some ⟨state heap next a b b d frames source 9981,[],0⟩ := by rfl
  have t1 : tickNatural program (state heap next a b b d frames source 9981)=
      some ⟨state heap next a b b d (⟨9982,.r3,⟨a,b,b,d⟩⟩::frames) source 1558,[],0⟩ := by rfl
  obtain ⟨k,ext,root,bound,run,rep⟩ := shift_call costs table exp next b d dense ⟨a,b,b,d⟩ 9982 frames source
  have t2 : tickNatural program (state (heap++ext) (next+ext.length) a b b root frames source 9982)=
      some ⟨state (heap++ext) (next+ext.length) saved.a root saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨k+3,ext,root,by omega,by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using NaturalRun.step t0 (.step t1 (run_append run (.step t2 (.done _)))),rep⟩
end DirectedFlowCutGap.MinimumGuess
