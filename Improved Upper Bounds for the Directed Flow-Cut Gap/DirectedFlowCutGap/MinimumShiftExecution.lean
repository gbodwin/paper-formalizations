import DirectedFlowCutGap.MinimumShiftTrace

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem compute {n : ℕ} (costs : BinaryFractionalRows.Row n) {heap : NaturalHeap} {a c : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap c exponent) (next b d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 1560)) (source : Bits) :
    ∃ k ext root,k ≤ inputSteps costs.toList exponent ∧
      NaturalRun program k (state heap next a b c d stack source 1558) []
        (state (heap++ext) (next+ext.length) a b c root stack source 1559) ∧
      Result (heap++ext) root (result costs exponent) := by
  obtain ⟨k,ext,root,bound,body,rep⟩ := shifted_return costs table exp next b d dense
    ⟨a,b,c,d⟩ 1559 stack source
  have first : tickNatural program (state heap next a b c d stack source 1558)=
      some ⟨state heap next a b c d (⟨1559,.r3,⟨a,b,c,d⟩⟩::stack) source 1540,[],0⟩ := by rfl
  exact ⟨k+1,ext,root,bound,by simpa [Nat.add_comm] using NaturalRun.step first body,rep⟩
end DirectedFlowCutGap.MinimumShift
