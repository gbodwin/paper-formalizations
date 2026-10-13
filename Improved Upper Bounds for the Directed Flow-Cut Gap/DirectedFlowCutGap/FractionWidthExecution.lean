import DirectedFlowCutGap.FractionWidthTrace

namespace DirectedFlowCutGap.FractionWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem size_length (word : Bits) : (BinaryCounters.sizeBits word).1.length ≤ word.length := by
  have h := (BinaryLengthProgram.countWord_spec (trim word).1.length []).2
  rw [BinarySizeProgram.countWord_exact] at h
  simp only [List.length_nil,Nat.zero_add] at h
  exact h.trans (trim_spec word).2.2.1

def inputSteps (q : BinaryRational.Fraction) : ℕ := 128*(q.num.length+q.den.length+1)^2

theorem steps_bound (q : BinaryRational.Fraction) : steps q+1 ≤ inputSteps q := by
  have hn := BinarySizeProgram.steps_bound q.num
  have hd := BinarySizeProgram.steps_bound q.den
  have hm := BinaryMaximumProgram.steps_bound (BinaryCounters.sizeBits q.num).1 (BinaryCounters.sizeBits q.den).1
  have ln := size_length q.num
  have ld := size_length q.den
  unfold steps inputSteps BinarySizeProgram.inputSteps BinaryMaximumProgram.inputSteps at *
  nlinarith

theorem width {q : BinaryRational.Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : RationalComparisonProgram.Stored heap a q) (next b c d : ℕ) (hn : next=heap.length)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root,ext.length=cells q ∧
      NaturalRun program (steps q+1) (state heap next a b c d stack source 126) []
        (state (heap++ext) (next+ext.length) a b c root stack source 127) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.fractionWidth q).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := width_return input next b c d hn ⟨a,b,c,d⟩ 127 stack source
  have first : tickNatural program (state heap next a b c d stack source 126)=
      some ⟨state heap next a b c d (⟨127,.r3,⟨a,b,c,d⟩⟩::stack) source 110,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.FractionWidthProgram
