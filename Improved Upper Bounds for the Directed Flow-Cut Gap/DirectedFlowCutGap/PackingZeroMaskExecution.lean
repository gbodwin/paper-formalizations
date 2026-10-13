import DirectedFlowCutGap.PackingZeroMaskTrace

namespace DirectedFlowCutGap.PackingZeroMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem steps_bound (rows : List (Bits × Bits)) :
    steps rows ≤ 4*SourceRowTableProgram.bits rows+16*rows.length+3 := by
  induction rows with
  | nil => simp [steps,SourceRowTableProgram.bits]
  | cons r rs ih =>
    have hz := BinaryZeroProgram.steps_bound r.1
    simp only [steps,SourceRowTableProgram.bits,List.length_cons,Nat.mul_add] at *
    omega

theorem scan {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : WordPairTableRead.Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (stack : List (Frame ℕ 32)) (source : Bits) :
    ∃ ext root, ext.length=2*rows.length+1 ∧
      NaturalRun program (steps rows+1) (state heap next a b c d stack source 30) []
        (state (heap++ext) (next+ext.length) a b c root stack source 31) ∧
      BoolList (heap++ext) root (mask rows) := by
  obtain ⟨ext,root,len,run,rep⟩ := mask_return table next b c d hn ⟨a,b,c,d⟩ 31 stack source
  have call : tickNatural program (state heap next a b c d stack source 30)=
      some ⟨state heap next a b c d (⟨31,.r3,⟨a,b,c,d⟩⟩::stack) source 10,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩
end DirectedFlowCutGap.PackingZeroMask
