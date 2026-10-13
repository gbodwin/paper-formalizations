import DirectedFlowCutGap.KeptMaskInputTrace

namespace DirectedFlowCutGap.KeptMaskInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (s t : Bits) (vs : List Bits) (rows : List (Bits × Bits)) : ℕ :=
  4*SourceRowTableProgram.bits rows+16*rows.length+KeptMask.inputSteps s t vs+18

theorem steps_bound (s t : Bits) (vs : List Bits) (rows : List (Bits × Bits)) :
    steps s t vs rows+1 ≤ inputSteps s t vs rows := by
  have hz := PackingZeroMask.steps_bound rows
  have hk := KeptMask.steps_bound s t vs (PackingZeroMask.mask rows)
  unfold steps inputSteps
  omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {rows : List (Bits × Bits)}
    (hv : Vertices heap a vs) (hc : Context heap b s t rows) (aligned : vs.length=rows.length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs rows ∧ NaturalRun program (steps s t vs rows+1)
      (state heap next a b c d stack source 198) []
      (state (heap++ext) (next+ext.length) a b c root stack source 199) ∧
      BoolList (heap++ext) root (mask s t vs rows) := by
  obtain ⟨ext,root,len,run,rep⟩ := input_return hv hc aligned next c d hn ⟨a,b,c,d⟩ 199 stack source
  have call : tickNatural program (state heap next a b c d stack source 198)=
      some ⟨state heap next a b c d (⟨199,.r3,⟨a,b,c,d⟩⟩::stack) source 170,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem mask_original {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (vs : List (Fin n)) (c : BinaryFractionalRows.Row n) :
    mask (label s) (label t) (vs.map label) (IndexedRationalRead.fields c.toList)=
      List.zipWith (fun u zero => !zero || decide (u=s) || decide (u=t)) vs
        (BinaryFractionalDispatch.zeroMask c).1.toList := by
  unfold mask
  rw [PackingZeroMask.mask_eq_original,KeptMask.mask_encode label hlabel]
end DirectedFlowCutGap.KeptMaskInput
