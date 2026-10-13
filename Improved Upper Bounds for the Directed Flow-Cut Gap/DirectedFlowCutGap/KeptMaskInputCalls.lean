import DirectedFlowCutGap.KeptMaskInputCallLift

namespace DirectedFlowCutGap.KeptMaskInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem zero_return {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : WordPairTableRead.Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 200) (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=2*rows.length+1 ∧ NaturalRun program (PackingZeroMask.steps rows+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 30) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (PackingZeroMask.mask rows) := by
  obtain ⟨ext,root,len,core,rep⟩ := PackingZeroMask.scan table next b c d hn [] source
  have lifted := child_return zeroLabel PackingZeroMask.program zero_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [PackingZeroMask.state,zeroLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem mask_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {zs : Bits}
    (hv : Vertices heap a vs) (hc : KeptMask.Context heap b s t zs) (aligned : vs.length=zs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 200)
    (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=KeptMask.cells s t vs zs ∧ NaturalRun program (KeptMask.steps s t vs zs+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 162) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (KeptMask.mask s t vs zs) := by
  obtain ⟨ext,root,len,core,rep⟩ := KeptMask.scan hv hc aligned next c d hn [] source
  have lifted := child_return maskLabel KeptMask.program mask_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptMask.state,maskLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.KeptMaskInput
