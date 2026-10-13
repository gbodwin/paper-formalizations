import DirectedFlowCutGap.PositiveMinimumCallLift
import DirectedFlowCutGap.PositiveMinimumArgminCore

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem inventory_call (rows : List Fraction) (words : List Bits) (aligned : words.length=rows.length)
    {heap : NaturalHeap} {a b : ℕ} (verts : GraphDiscoveryProgram.Vertices heap a words)
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 256)
    (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=PositiveInventory.cells rows ∧
      NaturalRun program (PositiveInventory.steps rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 46) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PositiveInventory.Inventory (heap++ext) root (PositiveInventory.selected (words.zip rows)) := by
  obtain ⟨ext,root,len,core,rep⟩ := PositiveInventory.scan rows words aligned verts table next c d hn [] source
  have lift := child_return inventoryLabel PositiveInventory.program inventory_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [PositiveInventory.state,inventoryLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem argmin_call (xs : List RetainedArgminProgram.Item) {heap : NaturalHeap} {a : ℕ}
    (input : RetainedArgminProgram.ItemList heap a xs) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 256) (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=RetainedArgminProgram.cells xs ∧
      NaturalRun program (RetainedArgminProgram.steps xs+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 226) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RetainedArgminProgram.Selected (heap++ext) root (RetainedArgminProgram.select xs) := by
  obtain ⟨out,core,selected,_,src,frames,dense,ext,hpc,_⟩ :=
    RetainedArgminProgram.run_high_pc xs (RetainedArgminProgram.state heap next a b c d [] source 178)
      rfl hn input rfl
  obtain ⟨ext,he,len⟩ := ext
  have terminal : program (argminLabel out.pc)=.ret .r3 := by
    rcases hpc with hp | hp <;> rw [hp] <;> rfl
  have lift := child_return argminLabel RetainedArgminProgram.program argmin_slots core rfl frames
    .r3 .r3 saved pc stack terminal
  have un : out.next=next+ext.length := by rw [dense,he];simp [RetainedArgminProgram.state,hn]
  refine ⟨ext,out.registers.d,len,?_,?_⟩
  · simpa [RetainedArgminProgram.state,argminLabel,state,Registers.get,Registers.set,he,un,src] using lift
  · simpa only [he,RetainedArgminProgram.state] using selected
end DirectedFlowCutGap.PositiveMinimum
