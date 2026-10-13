import DirectedFlowCutGap.PositiveInventoryTrace

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem steps_bound (rows : List Fraction) :
    steps rows ≤ 4*SourceRowTableProgram.bits (IndexedRationalRead.fields rows)+24*rows.length+3 := by
  induction rows with
  | nil => simp [steps,IndexedRationalRead.fields,SourceRowTableProgram.bits]
  | cons q qs ih =>
    have hz := BinaryZeroProgram.steps_bound q.num
    have branch : (if (BinaryArithmetic.isZero q.num).1 then 6 else 13)≤13 := by split <;> omega
    simp only [steps,IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits,
      List.length_cons,Nat.mul_add] at *
    omega

theorem cells_bound (rows : List Fraction) : cells rows≤4*rows.length+1 := by
  induction rows with
  | nil => simp [cells]
  | cons q qs ih =>
    simp only [cells,List.length_cons]
    split <;> omega

theorem scan (rows : List Fraction) (words : List Bits) (aligned : words.length=rows.length)
    {heap : NaturalHeap} {a b : ℕ} (verts : GraphDiscoveryProgram.Vertices heap a words)
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows+1) (state heap next a b c d stack source 46) []
        (state (heap++ext) (next+ext.length) a b c root stack source 47) ∧
      Inventory (heap++ext) root (selected (words.zip rows)) := by
  obtain ⟨ext,root,len,run,rep⟩ := inventory_return rows words aligned verts table next c d hn
    ⟨a,b,c,d⟩ 47 stack source
  have call : tickNatural program (state heap next a b c d stack source 46)=
      some ⟨state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::stack) source 10,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩
end DirectedFlowCutGap.PositiveInventory
