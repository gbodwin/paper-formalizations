import DirectedFlowCutGap.PackingAmountProgram

namespace DirectedFlowCutGap.PackingAmount
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem amount_high {word : Bits} {rows : List Fraction} (initial : NaturalState 44)
    (pc0 : initial.pc=40) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    {mask index : ℕ} (choice : initial.heap[initial.registers.a]?=some (.pair mask index))
    (indexRep : BoolList initial.heap index word)
    (table : StoredList initial.heap initial.registers.b rows) (hi : value word<rows.length) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+6) initial []
        (state (initial.heap++ext) (initial.next+ext.length) index initial.registers.b
          initial.registers.c root [] initial.source 42) ∧
      Stored (initial.heap++ext) root (IndexedRationalRead.lookup rows word) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty choice indexRep table
      subst pc;subst stack
      have t40 : tickNatural program (state heap next a b c d [] source 40)=
          some ⟨state heap next index b c d [] source 41,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,choice]
      have t41 : tickNatural program (state heap next index b c d [] source 41)=
          some ⟨state heap next index b c d [⟨42,.r3,⟨index,b,c,d⟩⟩] source 28,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := read_return indexRep table hi next c d hn ⟨index,b,c,d⟩ 42 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step t40 (.step t41 run),rep⟩

theorem lookup_get {m : ℕ} (capacity : Row m) (j : Fin m) (word : Bits)
    (label : value word=j.val) : IndexedRationalRead.lookup capacity.toList word=get capacity j := by
  simp [IndexedRationalRead.lookup,label,BinaryFractionalRows.get]

theorem choice_high {m : ℕ} (capacity : Row m) (q : BinaryFractionalCore.Choice m)
    (labels : Fin m → Bits) (numeric : ∀ j,value (labels j)=j.val)
    (initial : NaturalState 44) (pc0 : initial.pc=40) (hn : initial.next=initial.heap.length)
    (empty : initial.stack=[]) (choice : OracleChoice.StoredChoice initial.heap initial.registers.a labels q)
    (table : StoredList initial.heap initial.registers.b capacity.toList) :
    ∃ ext root index,ext.length=q.bottleneck.val+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps (labels q.bottleneck)+6) initial []
        (state (initial.heap++ext) (initial.next+ext.length) index initial.registers.b
          initial.registers.c root [] initial.source 42) ∧
      Stored (initial.heap++ext) root (get capacity q.bottleneck) ∧
      BoolList (initial.heap++ext) index (labels q.bottleneck) := by
  obtain ⟨mask,index,hchoice,_,hindex⟩ := choice
  have hi : value (labels q.bottleneck)<capacity.toList.length := by
    simp only [numeric,Vector.length_toList]
    exact q.bottleneck.isLt
  obtain ⟨ext,root,len,run,rep⟩ := amount_high initial pc0 hn empty hchoice hindex table hi
  refine ⟨ext,root,index,?_,run,?_,boolList_extend hindex ext⟩
  · simpa only [numeric] using len
  · simpa only [lookup_get capacity q.bottleneck _ (numeric _)] using rep
end DirectedFlowCutGap.PackingAmount
