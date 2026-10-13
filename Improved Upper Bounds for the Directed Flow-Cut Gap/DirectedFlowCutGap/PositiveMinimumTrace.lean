import DirectedFlowCutGap.PositiveMinimumBound

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem minimum_return (rows : List Fraction) (words : List Bits) (aligned : words.length=rows.length)
    {heap : NaturalHeap} {a b : ℕ} (verts : GraphDiscoveryProgram.Vertices heap a words)
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 256)
    (stack : List (Frame ℕ 256)) (source : Bits) (W : ℕ)
    (size : ∀ q∈rows,q.num.length≤W ∧ q.den.length≤W) :
    ∃ k ext root,k+1≤ inputSteps rows W ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 248) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Result (heap++ext) root (select (PositiveInventory.selected (words.zip rows))) := by
  let frame : Frame ℕ 256 := ⟨pc,.r3,saved⟩
  obtain ⟨ext,inventory,_,prepared,rep⟩ := inventory_call rows words aligned verts table next c d hn
    ⟨a,b,c,d⟩ 249 (frame::stack) source
  obtain ⟨items,itemList,rel⟩ := PositiveInventory.inventory_items rep
  have rel' : List.Forall₂ (Encoded (heap++ext)) (PositiveInventory.selected (words.zip rows)) items := rel
  obtain ⟨more,root,_,selected,answer⟩ := argmin_call items itemList (next+ext.length) b c inventory
    (by simp [hn]) ⟨inventory,b,c,inventory⟩ 251 (frame::stack) source
  have t248 : tickNatural program (state heap next a b c d (frame::stack) source 248)=
      some ⟨state heap next a b c d (⟨249,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 46,[],0⟩ := by rfl
  have t249 : tickNatural program (state (heap++ext) (next+ext.length) a b c inventory (frame::stack) source 249)=
      some ⟨state (heap++ext) (next+ext.length) inventory b c inventory (frame::stack) source 250,[],0⟩ := by rfl
  have t250 : tickNatural program
      (state (heap++ext) (next+ext.length) inventory b c inventory (frame::stack) source 250)=
      some ⟨state (heap++ext) (next+ext.length) inventory b c inventory
        (⟨251,.r3,⟨inventory,b,c,inventory⟩⟩::frame::stack) source 226,[],0⟩ := by rfl
  have t251 : tickNatural program
      (state ((heap++ext)++more) (next+ext.length+more.length) inventory b c root (frame::stack) source 251)=
      some ⟨state ((heap++ext)++more) (next+ext.length+more.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨PositiveInventory.steps rows+RetainedArgminProgram.steps items+7,ext++more,root,?_,?_,?_⟩
  · simpa only [Nat.add_assoc] using total_bound rows words items W rel' size
  · have all := NaturalRun.step t248 (run_append prepared (.step t249 (.step t250
      (run_append selected (.step t251 (.done _))))))
    convert all using 1 <;> simp [state,List.append_assoc,Nat.add_assoc]
    omega
  · have result := selected_related (related_extend rel' more) answer
    simpa only [List.append_assoc] using result
end DirectedFlowCutGap.PositiveMinimum
