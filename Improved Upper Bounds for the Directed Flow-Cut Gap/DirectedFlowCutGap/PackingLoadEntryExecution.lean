import DirectedFlowCutGap.PackingLoadEntryProgram

namespace DirectedFlowCutGap.PackingLoadEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem operand_high (enabled : Bool) (amount : Fraction) {heap : NaturalHeap}
    {next a b c d : ℕ} (flag : heap[c]?=some (.flag enabled))
    (amt : Stored heap b amount) (hn : next=heap.length) (source : Bits) :
    ∃ ext br cr,ext.length=(if enabled then 0 else 4) ∧
      NaturalRun program (if enabled then 1 else 5)
        (state heap next a b c d [] source 142) []
        (state (heap++ext) (next+ext.length) a br cr d [] source 148) ∧
      Stored (heap++ext) br (operand enabled amount) := by
  cases enabled with
  | true =>
    have ht : tickNatural program (state heap next a b c d [] source 142)=
        some ⟨state heap next a b c d [] source 148,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,flag]
    exact ⟨[],b,c,rfl,by simpa using NaturalRun.step ht (.done _),by simpa [operand] using amt⟩
  | false =>
    let h1 := heap++[.nil]
    let h2 := h1++[.flag true]
    let h3 := h2++[.pair (next+1) next]
    let h4 := h3++[.pair next (next+2)]
    let e0 : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
    have nilCell : h4[next]?=some .nil := by simp [h4,h3,h2,h1,hn]
    have flagCell : h4[next+1]?=some (.flag true) := by simp [h4,h3,h2,h1,hn]
    have pairCell : h4[next+2]?=some (.pair (next+1) next) := by simp [h4,h3,h2,h1,hn]
    have record : h4[next+3]?=some (.pair next (next+2)) := by simp [h4,h3,h2,h1,hn]
    have zeroRep : Stored h4 (next+3) BinaryRational.zero :=
      ⟨next,next+2,record,.nil nilCell,.cons pairCell flagCell (.nil nilCell)⟩
    have t142 : tickNatural program (state heap next a b c d [] source 142)=
        some ⟨state heap next a b c d [] source 143,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,flag]
    have t143 : tickNatural program (state heap next a b c d [] source 143)=
        some ⟨state h1 (next+1) a next c d [] source 144,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
    have t144 : tickNatural program (state h1 (next+1) a next c d [] source 144)=
        some ⟨state h2 (next+2) a next (next+1) d [] source 145,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h2,Nat.add_assoc]
    have t145 : tickNatural program (state h2 (next+2) a next (next+1) d [] source 145)=
        some ⟨state h3 (next+3) a next (next+2) d [] source 146,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h3,Nat.add_assoc]
    have t146 : tickNatural program (state h3 (next+3) a next (next+2) d [] source 146)=
        some ⟨state h4 (next+4) a (next+3) (next+2) d [] source 148,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h4,Nat.add_assoc]
    refine ⟨e0,next+3,next+2,rfl,?_,?_⟩
    · simpa [e0,h4,h3,h2,h1,List.append_assoc] using
        NaturalRun.step t142 (.step t143 (.step t144 (.step t145 (.step t146 (.done _)))))
    · simpa [e0,h4,h3,h2,h1,List.append_assoc,operand] using zeroRep

theorem entry_high (enabled : Bool) (amount y : Fraction) {heap : NaturalHeap} {a b c : ℕ}
    (weight : Stored heap a y) (amt : Stored heap b amount) (flag : heap[c]?=some (.flag enabled))
    (next d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext root br cr,ext.length=cells enabled amount y ∧
      NaturalRun program (steps enabled amount y)
        (state heap next a b c d [] source 142) []
        (state (heap++ext) (next+ext.length) a br cr root [] source 149) ∧
      Stored (heap++ext) root (result enabled amount y) := by
  obtain ⟨e0,br,cr,l0,pre,rep⟩ := operand_high (a:=a) (d:=d) enabled amount flag amt hn source
  have dense : next+e0.length=(heap++e0).length := by simp [hn]
  obtain ⟨ea,ra,la,high,addRep⟩ := CanonicalRationalAddition.add_high y (operand enabled amount)
    (CanonicalRationalAddition.state (heap++e0) (next+e0.length) a br cr d [] source 140)
    rfl dense (stored_extend weight e0) rep rfl
  have called := call_run label CanonicalRationalAddition.program slots high
    (by simp [program,label,CanonicalRationalAddition.program,callable]) ⟨a,br,cr,d⟩ 149 []
  have body : NaturalRun program (CanonicalRationalAddition.instructions y (operand enabled amount)+2)
      (state (heap++e0) (next+e0.length) a br cr d [⟨149,.r3,⟨a,br,cr,d⟩⟩] source 140) []
      (state (heap++e0++ea) (next+e0.length+ea.length) a br cr ra [] source 149) := by
    convert called using 1 <;> simp [state,label,Nat.add_assoc]
    omega
  have call : tickNatural program (state (heap++e0) (next+e0.length) a br cr d [] source 148)=
      some ⟨state (heap++e0) (next+e0.length) a br cr d [⟨149,.r3,⟨a,br,cr,d⟩⟩] source 140,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++ea,ra,br,cr,?_,?_,?_⟩
  · simp [cells,la,l0];omega
  · convert run_append pre (.step call body) using 1 <;> simp [List.append_assoc,Nat.add_assoc,steps]
    split <;> omega
  · simpa [CanonicalRationalAddition.state,List.append_assoc,result] using addRep
end DirectedFlowCutGap.PackingLoadEntry
