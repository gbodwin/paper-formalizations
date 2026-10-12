import DirectedFlowCutGap.MaskedRationalRowProgram

namespace DirectedFlowCutGap.MaskedRationalRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem head_return (enabled : Bool) {heap : NaturalHeap} {next a b c d row mask head rest tail : ℕ}
    {x : Fraction} {xs : List Fraction} (flag : heap[b]?=some (.flag enabled))
    (original : heap[a]?=some (.pair row mask)) (entry : heap[row]?=some (.pair head rest))
    (ctx : heap[c]?=some (.pair a tail)) (valueRep : Stored heap head x)
    (tailRep : StoredList heap tail xs) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 24) (stack : List (Frame ℕ 24)) (source : Bits) :
    ∃ ext root,ext.length=(if enabled then 1 else 5) ∧
      NaturalRun program (if enabled then 6 else 8)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root ((if enabled then x else BinaryRational.zero)::xs) := by
  let frames : List (Frame ℕ 24) := ⟨pc,.r3,saved⟩::stack
  cases enabled with
  | true =>
    obtain ⟨body,rep⟩ := cons_return (d:=d) ctx valueRep tailRep hn saved pc stack source
    have t11 : tickNatural program (state heap next a b c d frames source 11)=
        some ⟨state heap next a b c d frames source 16,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,flag,tagBranch]
    have t16 : tickNatural program (state heap next a b c d frames source 16)=
        some ⟨state heap next row b c d frames source 17,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,original]
    have t17 : tickNatural program (state heap next row b c d frames source 17)=
        some ⟨state heap next head b c d frames source 19,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,entry]
    exact ⟨[.pair head tail],next,rfl,.step t11 (.step t16 (.step t17 body)),rep⟩
  | false =>
    let h1 := heap++[.nil]
    let h2 := h1++[.flag true]
    let h3 := h2++[.pair (next+1) next]
    let h4 := h3++[.pair next (next+2)]
    let zeroExt : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
    have eh : heap++zeroExt=h4 := by simp [zeroExt,h4,h3,h2,h1,List.append_assoc]
    have nilCell : h4[next]?=some .nil := by simp [h4,h3,h2,h1,hn]
    have flagCell : h4[next+1]?=some (.flag true) := by simp [h4,h3,h2,h1,hn]
    have pairCell : h4[next+2]?=some (.pair (next+1) next) := by simp [h4,h3,h2,h1,hn]
    have record : h4[next+3]?=some (.pair next (next+2)) := by simp [h4,h3,h2,h1,hn]
    have zeroRep : Stored h4 (next+3) BinaryRational.zero :=
      ⟨next,next+2,record,.nil nilCell,.cons pairCell flagCell (.nil nilCell)⟩
    have ctx' : h4[c]?=some (.pair a tail) := by rw [←eh];exact lookup_extend ctx zeroExt
    have tail' : StoredList h4 tail xs := by rw [←eh];exact list_extend tailRep zeroExt
    have dense : next+4=h4.length := by simp [h4,h3,h2,h1,hn]
    obtain ⟨body,rep⟩ := cons_return (b:=next+2) (d:=d) ctx' zeroRep tail' dense saved pc stack source
    have t11 : tickNatural program (state heap next a b c d frames source 11)=
        some ⟨state heap next a b c d frames source 12,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,flag,tagBranch]
    have t12 : tickNatural program (state heap next a b c d frames source 12)=
        some ⟨state h1 (next+1) next b c d frames source 13,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
    have t13 : tickNatural program (state h1 (next+1) next b c d frames source 13)=
        some ⟨state h2 (next+2) next (next+1) c d frames source 14,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h2]
    have t14 : tickNatural program (state h2 (next+2) next (next+1) c d frames source 14)=
        some ⟨state h3 (next+3) next (next+2) c d frames source 15,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h3]
    have t15 : tickNatural program (state h3 (next+3) next (next+2) c d frames source 15)=
        some ⟨state h4 (next+4) (next+3) (next+2) c d frames source 19,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h4]
    let ext := zeroExt++[.pair (next+3) tail]
    refine ⟨ext,next+4,rfl,?_,?_⟩
    · simpa [ext,zeroExt,h4,h3,h2,h1,frames,Nat.add_assoc,List.append_assoc] using
        NaturalRun.step t11 (.step t12 (.step t13 (.step t14 (.step t15 body))))
    · simpa [ext,zeroExt,h4,h3,h2,h1,List.append_assoc] using rep
end DirectedFlowCutGap.MaskedRationalRow
