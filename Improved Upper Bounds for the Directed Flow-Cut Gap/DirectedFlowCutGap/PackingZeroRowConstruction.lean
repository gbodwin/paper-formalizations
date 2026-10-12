import DirectedFlowCutGap.PackingZeroRowProgram

namespace DirectedFlowCutGap.PackingZeroRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem zero_high {heap : NaturalHeap} {a n : ℕ} (spine : IndexSpine heap a n)
    (next b c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext root,ext.length=n+5 ∧ NaturalRun program (5*n+8)
      (state heap next a b c d [] source 8) []
      (state (heap++ext) (next+ext.length) a (next+3) (next+2) root [] source 13) ∧
      StoredList (heap++ext) root (List.replicate n BinaryRational.zero) ∧
      Stored (heap++ext) (next+3) BinaryRational.zero := by
  let h1 := heap++[.nil]
  let h2 := h1++[.flag true]
  let h3 := h2++[.pair (next+1) next]
  let h4 := h3++[.pair next (next+2)]
  let e0 : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
  have eh : heap++e0=h4 := by simp [e0,h4,h3,h2,h1,List.append_assoc]
  have nilCell : h4[next]?=some .nil := by simp [h4,h3,h2,h1,hn]
  have flagCell : h4[next+1]?=some (.flag true) := by simp [h4,h3,h2,h1,hn]
  have pairCell : h4[next+2]?=some (.pair (next+1) next) := by simp [h4,h3,h2,h1,hn]
  have record : h4[next+3]?=some (.pair next (next+2)) := by simp [h4,h3,h2,h1,hn]
  have zeroRep : Stored h4 (next+3) BinaryRational.zero :=
    ⟨next,next+2,record,.nil nilCell,.cons pairCell flagCell (.nil nilCell)⟩
  have spine4 : IndexSpine h4 a n := by
    rw [←eh]
    exact indexSpine_extend spine e0
  have dense4 : next+4=h4.length := by simp [h4,h3,h2,h1,hn]
  obtain ⟨er,rr,lr,rowRun,rowRep⟩ := replicate_return spine4 zeroRep (next+4) (next+2) d dense4
    ⟨a,next+3,next+2,d⟩ 13 [] source
  have t8 : tickNatural program (state heap next a b c d [] source 8)=
      some ⟨state h1 (next+1) a next c d [] source 9,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
  have t9 : tickNatural program (state h1 (next+1) a next c d [] source 9)=
      some ⟨state h2 (next+2) a next (next+1) d [] source 10,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h2]
  have t10 : tickNatural program (state h2 (next+2) a next (next+1) d [] source 10)=
      some ⟨state h3 (next+3) a next (next+2) d [] source 11,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h3]
  have t11 : tickNatural program (state h3 (next+3) a next (next+2) d [] source 11)=
      some ⟨state h4 (next+4) a (next+3) (next+2) d [] source 12,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h4]
  have t12 : tickNatural program (state h4 (next+4) a (next+3) (next+2) d [] source 12)=
      some ⟨state h4 (next+4) a (next+3) (next+2) d [⟨13,.r3,⟨a,next+3,next+2,d⟩⟩] source 0,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++er,rr,by simp [e0,lr],?_,?_,?_⟩
  · convert NaturalRun.step t8 (.step t9 (.step t10 (.step t11 (.step t12 rowRun)))) using 1 <;>
      simp [e0,h4,h3,h2,h1,List.append_assoc,Nat.add_assoc,state]
    omega
  · simpa [e0,h4,h3,h2,h1,List.append_assoc] using rowRep
  · simpa [e0,h4,h3,h2,h1,List.append_assoc] using stored_extend zeroRep er
theorem zero_packed {heap : NaturalHeap} {a n : ℕ} (spine : IndexSpine heap a n)
    (next b c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext root zeroRoot loadsRoot,ext.length=n+6 ∧ NaturalRun program (5*n+9)
      (state heap next a b c d [] source 8) []
      (state (heap++ext) (next+ext.length) a zeroRoot (next+2) root [] source 14) ∧
      (heap++ext)[root]?=some (.pair zeroRoot loadsRoot) ∧
      StoredList (heap++ext) loadsRoot (List.replicate n BinaryRational.zero) ∧
      Stored (heap++ext) zeroRoot BinaryRational.zero := by
  obtain ⟨e,r,len,run,rep,z⟩ := zero_high spine next b c d hn source
  let h := heap++e
  let k := next+e.length
  have ht : tickNatural program (state h k a (next+3) (next+2) r [] source 13)=
      some ⟨state (h++[.pair (next+3) r]) (k+1) a (next+3) (next+2) k [] source 14,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  refine ⟨e++[.pair (next+3) r],k,next+3,r,by simp [len],?_,?_,?_,?_⟩
  · convert run_append run (.step ht (.done _)) using 1 <;>
      simp [h,k,List.append_assoc,Nat.add_assoc]
  · simp [k,hn]
  · simpa [List.append_assoc] using list_extend rep [.pair (next+3) r]
  · simpa [List.append_assoc] using stored_extend z [.pair (next+3) r]
end DirectedFlowCutGap.PackingZeroRow
