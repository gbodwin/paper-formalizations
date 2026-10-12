import DirectedFlowCutGap.CanonicalRationalQuotientProgram

namespace DirectedFlowCutGap.CanonicalRationalQuotient
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem test_prefix {word : Bits} {heap : NaturalHeap} {a b bn bd : ℕ}
    (pair : heap[b]?=some (.pair bn bd)) (num : BoolList heap bn word)
    (next c d : ℕ) (hn : next=heap.length)
    (stack : List (Frame ℕ 164)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+5)
      (state heap next a b c d stack source 144) []
      (state (heap++[.pair a b,.flag (BinaryArithmetic.isZero word).1]) (next+2)
        bn b next (next+1) stack source 147) := by
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense : n0=h0.length := by simp [n0,h0,e0,hn]
  have pair0 : h0[b]?=some (.pair bn bd) := lookup_extend pair e0
  have core := zero_return (boolList_extend num e0) n0 b next d dense ⟨bn,b,next,d⟩ 147 stack source
  have t144 : tickNatural program (state heap next a b c d stack source 144)=
      some ⟨state h0 n0 a b next d stack source 145,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0,n0]
  have t145 : tickNatural program (state h0 n0 a b next d stack source 145)=
      some ⟨state h0 n0 bn b next d stack source 146,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
  have t146 : tickNatural program (state h0 n0 bn b next d stack source 146)=
      some ⟨state h0 n0 bn b next d (⟨147,.r3,⟨bn,b,next,d⟩⟩::stack) source 139,[],0⟩ := by
    simp [tickNatural,program,state]
  convert NaturalRun.step t144 (.step t145 (.step t146 core)) using 1 <;>
    simp [n0,e0,List.append_assoc]

theorem zero_finish {heap : NaturalHeap} {a b c d : ℕ}
    (flag : heap[d]?=some (.flag true)) (next : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 164) (stack : List (Frame ℕ 164)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧
      NaturalRun program 6 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 147) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root BinaryRational.zero := by
  let frames : List (Frame ℕ 164) := ⟨pc,.r3,saved⟩::stack
  let h1 := heap++[.nil]
  let h2 := h1++[.flag true]
  let h3 := h2++[.pair (next+1) next]
  let h4 := h3++[.pair next (next+2)]
  have t147 : tickNatural program (state heap next a b c d frames source 147)=
      some ⟨state heap next a b c d frames source 148,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,flag,tagBranch]
  have t148 : tickNatural program (state heap next a b c d frames source 148)=
      some ⟨state h1 (next+1) a b c next frames source 149,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
  have t149 : tickNatural program (state h1 (next+1) a b c next frames source 149)=
      some ⟨state h2 (next+2) a (next+1) c next frames source 150,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h2]
  have t150 : tickNatural program (state h2 (next+2) a (next+1) c next frames source 150)=
      some ⟨state h3 (next+3) a (next+2) c next frames source 151,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h3]
  have t151 : tickNatural program (state h3 (next+3) a (next+2) c next frames source 151)=
      some ⟨state h4 (next+4) a (next+2) c (next+3) frames source 152,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h4]
  have t152 : tickNatural program (state h4 (next+4) a (next+2) c (next+3) frames source 152)=
      some ⟨state h4 (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
  have eh : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,List.append_assoc]
  have nilCell : h4[next]?=some .nil := by simp [h4,h3,h2,h1,hn]
  have flagCell : h4[next+1]?=some (.flag true) := by simp [h4,h3,h2,h1,hn]
  have pairCell : h4[next+2]?=some (.pair (next+1) next) := by simp [h4,h3,h2,h1,hn]
  have record : h4[next+3]?=some (.pair next (next+2)) := by simp [h4,h3,h2,h1,hn]
  refine ⟨ext,next+3,rfl,?_,?_⟩
  · simpa [ext,eh] using NaturalRun.step t147 (.step t148 (.step t149 (.step t150 (.step t151 (.step t152 (.done _))))))
  · rw [eh]
    exact ⟨next,next+2,record,.nil nilCell,.cons pairCell flagCell (.nil nilCell)⟩
end DirectedFlowCutGap.CanonicalRationalQuotient
