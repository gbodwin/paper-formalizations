import DirectedFlowCutGap.PackingZeroMaskCall

namespace DirectedFlowCutGap.PackingZeroMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def steps : List (Bits × Bits) → ℕ
  | [] => 3
  | r::rs => BinaryZeroProgram.steps r.1+13+steps rs

def mask (rows : List (Bits × Bits)) : Bits := rows.map fun r => (isZero r.1).1

theorem mask_return {rows : List (Bits × Bits)} {heap : NaturalHeap} {a : ℕ}
    (table : WordPairTableRead.Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 32) (stack : List (Frame ℕ 32)) (source : Bits) :
    ∃ ext root, ext.length=2*rows.length+1 ∧
      NaturalRun program (steps rows)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mask rows) := by
  induction rows generalizing heap a next b c d saved pc stack with
  | nil =>
    cases table with
    | nil hp =>
      refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
      have t10 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t11 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11)=
          some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 12,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t12 : tickNatural program
          (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 12)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact .step t10 (.step t11 (.step t12 (.done _)))
  | cons r rs ih =>
    rcases r with ⟨x,y⟩
    cases table with
    | @cons root item tail num den _ _ _ hp hv hx _ ht =>
      let flag : Cell ℕ := Cell.flag (isZero x).1
      let h0 := heap++[flag]
      have ht0 := BinaryIndexedPairRead.table_extend ht [flag]
      have hn0 : next+1=h0.length := by simp [h0,hn]
      obtain ⟨ext,out,len,run,rep⟩ := ih ht0 (next+1) next a next hn0
        ⟨tail,next,a,next⟩ 22 (⟨pc,.r3,saved⟩::stack)
      let cell := Cell.pair next out
      have head : ((h0++ext)++[cell])[next]?=some flag :=
        lookup_extend (lookup_extend (by simp [h0,hn]) ext) [cell]
      have last : ((h0++ext)++[cell])[next+1+ext.length]?=some cell := by
        rw [hn0]
        simpa only [List.length_append] using
          (show ((h0++ext)++[cell])[(h0++ext).length]?=some cell from by simp)
      have tailRep := boolList_extend rep [cell]
      refine ⟨[flag]++ext++[cell],next+1+ext.length,by simp [len];omega,?_,?_⟩
      · have t10 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10)=
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 14,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hp,tagBranch]
        have t14 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 14)=
            some ⟨state heap next a item c d (⟨pc,.r3,saved⟩::stack) source 15,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hp]
        have t15 : tickNatural program (state heap next a item c d (⟨pc,.r3,saved⟩::stack) source 15)=
            some ⟨state heap next a num c d (⟨pc,.r3,saved⟩::stack) source 16,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hv]
        have t16 : tickNatural program (state heap next a num c d (⟨pc,.r3,saved⟩::stack) source 16)=
            some ⟨state heap next a num a d (⟨pc,.r3,saved⟩::stack) source 17,[],0⟩ := by rfl
        have t17 : tickNatural program (state heap next a num a d (⟨pc,.r3,saved⟩::stack) source 17)=
            some ⟨state heap next num num a d (⟨pc,.r3,saved⟩::stack) source 18,[],0⟩ := by rfl
        have t18 : tickNatural program (state heap next num num a d (⟨pc,.r3,saved⟩::stack) source 18)=
            some ⟨state heap next num num a d
              (⟨19,.r3,⟨num,num,a,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 7,[],0⟩ := by rfl
        have zr := zero_return hx next num a d hn ⟨num,num,a,d⟩ .r3 19
          (⟨pc,.r3,saved⟩::stack) source
        have t19 : tickNatural program (state h0 (next+1) num num a next (⟨pc,.r3,saved⟩::stack) source 19)=
            some ⟨state h0 (next+1) num next a next (⟨pc,.r3,saved⟩::stack) source 20,[],0⟩ := by rfl
        have hp0 := lookup_extend hp [flag]
        have t20 : tickNatural program (state h0 (next+1) num next a next (⟨pc,.r3,saved⟩::stack) source 20)=
            some ⟨state h0 (next+1) tail next a next (⟨pc,.r3,saved⟩::stack) source 21,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,h0] at hp0 ⊢
          simp [hp0]
        have t21 : tickNatural program (state h0 (next+1) tail next a next (⟨pc,.r3,saved⟩::stack) source 21)=
            some ⟨state h0 (next+1) tail next a next
              (⟨22,.r3,⟨tail,next,a,next⟩⟩::⟨pc,.r3,saved⟩::stack) source 10,[],0⟩ := by rfl
        have t22 : tickNatural program
            (state (h0++ext) (next+1+ext.length) tail next a out (⟨pc,.r3,saved⟩::stack) source 22)=
            some ⟨state ((h0++ext)++[cell]) (next+1+ext.length+1) tail next a
              (next+1+ext.length) (⟨pc,.r3,saved⟩::stack) source 23,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,cell]
        have t23 : tickNatural program
            (state ((h0++ext)++[cell]) (next+1+ext.length+1) tail next a
              (next+1+ext.length) (⟨pc,.r3,saved⟩::stack) source 23)=
            some ⟨state ((h0++ext)++[cell]) (next+1+ext.length+1) saved.a saved.b saved.c
              (next+1+ext.length) stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        have rest := run_append run (.step t22 (.step t23 (.done _)))
        have afterZero := NaturalRun.step t19 (.step t20 (.step t21 rest))
        have all := run_append zr afterZero
        have whole := NaturalRun.step t10 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 all)))))
        convert whole using 1 <;> simp [steps,state,h0,flag,List.append_assoc,Nat.add_assoc] <;> omega
      · simpa [mask,h0,flag,List.append_assoc] using BoolList.cons last head tailRep
end DirectedFlowCutGap.PackingZeroMask
