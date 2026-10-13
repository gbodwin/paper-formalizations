import DirectedFlowCutGap.ActualPackingRun
import DirectedFlowCutGap.BinaryLengthProgram

namespace DirectedFlowCutGap.PackingDimension
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open BinaryLengthProgram
open CanonicalRationalSum (StoredList list_extend)

/-! The actual length table only follows list tails; its head cells may contain
original rational records rather than Boolean flags. No copy is required. -/
theorem scan_rows {word : List Fraction} {acc : Bits} {heap : NaturalHeap} {a b : ℕ}
    (input : StoredList heap a word) (counter : BoolList heap b acc)
    (next c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ out, NaturalRun program (scanSteps word.length acc)
        (state heap next a b c d source 17) [] out ∧
      BoolList out.heap out.registers.b (countWord word.length acc) ∧
      (∃ ext, out.heap=heap++ext ∧ ext.length=scanCells word.length acc) ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=22 ∧
      tickNatural program out=none := by
  induction word generalizing acc heap a b next c d with
  | nil =>
      cases input with
      | nil hnil =>
          refine ⟨state heap next a b c d source 22,?_,counter,⟨[],by simp [state],rfl⟩,hn,rfl,rfl,rfl,?_⟩
          · have h : tickNatural program (state heap next a b c d source 17)=
                some ⟨state heap next a b c d source 22,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
            exact NaturalRun.step h (NaturalRun.done _)
          · rfl
  | cons bit word ih =>
      cases input with
      | @cons a head tail bit word hp hf ht =>
          obtain ⟨ext,root,exlen,inc,rep⟩ :=
            BinaryIncrementProgram.increment_return counter next b tail d hn
              ⟨b,b,tail,d⟩ 14 [] source
          have inc' := ReferenceProgramLabels.run label BinaryIncrementProgram.program program agree inc
          have t17 : tickNatural program (state heap next a b c d source 17)=
              some ⟨state heap next a b c d source 18,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t18 : tickNatural program (state heap next a b c d source 18)=
              some ⟨state heap next a b tail d source 19,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          have t19 : tickNatural program (state heap next a b tail d source 19)=
              some ⟨state heap next b b tail d source 20,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          have t20 : tickNatural program (state heap next b b tail d source 20)=
              some ⟨ReferenceProgramLabels.state label
                (BinaryIncrementProgram.state heap next b b tail d [⟨14,.r3,⟨b,b,tail,d⟩⟩] source 0),[],0⟩ := by
            simp [tickNatural,program,state,ReferenceProgramLabels.state,
              ReferenceProgramLabels.frame,label,BinaryIncrementProgram.state]
          have t14 : tickNatural program (ReferenceProgramLabels.state label
                (BinaryIncrementProgram.state (heap++ext) (next+BinaryIncrementProgram.cells acc)
                  b b tail root [] source 14))=
              some ⟨state (heap++ext) (next+BinaryIncrementProgram.cells acc) b root tail root source 21,[],0⟩ := by
            simp [tickNatural,program,state,ReferenceProgramLabels.state,label,
              BinaryIncrementProgram.state,Registers.get,Registers.set]
          have t21 : tickNatural program
              (state (heap++ext) (next+BinaryIncrementProgram.cells acc) b root tail root source 21)=
              some ⟨state (heap++ext) (next+BinaryIncrementProgram.cells acc) tail root tail root source 17,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          have hn' : next+BinaryIncrementProgram.cells acc=(heap++ext).length := by simp [hn,exlen]
          obtain ⟨out,rest,stored,⟨more,hout,mlen⟩,dense,frames,src,pc,halt⟩ :=
            ih (list_extend ht ext) rep (next+BinaryIncrementProgram.cells acc) tail root hn'
          refine ⟨out,?_,stored,⟨ext++more,?_,?_⟩,dense,frames,src,pc,halt⟩
          · have endRun := NaturalRun.step t14 (NaturalRun.step t21 rest)
            have body := run_append inc' endRun
            convert NaturalRun.step t17 (NaturalRun.step t18 (NaturalRun.step t19 (NaturalRun.step t20 body))) using 1 <;> simp [scanSteps,List.length_cons]
            omega
          · simpa [List.append_assoc] using hout
          · simp [scanCells,List.length_cons,exlen,mlen]

/-- Self-contained initialization allocates its own empty counter, then visits
all stored cells. No caller, supplied counter or value oracle is assumed. -/
theorem count_rows {word : List Fraction} (initial : NaturalState 24)
    (pc0 : initial.pc=16) (hn : initial.next=initial.heap.length)
    (input : StoredList initial.heap initial.registers.a word) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (1+scanSteps word.length []) initial [] out ∧
      BoolList out.heap out.registers.b (countWord word.length []) ∧
      value (countWord word.length [])=word.length ∧
      StoredList out.heap initial.registers.a word ∧
      (∃ ext, out.heap=initial.heap++ext ∧ ext.length=1+scanCells word.length []) ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=22 ∧
      tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at hn pc0 input empty
          subst pc
          subst stack
          have init : tickNatural program (state heap next a b c d source 16)=
              some ⟨state (heap++[.nil]) (next+1) a next c d source 17,[],0⟩ := by
            simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
          have counter : BoolList (heap++[.nil]) next [] := by
            apply BoolList.nil
            rw [List.getElem?_append_right (by omega)]
            simp [hn]
          have hn' : next+1=(heap++[Cell.nil]).length := by simp [hn]
          obtain ⟨out,run,stored,⟨more,ext,len⟩,dense,frames,src,pc,halt⟩ :=
            scan_rows (list_extend input [.nil]) counter (next+1) c d hn' source
          refine ⟨out,?_,stored,?_,?_,⟨[.nil]++more,?_,?_⟩,
            dense,frames,src,pc,halt⟩
          · simpa [state,Nat.add_comm] using NaturalRun.step init run
          · simpa [value] using (countWord_spec word.length []).1
          · rw [ext]
            exact list_extend (list_extend input [.nil]) more
          · simpa [List.append_assoc] using ext
          · simp [len,Nat.add_comm]


end DirectedFlowCutGap.PackingDimension
