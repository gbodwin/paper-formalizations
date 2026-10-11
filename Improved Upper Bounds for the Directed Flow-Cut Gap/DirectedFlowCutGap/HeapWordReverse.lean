import DirectedFlowCutGap.PackedBooleanConstructor

/-! A literal six-slot persistent word reversal. It allocates one new spine
cell per stored bit, retaining the existing flag cells, and makes its own nil
accumulator. This is a pathwise heap operation, not a distributional symmetry. -/
namespace DirectedFlowCutGap.HeapWordReverse
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def program : Program 6 := fun pc => match pc.val with
  | 0 => .make .r1 .nil 1
  | 1 => .branch .r0 5 5 5 2
  | 2 => .field .r2 .r0 false 3
  | 3 => .make .r1 (.pair .r2 .r1) 4
  | 4 => .field .r0 .r0 true 1
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 6)) (source : Bits) (pc : Fin 6) : NaturalState 6 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem loop (word : Bits) {heap : NaturalHeap} {a b : ℕ} {acc : Bits}
    (rep : BoolList heap a word) (accRep : BoolList heap b acc)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 6)) (source : Bits) :
    ∃ out, NaturalRun program (4*word.length+1) (state heap next a b c d stack source 1) [] out ∧
      BoolList out.heap out.registers.b (word.reverse++acc) ∧
      (∃ extra,out.heap=heap++extra ∧ extra.length=word.length) ∧
      out.next=out.heap.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=5 := by
  induction word generalizing heap a b acc next c with
  | nil =>
      cases rep with
      | nil h =>
          refine ⟨state heap next a b c d stack source 5,?_,?_,⟨[],by simp [state],by simp⟩,hn,rfl,rfl,rfl⟩
          · have ht : tickNatural program (state heap next a b c d stack source 1)=
                some ⟨state heap next a b c d stack source 5,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,h,tagBranch]
            simpa using NaturalRun.step ht (NaturalRun.done _)
          · simpa [state] using accRep
  | cons bit bits ih =>
      cases rep with
      | @cons _ flag tail _ _ hp hf hr =>
          let heap' := heap++[Cell.pair flag b]
          have hc : heap'[next]?=some (.pair flag b) := by simp [heap',hn]
          have ap : BoolList heap' next (bit::acc) :=
            .cons hc (lookup_extend hf _) (boolList_extend accRep _)
          have rp : BoolList heap' tail bits := boolList_extend hr _
          have hn' : next+1=heap'.length := by simp [heap',hn]
          obtain ⟨out,run,represented,⟨extra,he,hlen⟩,dense,frames,src,pc⟩ :=
            ih rp ap (next+1) flag hn'
          refine ⟨out,?_,?_,⟨Cell.pair flag b::extra,?_,?_⟩,dense,frames,src,pc⟩
          · have t1 : tickNatural program (state heap next a b c d stack source 1)=
                some ⟨state heap next a b c d stack source 2,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hp,tagBranch]
            have t2 : tickNatural program (state heap next a b c d stack source 2)=
                some ⟨state heap next a b flag d stack source 3,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,hp]
            have t3 : tickNatural program (state heap next a b flag d stack source 3)=
                some ⟨state heap' (next+1) a next flag d stack source 4,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,heap']
            have t4 : tickNatural program (state heap' (next+1) a next flag d stack source 4)=
                some ⟨state heap' (next+1) tail next flag d stack source 1,[],0⟩ := by
              have hp' : heap'[a]?=some (.pair flag tail) := lookup_extend hp [Cell.pair flag b]
              simp [tickNatural,program,state,Registers.get,Registers.set,hp']
            simpa [Nat.mul_add,Nat.add_assoc] using
              NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 (NaturalRun.step t4 run)))
          · simpa [List.reverse_cons,List.append_assoc] using represented
          · simpa [heap',List.append_assoc] using he
          · simp [hlen]

theorem reverse_high {word : Bits} (initial : NaturalState 6) (pc0 : initial.pc=0)
    (hn : initial.next=initial.heap.length)
    (rep : BoolList initial.heap initial.registers.a word) :
    ∃ out, NaturalRun program (4*word.length+2) initial [] out ∧
      BoolList out.heap out.registers.b word.reverse ∧
      (∃ extra,out.heap=initial.heap++extra ∧ extra.length=word.length+1) ∧
      out.next=out.heap.length ∧ out.stack=initial.stack ∧ out.source=initial.source ∧
      out.pc=5 ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at hn pc0 rep
          subst pc
          have nilRep : BoolList (heap++[Cell.nil]) next [] := .nil (by simp [hn])
          have rep' := boolList_extend rep [Cell.nil]
          obtain ⟨out,run,represented,⟨extra,he,hlen⟩,dense,frames,src,pc⟩ :=
            loop word rep' nilRep (next+1) c d (by simp [hn]) stack source
          refine ⟨out,?_,?_,⟨Cell.nil::extra,?_,?_⟩,dense,frames,src,pc,?_⟩
          · have ht : tickNatural program (state heap next a b c d stack source 0)=
                some ⟨state (heap++[Cell.nil]) (next+1) a next c d stack source 1,[],0⟩ := by
              simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
            simpa [state,Nat.add_assoc] using NaturalRun.step ht run
          · simpa using represented
          · simpa [List.append_assoc] using he
          · simp [hlen]
          · simp [tickNatural,pc,program]

/-- Actual lower reversal includes all persistent copies, cursor increments,
and the final halt. The existing flag cells are retained by reference. -/
theorem reverse_bit {word : Bits} {H B : ℕ} (initial : BitState 6)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=0)
    (hn : value initial.next=initial.heap.length)
    (rep : BoolList (eraseState initial).heap (eraseState initial).registers.a word) :
    ∃ charge out, Run program (4*word.length+2) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b word.reverse ∧
      out.source=initial.source ∧ out.pc=5 ∧
      out.heap.length=initial.heap.length+word.length+1 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 6 H B (4*word.length+2) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  obtain ⟨final,high,reversed,⟨extra,ext,len⟩,_,_,src,pc,halt⟩ :=
    reverse_high (eraseState initial) pc0 hn' rep
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact reversed
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).heap.length=(eraseState initial).heap.length+word.length+1 := by
      rw [erase,ext,List.length_append,len]
      omega
    simpa [eraseState,State.map] using h

end DirectedFlowCutGap.HeapWordReverse
