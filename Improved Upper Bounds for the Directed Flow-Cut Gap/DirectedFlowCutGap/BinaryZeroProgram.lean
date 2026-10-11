import DirectedFlowCutGap.PackedBooleanConstructor

/-! A literal padded-word zero test. The real loop follows stored pair/flag
cells, short-circuits at a true bit, and allocates its returned Boolean flag.
The saved caller, original heap and unused source remain part of the run. -/
namespace DirectedFlowCutGap.BinaryZeroProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def program : Program 9 := fun pc => match pc.val with
  | 0 => .branch .r0 4 8 8 1
  | 1 => .field .r2 .r0 false 2
  | 2 => .branch .r2 8 3 5 8
  | 3 => .field .r0 .r0 true 0
  | 4 => .make .r3 (.flag true) 6
  | 5 => .make .r3 (.flag false) 6
  | 6 => .ret .r3
  | 7 => .call 0 8 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 9)) (source : Bits) (pc : Fin 9) : NaturalState 9 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def steps : Bits → ℕ
  | [] => 3
  | false::xs => 4+steps xs
  | true::_ => 5

theorem steps_bound (word : Bits) : steps word ≤ 4*word.length+3 := by
  induction word with
  | nil => simp [steps]
  | cons b bs ih => cases b <;> simp_all [steps] <;> omega

/-- No pure zero-test result is supplied: the actual instructions determine
and return precisely the Boolean result of the existing bit algorithm. -/
theorem zero_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (_hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 9) (stack : List (Frame ℕ 9)) (source : Bits) :
    NaturalRun program (steps word)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++[.flag (isZero word).1]) (next+1)
        saved.a saved.b saved.c next stack source pc) := by
  induction word generalizing a b c d with
  | nil =>
    cases input with
    | nil hnil =>
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 4,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
      have t4 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 4)=
          some ⟨state (heap++[.flag true]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 6,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t6 : tickNatural program (state (heap++[.flag true]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 6)=
          some ⟨state (heap++[.flag true]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact NaturalRun.step t0 (NaturalRun.step t4 (NaturalRun.step t6 (NaturalRun.done _)))
  | cons bit word ih =>
    cases input with
    | @cons a head tail bit word hp hf ht =>
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
          some ⟨state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      cases bit with
      | false =>
        have t2 : tickNatural program (state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 2)=
            some ⟨state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 3,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hf,tagBranch]
        have t3 : tickNatural program (state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 3)=
            some ⟨state heap next tail b head d (⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hp]
        convert NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 (ih ht b head d)))) using 1 <;> simp [steps,isZero]
        omega
      | true =>
        have t2 : tickNatural program (state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 2)=
            some ⟨state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 5,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hf,tagBranch]
        have t5 : tickNatural program (state heap next a b head d (⟨pc,.r3,saved⟩::stack) source 5)=
            some ⟨state (heap++[.flag false]) (next+1) a b head next (⟨pc,.r3,saved⟩::stack) source 6,[],0⟩ := by
          simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
        have t6 : tickNatural program (state (heap++[.flag false]) (next+1) a b head next (⟨pc,.r3,saved⟩::stack) source 6)=
            some ⟨state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        exact NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2
          (NaturalRun.step t5 (NaturalRun.step t6 (NaturalRun.done _)))))

theorem zero_high {word : Bits} (initial : NaturalState 9)
    (pc0 : initial.pc=7) (hn : initial.next=initial.heap.length)
    (input : BoolList initial.heap initial.registers.a word) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (1+steps word) initial [] out ∧
      out.heap=initial.heap++[.flag (isZero word).1] ∧
      out.next=initial.next+1 ∧ out.registers.a=initial.registers.a ∧
      out.registers.b=initial.registers.b ∧ out.registers.c=initial.registers.c ∧
      out.registers.d=initial.next ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=8 ∧
      out.heap[out.registers.d]?=some (.flag (isZero word).1) ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc; subst stack
      have t7 : tickNatural program (state heap next a b c d [] source 7)=
          some ⟨state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      refine ⟨state (heap++[.flag (isZero word).1]) (next+1) a b c next [] source 8,
        ?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl⟩
      · simpa [state,Nat.add_comm] using NaturalRun.step t7 (zero_return input next b c d hn ⟨a,b,c,d⟩ 8 [] source)
      · simp [state,hn]

/-- Every lower interpreter operation, including the final halt, is charged.
The returned semantic flag is tied to the same retained padded input. -/
theorem zero_bit {word : Bits} {H B : ℕ} (initial : BitState 9)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=7)
    (hn : value initial.next=initial.heap.length)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+steps word) charge initial [] out ∧
      (eraseState out).heap=(eraseState initial).heap++[.flag (isZero word).1] ∧
      BoolList (eraseState out).heap (eraseState out).registers.a word ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (isZero word).1) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=8 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 9 H B (1+steps word) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,heap,next,a,b,c,d,frames,source,pc,flag,halt⟩ := zero_high (eraseState initial) pc0 hn' input empty'
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,src.trans source,?_,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact heap
  · rw [erase,heap,a];exact boolList_extend input _
  · rw [erase];exact flag
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.BinaryZeroProgram
