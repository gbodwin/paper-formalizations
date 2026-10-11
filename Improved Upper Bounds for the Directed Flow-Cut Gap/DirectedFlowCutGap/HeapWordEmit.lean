import DirectedFlowCutGap.PackedBooleanConstructor

/-! A literal five-instruction heap-word emitter. Every stored bit, including
padding, is emitted by an actual instruction; no implicit DAG expansion is an
output operation. The source and heap are unchanged. -/
namespace DirectedFlowCutGap.HeapWordEmit
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def program : Program 5 := fun pc => match pc.val with
  | 0 => .branch .r0 4 4 4 1
  | 1 => .field .r2 .r0 false 2
  | 2 => .emit .r2 3
  | 3 => .field .r0 .r0 true 0
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 5)) (source : Bits) (pc : Fin 5) : NaturalState 5 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- The emitted bits retain exactly the represented word's order and padding. -/
theorem emit {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (rep : BoolList heap a word) (next b c d : ℕ)
    (stack : List (Frame ℕ 5)) (source : Bits) :
    ∃ tail last, NaturalRun program (4*word.length+1)
      (state heap next a b c d stack source 0) (word.map Event.emit)
      (state heap next tail b last d stack source 4) ∧ heap[tail]?=some .nil := by
  induction rep generalizing c with
  | @nil root h =>
      refine ⟨_,c,?_,h⟩
      have step : tickNatural program (state heap next root b c d stack source 0)=
          some ⟨state heap next root b c d stack source 4,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,h,tagBranch]
      simpa using NaturalRun.step step (NaturalRun.done _)
  | @cons root flag tail bit bits hp hf hr ih =>
      obtain ⟨endroot,last,run,hend⟩ := ih flag
      refine ⟨endroot,last,?_,hend⟩
      have t0 : tickNatural program (state heap next root b c d stack source 0)=
          some ⟨state heap next root b c d stack source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t1 : tickNatural program (state heap next root b c d stack source 1)=
          some ⟨state heap next root b flag d stack source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t2 : tickNatural program (state heap next root b flag d stack source 2)=
          some ⟨state heap next root b flag d stack source 3,[Event.emit bit],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hf]
      have t3 : tickNatural program (state heap next root b flag d stack source 3)=
          some ⟨state heap next tail b flag d stack source 0,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      simpa [Nat.mul_add,Nat.add_assoc] using
        NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 run)))

theorem emit_high {word : Bits} (initial : NaturalState 5) (pc0 : initial.pc=0)
    (rep : BoolList initial.heap initial.registers.a word) :
    ∃ out, NaturalRun program (4*word.length+1) initial (word.map Event.emit) out ∧
      out.heap=initial.heap ∧ out.next=initial.next ∧ out.stack=initial.stack ∧
      out.registers.b=initial.registers.b ∧ out.registers.d=initial.registers.d ∧
      out.source=initial.source ∧ out.pc=4 ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 rep
          subst pc
          obtain ⟨tail,last,run,_⟩ := emit rep next b c d stack source
          exact ⟨state heap next tail b last d stack source 4,run,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The exact emitted sequence and final halt are paid by the lower interpreter.
Only the erased heap equality is claimed; references may be copied as bits. -/
theorem emit_bit {word : Bits} {H B : ℕ} (initial : BitState 5)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=0)
    (rep : BoolList (eraseState initial).heap (eraseState initial).registers.a word) :
    ∃ charge out, Run program (4*word.length+1) charge initial (word.map Event.emit) out ∧
      (eraseState out).heap=(eraseState initial).heap ∧
      out.source=initial.source ∧ out.pc=4 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 5 H B (4*word.length+1) := by
  obtain ⟨final,high,heap,_,_,_,_,src,pc,halt⟩ := emit_high (eraseState initial) pc0 rep
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact heap
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.HeapWordEmit
