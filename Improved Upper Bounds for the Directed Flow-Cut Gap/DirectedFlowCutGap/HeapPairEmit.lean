import DirectedFlowCutGap.HeapWordEmit
import DirectedFlowCutGap.ReferenceProgramLabels

/-! One actual ten-slot program emits both represented fields, retaining all
padding and exact numerator-then-denominator order. Their boundary remains
specified by the two input words; no self-delimiting coding claim is made. -/
namespace DirectedFlowCutGap.HeapPairEmit
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def firstLabel (p : Fin 5) : Fin 10 := ⟨p.val,by omega⟩
def secondLabel (p : Fin 5) : Fin 10 := ⟨p.val+5,by omega⟩
def program : Program 10 := fun pc => match pc.val with
  | 0 => .branch .r0 4 4 4 1
  | 1 => .field .r2 .r0 false 2
  | 2 => .emit .r2 3
  | 3 => .field .r0 .r0 true 0
  | 4 => .move .r0 .r1 5
  | 5 => .branch .r0 9 9 9 6
  | 6 => .field .r2 .r0 false 7
  | 7 => .emit .r2 8
  | 8 => .field .r0 .r0 true 5
  | _ => .halt

theorem first_agree (pc : Fin 5) (h : HeapWordEmit.program pc ≠ .halt) :
    program (firstLabel pc)=ReferenceProgramLabels.instruction firstLabel (HeapWordEmit.program pc) := by
  fin_cases pc <;> simp_all [program,firstLabel,HeapWordEmit.program,ReferenceProgramLabels.instruction]
theorem second_agree (pc : Fin 5) (h : HeapWordEmit.program pc ≠ .halt) :
    program (secondLabel pc)=ReferenceProgramLabels.instruction secondLabel (HeapWordEmit.program pc) := by
  fin_cases pc <;> simp_all [program,secondLabel,HeapWordEmit.program,ReferenceProgramLabels.instruction]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 10) :
    NaturalState 10 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

theorem run_append {C : ℕ} {p : Program C} {s u v : NaturalState C}
    {t k : ℕ} {events more : List Event}
    (h : NaturalRun p t s events u) (g : NaturalRun p k u more v) :
    NaturalRun p (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem emit {heap : NaturalHeap} {a b : ℕ} {num den : Bits}
    (hn : BoolList heap a num) (hd : BoolList heap b den)
    (next c d : ℕ) (source : Bits) :
    ∃ tail last, NaturalRun program (4*(num.length+den.length)+3)
      (state heap next a b c d source 0) ((num++den).map Event.emit)
      (state heap next tail b last d source 9) := by
  obtain ⟨tail1,last1,first,_⟩ := HeapWordEmit.emit hn next b c d [] source
  obtain ⟨tail2,last2,second,_⟩ := HeapWordEmit.emit hd next b last1 d [] source
  have hfirst := ReferenceProgramLabels.run firstLabel HeapWordEmit.program program first_agree first
  have hsecond := ReferenceProgramLabels.run secondLabel HeapWordEmit.program program second_agree second
  have mid : tickNatural program (state heap next tail1 b last1 d source 4)=
      some ⟨state heap next b b last1 d source 5,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have one : NaturalRun program (4*num.length+1) (state heap next a b c d source 0)
      (num.map Event.emit) (state heap next tail1 b last1 d source 4) := by
    simpa [ReferenceProgramLabels.state,HeapWordEmit.state,firstLabel,state] using hfirst
  have two : NaturalRun program (4*den.length+1) (state heap next b b last1 d source 5)
      (den.map Event.emit) (state heap next tail2 b last2 d source 9) := by
    simpa [ReferenceProgramLabels.state,HeapWordEmit.state,secondLabel,state] using hsecond
  refine ⟨tail2,last2,?_⟩
  have all := run_append one (NaturalRun.step mid two)
  convert all using 1 <;> first | omega | simp [List.map_append]

theorem emit_high {num den : Bits} (initial : NaturalState 10)
    (pc0 : initial.pc=0) (empty : initial.stack=[])
    (hn : BoolList initial.heap initial.registers.a num)
    (hd : BoolList initial.heap initial.registers.b den) :
    ∃ out, NaturalRun program (4*(num.length+den.length)+3) initial
        ((num++den).map Event.emit) out ∧
      out.heap=initial.heap ∧ out.next=initial.next ∧ out.stack=[] ∧
      out.source=initial.source ∧ out.pc=9 ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 empty hn hd
          subst pc
          subst stack
          obtain ⟨tail,last,run⟩ := emit hn hd next c d source
          exact ⟨state heap next tail b last d source 9,run,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem emit_bit {num den : Bits} {H B : ℕ} (initial : BitState 10)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=0) (empty : initial.stack=[])
    (hn : BoolList (eraseState initial).heap (eraseState initial).registers.a num)
    (hd : BoolList (eraseState initial).heap (eraseState initial).registers.b den) :
    ∃ charge out, Run program (4*(num.length+den.length)+3) charge initial
        ((num++den).map Event.emit) out ∧
      (eraseState out).heap=(eraseState initial).heap ∧
      out.source=initial.source ∧ out.pc=9 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 10 H B (4*(num.length+den.length)+3) := by
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,heap,_,_,src,pc,halt⟩ := emit_high (eraseState initial) pc0 empty' hn hd
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

end DirectedFlowCutGap.HeapPairEmit
