import DirectedFlowCutGap.CounterPrefixProgram
import DirectedFlowCutGap.HeapWordReverse

/-! One fixed30-slot program builds a unary counter, consumes exactly its source
prefix, and performs actual persistent reversal so the stored word has the
literal original request order. No fair-law symmetry is needed for this claim. -/
namespace DirectedFlowCutGap.OrderedCounterPrefix
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def prefixLabel (p : Fin 24) : Fin 30 := ⟨p.val,by omega⟩
def reverseLabel (p : Fin 6) : Fin 30 := ⟨p.val+24,by omega⟩
def program : Program 30 := fun pc =>
  if pc.val=22 then .move .r0 .r0 24
  else if h : pc.val<24 then
    ReferenceProgramLabels.instruction prefixLabel (CounterPrefixProgram.program ⟨pc.val,h⟩)
  else ReferenceProgramLabels.instruction reverseLabel (HeapWordReverse.program ⟨pc.val-24,by omega⟩)

theorem prefix_agree (pc : Fin 24) (h : CounterPrefixProgram.program pc ≠ .halt) :
    program (prefixLabel pc)=ReferenceProgramLabels.instruction prefixLabel (CounterPrefixProgram.program pc) := by
  fin_cases pc <;> simp_all [program,prefixLabel,CounterPrefixProgram.program]
theorem reverse_agree (pc : Fin 6) (h : HeapWordReverse.program pc ≠ .halt) :
    program (reverseLabel pc)=ReferenceProgramLabels.instruction reverseLabel (HeapWordReverse.program pc) := by
  fin_cases pc <;> simp_all [program,reverseLabel]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 30) :
    NaturalState 30 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def steps (word : Bits) : ℕ := CounterPrefixProgram.steps word+4*value word+3

theorem steps_bound (word : Bits) : steps word≤11*value word+10*word.length+10 := by
  have := CounterPrefixProgram.steps_bound word
  simp only [steps]
  omega

theorem run_append {s u v : NaturalState 30} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Request order, stored word and the actual residual source agree pathwise. -/
theorem materialize {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (rep : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (source : Bits) (enough : value word≤source.length) :
    ∃ out, NaturalRun program (steps word) (state heap next a b c d source 23)
        ((source.take (value word)).map Event.request) out ∧
      BoolList out.heap out.registers.b (source.take (value word)) ∧
      out.source=source.drop (value word) ∧ out.pc=29 ∧
      out.heap.length=heap.length+4*value word+3 ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ tickNatural program out=none := by
  obtain ⟨mid,first,stored,src,pc,len,dense,frames,_⟩ :=
    CounterPrefixProgram.materialize rep next b c d hn source enough
  let start : NaturalState 6 := ⟨mid.heap,mid.next,mid.registers,[],0,mid.source⟩
  obtain ⟨last,second,ordered,⟨extra,ext,exlen⟩,hdense,hframes,hsrc,hpc,_⟩ :=
    HeapWordReverse.reverse_high start rfl dense stored
  have first' := ReferenceProgramLabels.run prefixLabel CounterPrefixProgram.program program prefix_agree first
  have second' := ReferenceProgramLabels.run reverseLabel HeapWordReverse.program program reverse_agree second
  have hop : tickNatural program (ReferenceProgramLabels.state prefixLabel mid)=
      some ⟨ReferenceProgramLabels.state reverseLabel start,[],0⟩ := by
    simp [tickNatural,program,ReferenceProgramLabels.state,prefixLabel,pc,frames,start,
      Registers.get,Registers.set,reverseLabel]
  have hlength : ((source.take (value word)).reverse).length=value word := by
    simp [List.length_take,Nat.min_eq_left enough]
  refine ⟨ReferenceProgramLabels.state reverseLabel last,?_,?_,hsrc.trans src,?_,?_,hdense,?_,?_⟩
  · have all := run_append first' (NaturalRun.step hop second')
    convert all using 1 <;> simp [state,CounterPrefixProgram.state,
      ReferenceProgramLabels.state,prefixLabel,steps,hlength]; omega
  · change BoolList last.heap last.registers.b _
    simpa only [List.reverse_reverse] using ordered
  · change reverseLabel last.pc=29
    rw [hpc]
    rfl
  · change last.heap.length=heap.length+4*value word+3
    rw [ext,List.length_append,exlen,hlength]
    change mid.heap.length+_ = _
    omega
  · simp [ReferenceProgramLabels.state,hframes,start]
  · simp [tickNatural,program,ReferenceProgramLabels.state,hpc,reverseLabel,
      HeapWordReverse.program,ReferenceProgramLabels.instruction]

theorem materialize_high {word : Bits} (initial : NaturalState 30)
    (pc0 : initial.pc=23) (hn : initial.next=initial.heap.length)
    (rep : BoolList initial.heap initial.registers.a word) (empty : initial.stack=[])
    (enough : value word≤ initial.source.length) :
    ∃ out, NaturalRun program (steps word) initial
        ((initial.source.take (value word)).map Event.request) out ∧
      BoolList out.heap out.registers.b (initial.source.take (value word)) ∧
      out.source=initial.source.drop (value word) ∧ out.pc=29 ∧
      out.heap.length=initial.heap.length+4*value word+3 ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn rep empty enough
          subst pc
          subst stack
          exact materialize rep next b c d hn source enough

/-- The source-consuming and ordered-storage phases share one lower run and
one terminal-inclusive charge. No independent stream is reconstructed. -/
theorem materialize_bit {word : Bits} {H B : ℕ} (initial : BitState 30)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=23)
    (hn : value initial.next=initial.heap.length)
    (rep : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (empty : initial.stack=[]) (enough : value word≤ initial.source.length) :
    ∃ charge out, Run program (steps word) charge initial
        ((initial.source.take (value word)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b
        (initial.source.take (value word)) ∧
      out.source=initial.source.drop (value word) ∧ out.pc=29 ∧
      out.heap.length=initial.heap.length+4*value word+3 ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 30 H B (steps word) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,stored,src,pc,len,dense,frames,halt⟩ :=
    materialize_high (eraseState initial) pc0 hn' rep empty' enough
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,?_,?_,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact stored
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).heap.length=(eraseState initial).heap.length+4*value word+3 := by
      rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h

end DirectedFlowCutGap.OrderedCounterPrefix
