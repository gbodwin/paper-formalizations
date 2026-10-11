import DirectedFlowCutGap.BinaryIndexedPairRead
import DirectedFlowCutGap.HeapPairEmit

/-! The actual binary-index reader and exact two-field emitter are one fixed
36-slot program. The output consists of actual emit instructions for every
stored bit. No natural-indexed output decoder is substituted. -/
namespace DirectedFlowCutGap.IndexedPairEmit
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def readLabel (p : Fin 26) : Fin 36 := ⟨p.val,by omega⟩
def emitLabel (p : Fin 10) : Fin 36 := ⟨p.val+26,by omega⟩

def program : Program 36 := fun pc =>
  if pc.val=24 then .move .r0 .r0 26
  else if h : pc.val<26 then
    ReferenceProgramLabels.instruction readLabel (BinaryIndexedPairRead.program ⟨pc.val,h⟩)
  else ReferenceProgramLabels.instruction emitLabel (HeapPairEmit.program ⟨pc.val-26,by omega⟩)

theorem read_agree (pc : Fin 26) (h : BinaryIndexedPairRead.program pc ≠ .halt) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (BinaryIndexedPairRead.program pc) := by
  fin_cases pc <;> simp_all [program,readLabel,BinaryIndexedPairRead.program]

theorem emit_agree (pc : Fin 10) (h : HeapPairEmit.program pc ≠ .halt) :
    program (emitLabel pc)=ReferenceProgramLabels.instruction emitLabel (HeapPairEmit.program pc) := by
  fin_cases pc <;> simp_all [program,emitLabel]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 36) :
    NaturalState 36 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def steps (word num den : Bits) : ℕ :=
  BinaryIndexedPairRead.steps word+4*(num.length+den.length)+4

theorem emit {heap : NaturalHeap} {a b : ℕ} {word : Bits} {rows : List (Bits × Bits)}
    (wordRep : BoolList heap a word) (table : WordPairTableRead.Table heap b rows)
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ out, NaturalRun program (steps word rows[value word].1 rows[value word].2)
      (state heap next a b c d source 25)
      ((rows[value word].1++rows[value word].2).map Event.emit) out ∧
      (∃ extra,out.heap=heap++extra ∧ extra.length=value word+1) ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=35 ∧
      tickNatural program out=none := by
  obtain ⟨mid,hr,ra,rb,ext,dense,frames,src,pc,_⟩ :=
    BinaryIndexedPairRead.read wordRep table hi next c d hn source
  let start : NaturalState 10 := ⟨mid.heap,mid.next,mid.registers,[],0,mid.source⟩
  obtain ⟨last,he,hheap,hnext,hframes,hsrc,hpc,_⟩ := HeapPairEmit.emit_high start rfl rfl ra rb
  have first := ReferenceProgramLabels.run readLabel BinaryIndexedPairRead.program program read_agree hr
  have second := ReferenceProgramLabels.run emitLabel HeapPairEmit.program program emit_agree he
  have hop : tickNatural program (ReferenceProgramLabels.state readLabel mid)=
      some ⟨ReferenceProgramLabels.state emitLabel start,[],0⟩ := by
    simp [tickNatural,program,ReferenceProgramLabels.state,readLabel,pc,frames,start,
      Registers.get,Registers.set,emitLabel]
  refine ⟨ReferenceProgramLabels.state emitLabel last,?_,?_,?_,?_,?_,?_,?_⟩
  · have all := HeapPairEmit.run_append first (NaturalRun.step hop second)
    convert all using 1 <;> simp [state,BinaryIndexedPairRead.state,
      ReferenceProgramLabels.state,readLabel,steps]; omega
  · change ∃ extra,last.heap=heap++extra ∧ extra.length=value word+1
    rw [hheap]
    exact ext
  · change last.next=last.heap.length
    rw [hnext,hheap]
    exact dense
  · simp [ReferenceProgramLabels.state,hframes]
  · exact hsrc.trans src
  · change emitLabel last.pc=35
    rw [hpc]
    rfl
  · simp [tickNatural,program,ReferenceProgramLabels.state,hpc,emitLabel,
      HeapPairEmit.program,ReferenceProgramLabels.instruction]

theorem emit_high {word : Bits} {rows : List (Bits × Bits)} (initial : NaturalState 36)
    (pc0 : initial.pc=25) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (wordRep : BoolList initial.heap initial.registers.a word)
    (table : WordPairTableRead.Table initial.heap initial.registers.b rows)
    (hi : value word<rows.length) :
    ∃ out, NaturalRun program (steps word rows[value word].1 rows[value word].2) initial
      ((rows[value word].1++rows[value word].2).map Event.emit) out ∧
      (∃ extra,out.heap=initial.heap++extra ∧ extra.length=value word+1) ∧
      out.next=out.heap.length ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=35 ∧
      tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn empty wordRep table
          subst pc
          subst stack
          exact emit wordRep table hi next c d hn source

/-- The one lower run pays every actual index, record and output instruction,
then the one terminal halt, for the exact padded selected fields. -/
theorem emit_bit {word : Bits} {rows : List (Bits × Bits)} {H B : ℕ}
    (initial : BitState 36) (bounded : initial.Bounded H B) (pc0 : initial.pc=25)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (wordRep : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b rows)
    (hi : value word<rows.length) :
    ∃ charge out, Run program (steps word rows[value word].1 rows[value word].2) charge initial
      ((rows[value word].1++rows[value word].2).map Event.emit) out ∧
      (∃ extra,(eraseState out).heap=(eraseState initial).heap++extra ∧ extra.length=value word+1) ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=35 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤
        completeBound 36 H B (steps word rows[value word].1 rows[value word].2) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,ext,dense,frames,src,pc,halt⟩ :=
    emit_high (eraseState initial) pc0 hn' empty' wordRep table hi
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,source.trans src,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact ext
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.IndexedPairEmit
