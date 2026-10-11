import DirectedFlowCutGap.BinaryCounterProgram
import DirectedFlowCutGap.WordPairTableRead
import DirectedFlowCutGap.ReferenceProgramLabels

/-! One actual program constructs a unary index from its stored binary word,
then reads the selected two-word record in the same appended heap. Neither an
index spine nor a caller frame is supplied. Row/input-word representations and
whole graph substitution remain separate. -/
namespace DirectedFlowCutGap.BinaryIndexedPairRead
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

theorem table_extend {heap : NaturalHeap} {root : ℕ} {rows : List (Bits × Bits)}
    (h : WordPairTableRead.Table heap root rows) (extra : NaturalHeap) :
    WordPairTableRead.Table (heap++extra) root rows := by
  induction h with
  | nil h => exact .nil (lookup_extend h extra)
  | cons h hp hn hd _ ih =>
      exact .cons (lookup_extend h extra) (lookup_extend hp extra)
        (boolList_extend hn extra) (boolList_extend hd extra) ih

def counterLabel (p : Fin 17) : Fin 26 := ⟨p.val,by omega⟩
def readerLabel (p : Fin 7) : Fin 26 := ⟨p.val+18,by omega⟩

def program : Program 26 := fun pc => match pc.val with
  | 0 => .branch .r0 1 16 16 2
  | 1 => .make .r3 .nil 15
  | 2 => .field .r2 .r0 false 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .call 0 5 .r3
  | 5 => .move .r0 .r3 6
  | 6 => .move .r1 .r3 7
  | 7 => .branch .r0 10 16 16 8
  | 8 => .make .r1 (.pair .r2 .r1) 9
  | 9 => .field .r0 .r0 true 7
  | 10 => .branch .r2 16 13 11 16
  | 11 => .make .r1 (.pair .r2 .r1) 13
  | 13 => .move .r3 .r1 15
  | 15 => .ret .r3
  | 16 => .move .r0 .r1 17
  | 17 => .move .r1 .r3 18
  | 18 => .branch .r1 21 24 24 19
  | 19 => .field .r0 .r0 true 20
  | 20 => .field .r1 .r1 true 18
  | 21 => .field .r2 .r0 false 22
  | 22 => .field .r0 .r2 false 23
  | 23 => .field .r1 .r2 true 24
  | 25 => .call 0 16 .r3
  | _ => .halt

theorem counter_agree (pc : Fin 17) (h : BinaryCounterProgram.program pc ≠ .halt) :
    program (counterLabel pc) =
      ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  fin_cases pc <;> simp_all [program,counterLabel,BinaryCounterProgram.program,
    ReferenceProgramLabels.instruction]

theorem reader_agree (pc : Fin 7) (h : WordPairTableRead.program pc ≠ .halt) :
    program (readerLabel pc) =
      ReferenceProgramLabels.instruction readerLabel (WordPairTableRead.program pc) := by
  fin_cases pc <;> simp_all [program,readerLabel,WordPairTableRead.program,
    ReferenceProgramLabels.instruction]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 26) :
    NaturalState 26 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def steps (word : Bits) : ℕ := BinaryCounterProgram.steps word+3*value word+7

theorem steps_bound (word : Bits) : steps word ≤ 6*value word+10*word.length+10 := by
  have := BinaryCounterProgram.steps_bound word
  simp only [steps]
  omega

theorem run_append {s u v : NaturalState 26} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The same counter-extended heap supplies both selected stored word roots.
The incoming binary word may contain arbitrary padding. -/
theorem read {heap : NaturalHeap} {a b : ℕ} {word : Bits} {rows : List (Bits × Bits)}
    (wordRep : BoolList heap a word) (table : WordPairTableRead.Table heap b rows)
    (hi : value word < rows.length) (next c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ final, NaturalRun program (steps word) (state heap next a b c d source 25) [] final ∧
      BoolList final.heap final.registers.a rows[value word].1 ∧
      BoolList final.heap final.registers.b rows[value word].2 ∧
      (∃ extra,final.heap=heap++extra ∧ extra.length=value word+1) ∧
      final.next=final.heap.length ∧ final.stack=[] ∧
      final.source=source ∧ final.pc=24 ∧ tickNatural program final=none := by
  obtain ⟨ext,root,hlen,hcounter,counter⟩ := BinaryCounterProgram.convert_return
    wordRep next b c d hn ⟨a,b,c,d⟩ 16 [] source
  have hc := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program
    counter_agree hcounter
  let heap' := heap++ext
  let next' := next+BinaryCounterProgram.cells word
  have hn' : next'=heap'.length := by simp [heap',next',hn,hlen]
  have call : tickNatural program (state heap next a b c d source 25) =
      some ⟨ReferenceProgramLabels.state counterLabel
        (BinaryCounterProgram.state heap next a b c d [⟨16,.r3,⟨a,b,c,d⟩⟩] source 0),[],0⟩ := by
    simp [tickNatural,program,state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,BinaryCounterProgram.state,counterLabel]
  have called : NaturalRun program (BinaryCounterProgram.steps word+1)
      (state heap next a b c d source 25) [] (state heap' next' a b c root source 16) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      BinaryCounterProgram.state,counterLabel,state,heap',next'] using NaturalRun.step call hc
  obtain ⟨num,den,item,hread,ra,rb⟩ :=
    WordPairTableRead.read (table_extend table ext) counter hi next' c root [] source
  have hr := ReferenceProgramLabels.run readerLabel WordPairTableRead.program program reader_agree hread
  have t16 : tickNatural program (state heap' next' a b c root source 16) =
      some ⟨state heap' next' b b c root source 17,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t17 : tickNatural program (state heap' next' b b c root source 17) =
      some ⟨ReferenceProgramLabels.state readerLabel
        (WordPairTableRead.state heap' next' b root c root [] source 0),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,
      ReferenceProgramLabels.state,WordPairTableRead.state,readerLabel]
  refine ⟨state heap' next' num den item root source 24,?_,ra,rb,?_,hn',rfl,rfl,rfl,rfl⟩
  · have joined := run_append called (NaturalRun.step t16 (NaturalRun.step t17 hr))
    have hs : BinaryCounterProgram.steps word+1+(3*value word+4+1+1)=steps word := by
      simp only [steps]
      omega
    simpa [hs,ReferenceProgramLabels.state,WordPairTableRead.state,readerLabel,state,heap'] using joined
  · exact ⟨ext,rfl,hlen.trans (BinaryCounterProgram.cells_eq_value word)⟩


theorem read_high {word : Bits} {rows : List (Bits × Bits)} (initial : NaturalState 26)
    (pc0 : initial.pc=25) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (wordRep : BoolList initial.heap initial.registers.a word)
    (table : WordPairTableRead.Table initial.heap initial.registers.b rows)
    (hi : value word < rows.length) :
    ∃ final, NaturalRun program (steps word) initial [] final ∧
      BoolList final.heap final.registers.a rows[value word].1 ∧
      BoolList final.heap final.registers.b rows[value word].2 ∧
      (∃ extra,final.heap=initial.heap++extra ∧ extra.length=value word+1) ∧
      final.next=final.heap.length ∧ final.stack=[] ∧
      final.source=initial.source ∧ final.pc=24 ∧ tickNatural program final=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn empty wordRep table
          subst pc
          subst stack
          exact read wordRep table hi next c d hn source

/-- One lower instruction run pays the binary-index construction and actual
record read together. The selected stored fields remain represented in its
own final heap; no ideal callback or fixed7charge is substituted. -/
theorem read_bit {word : Bits} {rows : List (Bits × Bits)} {H B : ℕ}
    (initial : BitState 26) (bounded : initial.Bounded H B) (pc0 : initial.pc=25)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (wordRep : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b rows)
    (hi : value word < rows.length) :
    ∃ charge out, Run program (steps word) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a rows[value word].1 ∧
      BoolList (eraseState out).heap (eraseState out).registers.b rows[value word].2 ∧
      (∃ extra,(eraseState out).heap=(eraseState initial).heap++extra ∧ extra.length=value word+1) ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=24 ∧
      steps word ≤ 6*value word+10*word.length+10 ∧
      out.Bounded (H+steps word) (B+steps word) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 26 H B (steps word) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,ra,rb,ext,dense,frames,src,pc,halt⟩ :=
    read_high (eraseState initial) pc0 hn' empty' wordRep table hi
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,?_,?_,source.trans src,?_,steps_bound word,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact ra
  · rw [erase]; exact rb
  · rw [erase]; exact ext
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase]; exact dense
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack=[] := by rw [erase]; exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.BinaryIndexedPairRead
