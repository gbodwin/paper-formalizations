import DirectedFlowCutGap.BinaryCounterProgram
import DirectedFlowCutGap.ReferencePrefixMaterialization
import DirectedFlowCutGap.ReferenceProgramLabels

/-! One fixed 24-slot program first calls the actual binary-to-unary counter
routine, then allocates an empty accumulator and materializes that many source
bits. Both phases use one heap, one source and real caller frames. -/
namespace DirectedFlowCutGap.CounterPrefixProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def counterLabel (p : Fin 17) : Fin 24 := ⟨p.val,by omega⟩
def prefixLabel (p : Fin 5) : Fin 24 := ⟨p.val+18,by omega⟩

def program : Program 24 := fun pc => match pc.val with
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
  | 16 => .move .r1 .r3 17
  | 17 => .make .r0 .nil 18
  | 18 => .branch .r1 22 22 22 19
  | 19 => .request .r2 20
  | 20 => .make .r0 (.pair .r2 .r0) 21
  | 21 => .field .r1 .r1 true 18
  | 23 => .call 0 16 .r3
  | _ => .halt

theorem counter_agree (pc : Fin 17) (h : BinaryCounterProgram.program pc ≠ .halt) :
    program (counterLabel pc) =
      ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  fin_cases pc <;> simp_all [program,counterLabel,BinaryCounterProgram.program,
    ReferenceProgramLabels.instruction]

theorem prefix_agree (pc : Fin 5) (h : ReferencePrefixMaterialization.program pc ≠ .halt) :
    program (prefixLabel pc) =
      ReferenceProgramLabels.instruction prefixLabel (ReferencePrefixMaterialization.program pc) := by
  fin_cases pc <;> simp_all [program,prefixLabel,ReferencePrefixMaterialization.program,
    ReferenceProgramLabels.instruction]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 24) :
    NaturalState 24 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def steps (word : Bits) : ℕ := BinaryCounterProgram.steps word + 4*value word+4

theorem steps_bound (word : Bits) : steps word ≤ 7*value word+10*word.length+7 := by
  have := BinaryCounterProgram.steps_bound word
  simp only [steps]
  omega

theorem run_append {s u v : NaturalState 24} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- No represented unary counter or caller frame is supplied: the program
constructs both before reading the original source. -/
theorem materialize {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (table : BoolList heap a word) (next b c d : ℕ) (hn : next = heap.length)
    (source : Bits) (enough : value word ≤ source.length) :
    ∃ final, NaturalRun program (steps word) (state heap next a b c d source 23)
        ((source.take (value word)).map Event.request) final ∧
      BoolList final.heap final.registers.a (source.take (value word)).reverse ∧
      final.source = source.drop (value word) ∧ final.pc = 22 ∧
      final.heap.length = heap.length+3*value word+2 ∧
      final.next = final.heap.length ∧ final.stack = [] ∧ tickNatural program final = none := by
  obtain ⟨ext,root,hlen,hcounter,counter⟩ := BinaryCounterProgram.convert_return
    table next b c d hn ⟨a,b,c,d⟩ 16 [] source
  have hc := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program
    counter_agree hcounter
  let heap' := heap++ext
  let next' := next+BinaryCounterProgram.cells word
  have hn' : next' = heap'.length := by simp [heap',next',hn,hlen]
  have call : tickNatural program (state heap next a b c d source 23) =
      some ⟨ReferenceProgramLabels.state counterLabel
        (BinaryCounterProgram.state heap next a b c d [⟨16,.r3,⟨a,b,c,d⟩⟩] source 0),[],0⟩ := by
    simp [tickNatural,program,state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,BinaryCounterProgram.state,counterLabel]
  have called : NaturalRun program (BinaryCounterProgram.steps word+1)
      (state heap next a b c d source 23) [] (state heap' next' a b c root source 16) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      BinaryCounterProgram.state,counterLabel,state,heap',next'] using NaturalRun.step call hc
  let heap'' := heap'++[Cell.nil]
  have acc : BoolList heap'' next' [] := .nil (by simp [heap'',hn'])
  have count : IndexSpine heap'' root (value word) := indexSpine_extend counter [Cell.nil]
  have hn'' : next'+1 = heap''.length := by simp [heap'',hn']
  obtain ⟨out,hprefix,rep,src,pc,len,dense,frames,_⟩ :=
    ReferencePrefixMaterialization.materialize acc count (next'+1) c root hn'' [] source enough
  have hp := ReferenceProgramLabels.run prefixLabel ReferencePrefixMaterialization.program program
    prefix_agree hprefix
  have t16 : tickNatural program (state heap' next' a b c root source 16) =
      some ⟨state heap' next' a root c root source 17,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t17 : tickNatural program (state heap' next' a root c root source 17) =
      some ⟨ReferenceProgramLabels.state prefixLabel
        (ReferencePrefixMaterialization.state heap'' (next'+1) next' root c root [] source 0),[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,
      ReferenceProgramLabels.state,ReferencePrefixMaterialization.state,prefixLabel,heap'']
  let final := ReferenceProgramLabels.state prefixLabel out
  refine ⟨final,?_,?_,src,?_,?_,?_,?_,?_⟩
  · have joined := run_append called (NaturalRun.step t16 (NaturalRun.step t17 hp))
    convert joined using 1
    · simp only [steps]
      omega
    · simp
  · simpa [final,ReferenceProgramLabels.state] using rep
  · simp [final,ReferenceProgramLabels.state,pc,prefixLabel]
  · simp only [heap'',heap',List.length_append,List.length_cons,List.length_nil,hlen,
      BinaryCounterProgram.cells_eq_value] at len
    change out.heap.length = heap.length+3*value word+2
    omega
  · change out.next = out.heap.length
    rw [dense,len]
    omega
  · simp [final,ReferenceProgramLabels.state,frames]
  · simp [tickNatural,program,final,ReferenceProgramLabels.state,pc,prefixLabel]


theorem materialize_high {word : Bits} (initial : NaturalState 24)
    (pc0 : initial.pc = 23) (hn : initial.next = initial.heap.length)
    (table : BoolList initial.heap initial.registers.a word)
    (empty : initial.stack = []) (enough : value word ≤ initial.source.length) :
    ∃ final, NaturalRun program (steps word) initial
        ((initial.source.take (value word)).map Event.request) final ∧
      BoolList final.heap final.registers.a (initial.source.take (value word)).reverse ∧
      final.source = initial.source.drop (value word) ∧ final.pc = 22 ∧
      final.heap.length = initial.heap.length+3*value word+2 ∧
      final.next = final.heap.length ∧ final.stack = [] ∧ tickNatural program final = none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn table empty enough
          subst pc
          subst stack
          exact materialize table next b c d hn source enough

/-- The same fixed instruction program performs both phases in the lower
interpreter. All source reads, heap copies, real frames and the final halt are
charged together. The only supplied representation is the incoming binary word. -/
theorem materialize_bit {word : Bits} {H B : ℕ} (initial : BitState 24)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 23)
    (hn : value initial.next = initial.heap.length)
    (table : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (empty : initial.stack = []) (enough : value word ≤ initial.source.length) :
    ∃ charge out, Run program (steps word) charge initial
        ((initial.source.take (value word)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a
        (initial.source.take (value word)).reverse ∧
      out.source = initial.source.drop (value word) ∧ out.pc = 22 ∧
      out.heap.length = initial.heap.length+3*value word+2 ∧
      value out.next = out.heap.length ∧ out.stack = [] ∧
      steps word ≤ 7*value word+10*word.length+7 ∧
      out.Bounded (H+steps word) (B+steps word) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 24 H B (steps word) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack = [] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,rep,src,pc,len,dense,frames,halt⟩ :=
    materialize_high (eraseState initial) pc0 hn' table empty' enough
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,?_,?_,?_,steps_bound word,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact rep
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).heap.length = (eraseState initial).heap.length+3*value word+2 :=
      by rw [erase]; exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next = (eraseState out).heap.length := by rw [erase]; exact dense
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack = [] := by rw [erase]; exact frames
    simpa [eraseState,State.map] using h

end DirectedFlowCutGap.CounterPrefixProgram
