import DirectedFlowCutGap.BinaryIncrementProgram
import DirectedFlowCutGap.ReferenceProgramLabels

/-! A concrete stored-word scan. Every pair cell triggers an actual recursive
binary increment, and every stored padding bit counts. Input and source are
preserved in the same append-only heap. -/
namespace DirectedFlowCutGap.BinaryLengthProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def label (p : Fin 16) : Fin 24 := ⟨p.val,by omega⟩
def program : Program 24 := fun pc =>
  if pc.val=14 then .move .r1 .r3 21
  else if h : pc.val<16 then
    ReferenceProgramLabels.instruction label (BinaryIncrementProgram.program ⟨pc.val,h⟩)
  else match pc.val with
    | 16 => .make .r1 .nil 17
    | 17 => .branch .r0 22 23 23 18
    | 18 => .field .r2 .r0 true 19
    | 19 => .move .r0 .r1 20
    | 20 => .call 0 14 .r3
    | 21 => .move .r0 .r2 17
    | _ => .halt

theorem agree (pc : Fin 16) (h : BinaryIncrementProgram.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryIncrementProgram.program pc) := by
  fin_cases pc <;> simp_all [program,label,BinaryIncrementProgram.program]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 24) :
    NaturalState 24 := ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def countWord : ℕ → Bits → Bits
  | 0, acc => acc
  | n+1, acc => countWord n (increment true acc).1

def scanSteps : ℕ → Bits → ℕ
  | 0, _ => 1
  | n+1, acc => BinaryIncrementProgram.steps acc+6+scanSteps n (increment true acc).1

def scanCells : ℕ → Bits → ℕ
  | 0, _ => 0
  | n+1, acc => BinaryIncrementProgram.cells acc+scanCells n (increment true acc).1

theorem countWord_spec (n : ℕ) (acc : Bits) :
    value (countWord n acc)=value acc+n ∧ (countWord n acc).length ≤ acc.length+n := by
  induction n generalizing acc with
  | zero => simp [countWord]
  | succ n ih =>
      have hi := increment_spec true acc
      have h := ih (increment true acc).1
      simp only [countWord,Bool.toNat_true] at *
      constructor <;> omega

theorem scanSteps_bound (n : ℕ) (acc : Bits) :
    scanSteps n acc ≤ (8*(acc.length+n)+12)*n+1 := by
  induction n generalizing acc with
  | zero => simp [scanSteps]
  | succ n ih =>
      have hi := (increment_spec true acc).2.1
      have hs := BinaryIncrementProgram.steps_bound acc
      have h := ih (increment true acc).1
      have hm : (8*((increment true acc).1.length+n)+12)*n ≤
          (8*(acc.length+(n+1))+12)*n := Nat.mul_le_mul_right n (by omega)
      simp only [scanSteps]
      nlinarith

theorem scanCells_bound (n : ℕ) (acc : Bits) :
    scanCells n acc ≤ (2*(acc.length+n)+3)*n := by
  induction n generalizing acc with
  | zero => simp [scanCells]
  | succ n ih =>
      have hi := (increment_spec true acc).2.1
      have hs := BinaryIncrementProgram.cells_bound acc
      have h := ih (increment true acc).1
      have hm : (2*((increment true acc).1.length+n)+3)*n ≤
          (2*(acc.length+(n+1))+3)*n := Nat.mul_le_mul_right n (by omega)
      simp only [scanCells]
      nlinarith

theorem run_append {s u v : NaturalState 24} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Each visited input pair invokes the actual increment body. The accumulator
representation is preserved at the real continuation and next scan iteration. -/
theorem scan {word acc : Bits} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (counter : BoolList heap b acc)
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
            ih (boolList_extend ht ext) rep (next+BinaryIncrementProgram.cells acc) tail root hn'
          refine ⟨out,?_,stored,⟨ext++more,?_,?_⟩,dense,frames,src,pc,halt⟩
          · have endRun := NaturalRun.step t14 (NaturalRun.step t21 rest)
            have body := run_append inc' endRun
            convert NaturalRun.step t17 (NaturalRun.step t18 (NaturalRun.step t19 (NaturalRun.step t20 body))) using 1 <;> simp [scanSteps,List.length_cons]
            omega
          · simpa [List.append_assoc] using hout
          · simp [scanCells,List.length_cons,exlen,mlen]

/-- Self-contained initialization allocates its own empty counter, then visits
all stored cells. No caller, supplied counter or value oracle is assumed. -/
theorem length_high {word : Bits} (initial : NaturalState 24)
    (pc0 : initial.pc=16) (hn : initial.next=initial.heap.length)
    (input : BoolList initial.heap initial.registers.a word) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (1+scanSteps word.length []) initial [] out ∧
      BoolList out.heap out.registers.b (countWord word.length []) ∧
      value (countWord word.length [])=word.length ∧
      BoolList out.heap initial.registers.a word ∧
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
            scan (boolList_extend input [.nil]) counter (next+1) c d hn' source
          refine ⟨out,?_,stored,?_,?_,⟨[.nil]++more,?_,?_⟩,
            dense,frames,src,pc,halt⟩
          · simpa [state,Nat.add_comm] using NaturalRun.step init run
          · simpa [value] using (countWord_spec word.length []).1
          · rw [ext]
            exact boolList_extend (boolList_extend input [.nil]) more
          · simpa [List.append_assoc] using ext
          · simp [len,Nat.add_comm]

/-- The lower interpreter executes the same scan, recursive arithmetic and
saved calls. All their allocations/copies and the single final halt are paid. -/
theorem length_bit {word : Bits} {H B : ℕ} (initial : BitState 24)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=16)
    (hn : value initial.next=initial.heap.length)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+scanSteps word.length []) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b (countWord word.length []) ∧
      value (countWord word.length [])=word.length ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a word ∧
      out.heap.length=initial.heap.length+1+scanCells word.length [] ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧ out.source=initial.source ∧ out.pc=22 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 24 H B (1+scanSteps word.length []) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,stored,value_eq,original,⟨ext,heap_eq,len⟩,dense,frames,src,pc,halt⟩ :=
    length_high (eraseState initial) pc0 hn' input empty'
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,value_eq,?_,?_,?_,?_,source.trans src,?_,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact stored
  · rw [erase];exact original
  · have h : (eraseState out).heap.length=(eraseState initial).heap.length+1+scanCells word.length [] := by
      rw [erase,heap_eq,List.length_append,len]
      omega
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.BinaryLengthProgram
