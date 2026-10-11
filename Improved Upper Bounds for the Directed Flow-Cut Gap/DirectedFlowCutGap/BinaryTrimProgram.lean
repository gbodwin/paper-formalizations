import DirectedFlowCutGap.PackedBooleanConstructor

/-! Literal removal of most-significant zero padding. The recursive machine
shares existing Boolean flag cells and allocates only the retained list spine.
No integer decoding, supplied normal form or abstract trim charge is used. -/
namespace DirectedFlowCutGap.BinaryTrimProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def program : Program 13 := fun pc => match pc.val with
  | 0 => .branch .r0 1 10 10 2
  | 1 => .move .r3 .r0 8
  | 2 => .field .r1 .r0 false 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .call 0 5 .r3
  | 5 => .branch .r3 6 10 10 9
  | 6 => .branch .r1 10 8 9 10
  | 8 => .ret .r3
  | 9 => .make .r3 (.pair .r1 .r3) 8
  | 11 => .call 0 12 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 13)) (source : Bits) (pc : Fin 13) : NaturalState 13 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def steps : Bits → ℕ
  | [] => 3
  | b::xs => steps xs+7+(if (trim xs).1=[] ∧ b=true then 1 else 0)

theorem steps_bound (word : Bits) : steps word ≤ 8*word.length+3 := by
  induction word with
  | nil => simp [steps]
  | cons b xs ih => simp only [steps,List.length_cons];split <;> omega

theorem run_append {s u v : NaturalState 13} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc] using NaturalRun.step ht (ih g)

/-- Allocate one retained spine cell and return through the actual caller. -/
theorem prepend_return {heap : NaturalHeap} {head tail : ℕ} {bit : Bool} {word : Bits}
    (hf : heap[head]?=some (.flag bit)) (ht : BoolList heap tail word)
    (next a c : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 13) (stack : List (Frame ℕ 13)) (source : Bits) :
    NaturalRun program 2
      (state heap next a head c tail (⟨pc,.r3,saved⟩::stack) source 9)
      [] (state (heap++[.pair head tail]) (next+1) saved.a saved.b saved.c next stack source pc) ∧
    BoolList (heap++[.pair head tail]) next (bit::word) := by
  have t9 : tickNatural program
      (state heap next a head c tail (⟨pc,.r3,saved⟩::stack) source 9)=
      some ⟨state (heap++[.pair head tail]) (next+1) a head c next
        (⟨pc,.r3,saved⟩::stack) source 8,[],0⟩ := by
    simp [tickNatural,program,state,Recipe.cell,allocateNatural,Registers.get,Registers.set]
  have t8 : tickNatural program
      (state (heap++[.pair head tail]) (next+1) a head c next (⟨pc,.r3,saved⟩::stack) source 8)=
      some ⟨state (heap++[.pair head tail]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨.step t9 (.step t8 (.done _)),?_⟩
  exact .cons (by simp [hn]) (lookup_extend hf _) (boolList_extend ht _)

/-- The real recursive calls return exactly the existing Boolean algorithm's
trimmed word. Caller registers and stack, the input heap and source survive. -/
theorem trim_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 13) (stack : List (Frame ℕ 13)) (source : Bits) :
    ∃ ext root, ext.length=(trim word).1.length ∧
      NaturalRun program (steps word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (trim word).1 := by
  induction word generalizing heap a next b c d saved pc stack with
  | nil =>
    cases input with
    | nil hnil =>
      have t0 : tickNatural program
          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
      have t1 : tickNatural program
          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
          some ⟨state heap next a b c a (⟨pc,.r3,saved⟩::stack) source 8,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t8 : tickNatural program
          (state heap next a b c a (⟨pc,.r3,saved⟩::stack) source 8)=
          some ⟨state heap next saved.a saved.b saved.c a stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact ⟨[],a,rfl,by simpa [steps] using NaturalRun.step t0 (.step t1 (.step t8 (.done _))),
        by simpa [trim] using BoolList.nil hnil⟩
  | cons bit word ih =>
    cases input with
    | @cons a head tail bit word hp hf ht =>
      let frame : Frame ℕ 13 := ⟨pc,.r3,saved⟩
      obtain ⟨ext,root,len,body,rep⟩ := ih ht next head c d hn ⟨tail,head,c,d⟩ 5 (frame::stack)
      let fresh := next+ext.length
      have fresh_eq : fresh=(heap++ext).length := by simp [fresh,hn]
      have t0 : tickNatural program
          (state heap next a b c d (frame::stack) source 0)=
          some ⟨state heap next a b c d (frame::stack) source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t2 : tickNatural program
          (state heap next a b c d (frame::stack) source 2)=
          some ⟨state heap next a head c d (frame::stack) source 3,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t3 : tickNatural program
          (state heap next a head c d (frame::stack) source 3)=
          some ⟨state heap next tail head c d (frame::stack) source 4,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t4 : tickNatural program
          (state heap next tail head c d (frame::stack) source 4)=
          some ⟨state heap next tail head c d
            (⟨5,.r3,⟨tail,head,c,d⟩⟩::frame::stack) source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      have front : NaturalRun program (4+steps word)
          (state heap next a b c d (frame::stack) source 0) []
          (state (heap++ext) fresh tail head c root (frame::stack) source 5) := by
        have h := NaturalRun.step t0 (.step t2 (.step t3 (.step t4 body)))
        have hc : steps word+1+1+1+1=4+steps word := by omega
        rw [hc] at h
        exact h
      have hf' := lookup_extend hf ext
      by_cases hz : (trim word).1=[]
      · have hnil : (heap++ext)[root]?=some .nil := by rw [hz] at rep;cases rep;assumption
        have t5 : tickNatural program
            (state (heap++ext) fresh tail head c root (frame::stack) source 5)=
            some ⟨state (heap++ext) fresh tail head c root (frame::stack) source 6,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
        cases bit with
        | false =>
          have t6 : tickNatural program
              (state (heap++ext) fresh tail head c root (frame::stack) source 6)=
              some ⟨state (heap++ext) fresh tail head c root (frame::stack) source 8,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hf',tagBranch]
          have t8 : tickNatural program
              (state (heap++ext) fresh tail head c root (frame::stack) source 8)=
              some ⟨state (heap++ext) fresh saved.a saved.b saved.c root stack source pc,[],0⟩ := by
            simp [tickNatural,program,state,frame,Registers.get,Registers.set]
          refine ⟨ext,root,?_,?_,?_⟩
          · simp [trim,hz,len]
          · convert run_append front (.step t5 (.step t6 (.step t8 (.done _)))) using 1 <;>
              simp [steps,hz]
            all_goals omega
          · simpa [trim,hz] using rep
        | true =>
          have t6 : tickNatural program
              (state (heap++ext) fresh tail head c root (frame::stack) source 6)=
              some ⟨state (heap++ext) fresh tail head c root (frame::stack) source 9,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hf',tagBranch]
          obtain ⟨finish,output⟩ := prepend_return hf' rep fresh tail c fresh_eq saved pc stack source
          refine ⟨ext++[.pair head root],fresh,?_,?_,?_⟩
          · simp [trim,hz,len]
          · convert run_append front (.step t5 (.step t6 finish)) using 1 <;>
              simp [steps,hz,List.append_assoc,fresh,Nat.add_assoc]
            all_goals omega
          · simpa [trim,List.append_assoc] using output
      · have hpair : ∃ h t,(heap++ext)[root]?=some (.pair h t) := by
          cases he : (trim word).1 with
          | nil => exact (hz he).elim
          | cons b bs => rw [he] at rep;cases rep;exact ⟨_,_,by assumption⟩
        obtain ⟨rh,rt,hr⟩ := hpair
        have t5 : tickNatural program
            (state (heap++ext) fresh tail head c root (frame::stack) source 5)=
            some ⟨state (heap++ext) fresh tail head c root (frame::stack) source 9,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hr,tagBranch]
        have he : (trim word).1.isEmpty=false := by cases h : (trim word).1 <;> simp_all
        obtain ⟨finish,output⟩ := prepend_return hf' rep fresh tail c fresh_eq saved pc stack source
        refine ⟨ext++[.pair head root],fresh,?_,?_,?_⟩
        · simp [trim,he,len]
        · convert run_append front (.step t5 finish) using 1 <;>
            simp [steps,hz,List.append_assoc,fresh,Nat.add_assoc]
          all_goals omega
        · simpa [trim,he,List.append_assoc] using output

/-- Top-level call from a represented input, with no supplied caller frame. -/
theorem trim_high {word : Bits} (initial : NaturalState 13)
    (pc0 : initial.pc=11) (hn : initial.next=initial.heap.length)
    (input : BoolList initial.heap initial.registers.a word) (empty : initial.stack=[]) :
    ∃ ext root, ext.length=(trim word).1.length ∧
      NaturalRun program (1+steps word) initial []
        (state (initial.heap++ext) (initial.next+ext.length)
          initial.registers.a initial.registers.b initial.registers.c root [] initial.source 12) ∧
      BoolList (initial.heap++ext) root (trim word).1 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc;subst stack
      have t11 : tickNatural program (state heap next a b c d [] source 11)=
          some ⟨state heap next a b c d [⟨12,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,body,rep⟩ := trim_return input next b c d hn ⟨a,b,c,d⟩ 12 [] source
      exact ⟨ext,root,len,by simpa [state,Nat.add_comm] using NaturalRun.step t11 body,rep⟩

/-- Same lower-machine execution, including the actual final halt. Output
spine allocation is exact, and every original input flag/list cell survives. -/
theorem trim_bit {word : Bits} {H B : ℕ} (initial : BitState 13)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=11)
    (hn : value initial.next=initial.heap.length)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+steps word) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (trim word).1 ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a word ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=12 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=(trim word).1.length) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 13 H B (8*word.length+4) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := trim_high (eraseState initial) pc0 hn' input hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 12)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb : 1+steps word ≤ 8*word.length+4 := by have h:=steps_bound word;omega
  have hm : completeBound 13 H B (1+steps word) ≤ completeBound 13 H B (8*word.length+4) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact boolList_extend input ext
  · exact source
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=12 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.BinaryTrimProgram
