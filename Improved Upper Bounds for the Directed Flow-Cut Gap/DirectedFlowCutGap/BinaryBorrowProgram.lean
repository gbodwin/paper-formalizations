import DirectedFlowCutGap.PackedBooleanConstructor

/-! Literal borrow-propagation primitive. This returns exactly predCore,
including all-zero words; a later zero-test/trim wrapper is required for the
public natural predecessor. The original tail is shared after the first true bit. -/
namespace DirectedFlowCutGap.BinaryBorrowProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

/-- Entry 15 creates its own caller, entry 0 is recursive, and 14 is the halt. -/
def program : Program 16 := fun pc => match pc.val with
  | 0 => .branch .r0 1 14 14 4
  | 1 => .make .r3 .nil 13
  | 4 => .field .r1 .r0 false 5
  | 5 => .field .r0 .r0 true 6
  | 6 => .branch .r1 14 10 7 14
  | 7 => .make .r2 (.flag false) 8
  | 8 => .make .r3 (.pair .r2 .r0) 13
  | 10 => .call 0 11 .r3
  | 11 => .make .r2 (.flag true) 12
  | 12 => .make .r3 (.pair .r2 .r3) 13
  | 13 => .ret .r3
  | 15 => .call 0 14 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 16)) (source : Bits) (pc : Fin 16) : NaturalState 16 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- Ghost count of successful recursive instructions, excluding the top call. -/
def steps : Bits → ℕ
  | [] => 3
  | true::_ => 7
  | false::bs => steps bs + 8

/-- Exact append length; the true-head branch shares the unchanged tail. -/
def cells : Bits → ℕ
  | [] => 1
  | true::_ => 2
  | false::bs => cells bs + 2

theorem steps_bound (bs : Bits) : steps bs + 1 ≤ 8 * bs.length + 6 := by
  induction bs with
  | nil => simp [steps]
  | cons b bs ih => cases b <;> simp only [steps,List.length_cons] <;> omega

theorem cells_bound (bs : Bits) : cells bs ≤ 2 * bs.length + 3 := by
  induction bs with
  | nil => simp [cells]
  | cons b bs ih => cases b <;> simp only [cells,List.length_cons] <;> omega

theorem run_append {s u v : NaturalState 16} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Both finishing branches allocate a literal flag and pair, then pop the
actual caller and restore all saved registers other than its destination. -/
theorem prepend_return {heap : NaturalHeap} {bs : Bits} (bit : Bool)
    (next a b c d : ℕ) (hn : next = heap.length)
    (table : BoolList heap (if bit then d else a) bs)
    (saved : Registers ℕ) (pc : Fin 16) (stack : List (Frame ℕ 16)) (source : Bits) :
    let tail := if bit then d else a
    let ext : NaturalHeap := [.flag bit,.pair next tail]
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 11 else 7)) []
      (state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc) ∧
    BoolList (heap++ext) (next+1) (bit::bs) := by
  dsimp only
  let tail := if bit then d else a
  let ext : NaturalHeap := [.flag bit,.pair next tail]
  have t1 : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 11 else 7)) =
      some ⟨state (heap++[.flag bit]) (next+1) a b next d
        (⟨pc,.r3,saved⟩::stack) source (if bit then 12 else 8),[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have t2 : tickNatural program
      (state (heap++[.flag bit]) (next+1) a b next d
        (⟨pc,.r3,saved⟩::stack) source (if bit then 12 else 8)) =
      some ⟨state (heap++ext) (next+2) a b next (next+1)
        (⟨pc,.r3,saved⟩::stack) source 13,[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,
      Registers.set,ext,tail,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program
      (state (heap++ext) (next+2) a b next (next+1)
        (⟨pc,.r3,saved⟩::stack) source 13) =
      some ⟨state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨?_,?_⟩
  · simpa [ext,tail] using NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 (NaturalRun.done _)))
  · apply BoolList.cons (head := next) (tail := tail)
    · rw [List.getElem?_append_right (by omega)]
      simp [hn,tail]
    · simp [hn]
    · exact boolList_extend table _

/-- The recursive run restores a real incoming caller. There is no evaluator
correctness hypothesis, canonical-word restriction, or assumed frame interface. -/
theorem borrow_return {heap : NaturalHeap} {a : ℕ} {bs : Bits}
    (table : BoolList heap a bs) (next b c d : ℕ) (hn : next = heap.length)
    (saved : Registers ℕ) (pc : Fin 16) (stack : List (Frame ℕ 16)) (source : Bits) :
    ∃ ext root, ext.length = cells bs ∧
      NaturalRun program (steps bs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
        (state (heap++ext) (next+cells bs) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (predCore bs).1 := by
  induction bs generalizing heap a next b c d saved pc stack with
  | nil =>
      cases table with
      | nil ht =>
          let ext : NaturalHeap := [.nil]
          refine ⟨ext,next,rfl,?_,?_⟩
          · have t0 : tickNatural program
                (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) =
                some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,ht,tagBranch]
            have t1 : tickNatural program
                (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1) =
                some ⟨state (heap++ext) (next+1) a b c next
                  (⟨pc,.r3,saved⟩::stack) source 13,[],0⟩ := by
              simp [tickNatural,program,state,Recipe.cell,allocateNatural,Registers.set,ext]
            have t13 : tickNatural program
                (state (heap++ext) (next+1) a b c next
                  (⟨pc,.r3,saved⟩::stack) source 13) =
                some ⟨state (heap++ext) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set]
            simpa [steps,cells] using NaturalRun.step t0
              (NaturalRun.step t1 (NaturalRun.step t13 (NaturalRun.done _)))
          · exact .nil (by simp [ext,hn])
  | cons bit bs ih =>
      cases table with
      | @cons a head tail bit bs hp hf ht =>
          let frame : Frame ℕ 16 := ⟨pc,.r3,saved⟩
          have t0 : tickNatural program
              (state heap next a b c d (frame::stack) source 0) =
              some ⟨state heap next a b c d (frame::stack) source 4,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t4 : tickNatural program
              (state heap next a b c d (frame::stack) source 4) =
              some ⟨state heap next a head c d (frame::stack) source 5,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          have t5 : tickNatural program
              (state heap next a head c d (frame::stack) source 5) =
              some ⟨state heap next tail head c d (frame::stack) source 6,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          cases bit with
          | true =>
              have t6 : tickNatural program
                  (state heap next tail head c d (frame::stack) source 6) =
                  some ⟨state heap next tail head c d (frame::stack) source 7,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hf,tagBranch]
              obtain ⟨finish,rep⟩ := prepend_return false next tail head c d hn ht saved pc stack source
              refine ⟨[.flag false,.pair next tail],next+1,rfl,?_,?_⟩
              · simpa [steps,cells,frame] using NaturalRun.step t0 (NaturalRun.step t4
                  (NaturalRun.step t5 (NaturalRun.step t6 finish)))
              · simpa [predCore] using rep
          | false =>
              have t6 : tickNatural program
                  (state heap next tail head c d (frame::stack) source 6) =
                  some ⟨state heap next tail head c d (frame::stack) source 10,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hf,tagBranch]
              have t10 : tickNatural program
                  (state heap next tail head c d (frame::stack) source 10) =
                  some ⟨state heap next tail head c d
                    (⟨11,.r3,⟨tail,head,c,d⟩⟩::frame::stack) source 0,[],0⟩ := by
                simp [tickNatural,program,state]
              obtain ⟨ext,root,len,recRun,recRep⟩ :=
                ih ht next head c d hn ⟨tail,head,c,d⟩ 11 (frame::stack)
              have hn' : next+cells bs = (heap++ext).length := by simp [hn,len]
              obtain ⟨finish,rep⟩ := prepend_return true (next+cells bs) tail head c root hn'
                recRep saved pc stack source
              refine ⟨ext++[.flag true,.pair (next+cells bs) root],next+cells bs+1,?_,?_,?_⟩
              · simp [cells,len]
              · have body := run_append recRun finish
                simpa [steps,cells,frame,List.append_assoc,Nat.add_assoc] using
                  NaturalRun.step t0 (NaturalRun.step t4 (NaturalRun.step t5
                    (NaturalRun.step t6 (NaturalRun.step t10 body))))
              · simpa [predCore,List.append_assoc] using rep

/-- Self-contained top-level entry starts with no caller frames and makes its
own. Source and old heap are literally preserved; the dense cursor is exact. -/
theorem borrow_high {bs : Bits} (initial : NaturalState 16)
    (pc0 : initial.pc = 15) (hn : initial.next = initial.heap.length)
    (table : BoolList initial.heap initial.registers.a bs) (frames : initial.stack = []) :
    ∃ final, NaturalRun program (steps bs+1) initial [] final ∧
      BoolList final.heap final.registers.d (predCore bs).1 ∧
      BoolList final.heap initial.registers.a bs ∧
      final.source = initial.source ∧ final.pc = 14 ∧ final.stack = [] ∧
      final.registers.a = initial.registers.a ∧ final.registers.b = initial.registers.b ∧
      final.registers.c = initial.registers.c ∧ final.next = final.heap.length ∧
      (∃ ext, final.heap = initial.heap++ext ∧ ext.length = cells bs) ∧
      tickNatural program final = none := by
  cases initial with
  | mk heap next regs st pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn table frames
          subst pc
          subst st
          obtain ⟨ext,root,len,run,rep⟩ :=
            borrow_return table next b c d hn ⟨a,b,c,d⟩ 14 [] source
          have t15 : tickNatural program (state heap next a b c d [] source 15) =
              some ⟨state heap next a b c d [⟨14,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
            simp [tickNatural,program,state]
          refine ⟨state (heap++ext) (next+cells bs) a b c root [] source 14,
            ?_,rep,boolList_extend table ext,rfl,rfl,rfl,rfl,rfl,rfl,?_,⟨ext,rfl,len⟩,?_⟩
          · simpa [state] using NaturalRun.step t15 run
          · simp [state,hn,len]
          · simp [tickNatural,program,state]

/-- The existing bit interpreter executes the same finite table, including
copied saved frames and binary allocation/cursor work. The final halt is paid. -/
theorem borrow_bit {bs : Bits} {H B : ℕ} (initial : BitState 16)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 15)
    (hn : value initial.next = initial.heap.length)
    (table : BoolList (eraseState initial).heap (eraseState initial).registers.a bs)
    (frames : initial.stack = []) :
    ∃ charge out, Run program (steps bs+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (predCore bs).1 ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a bs ∧
      out.source = initial.source ∧ out.pc = 14 ∧ out.stack = [] ∧
      value out.next = out.heap.length ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext ∧ ext.length = cells bs) ∧
      steps bs+1 ≤ 8*bs.length+6 ∧ cells bs ≤ 2*bs.length+3 ∧
      out.Bounded (H+(steps bs+1)) (B+(steps bs+1)) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 16 H B (steps bs+1) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have frames' : (eraseState initial).stack = [] := by simp [eraseState,State.map,frames]
  obtain ⟨final,high,rep,word,src,pc,stack,_,_,_,dense,ext,halt⟩ :=
    borrow_high (eraseState initial) pc0 hn' table frames'
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,?_,steps_bound bs,cells_bound bs,
    bound,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact rep
  · rw [erase]; exact word
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack = [] := by rw [erase]; exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next = (eraseState out).heap.length := by rw [erase]; exact dense
    simpa [eraseState,State.map] using h
  · rw [erase]; exact ext

end DirectedFlowCutGap.BinaryBorrowProgram
