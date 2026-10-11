import DirectedFlowCutGap.PackedBooleanConstructor

/-! A fixed 17-slot recursive instruction table converts an already represented
little-endian Boolean word to a unary spine. All traversals, allocations, calls
and returns are actual instructions. Natural values occur only in specifications.
Acquisition/encoding of the input Boolean word remains a separate obligation. -/
namespace DirectedFlowCutGap.BinaryCounterProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

/-- Invalid tags and unused slots go to the actual halt at slot 16. -/
def program : Program 17 := fun pc => match pc.val with
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
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 17)) (source : Bits) (pc : Fin 17) : NaturalState 17 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- Ghost count of successful instructions, not an executable evaluator. -/
def steps : Bits → ℕ
  | [] => 3
  | b::bs => steps bs + 3*value bs + b.toNat + 10

/-- Ghost count of cells appended by the instruction run. -/
def cells : Bits → ℕ
  | [] => 1
  | b::bs => cells bs + value bs + b.toNat

theorem steps_bound (bs : Bits) : steps bs ≤ 3*value bs+10*bs.length+3 := by
  induction bs with
  | nil => simp [steps,value]
  | cons b bs ih => simp only [steps,value,List.length_cons]; omega

theorem cells_bound (bs : Bits) : cells bs ≤ value bs+1 := by
  induction bs with
  | nil => simp [cells,value]
  | cons b bs ih => simp only [cells,value]; omega

/-- Every allocated pair remains on the result spine, so this is exact. -/
theorem cells_eq_value (bs : Bits) : cells bs = value bs+1 := by
  induction bs with
  | nil => simp [cells,value]
  | cons b bs ih => simp only [cells,value]; omega

theorem run_append {s u v : NaturalState 17} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Slots 7, 8, 9 copy precisely the inspected spine, with one final branch. -/
theorem copy_loop {heap : NaturalHeap} {a b q m : ℕ}
    (cursor : IndexSpine heap a q) (acc : IndexSpine heap b m)
    (next c d : ℕ) (hn : next = heap.length) (stack : List (Frame ℕ 17)) (source : Bits) :
    ∃ ext a' b', ext.length = q ∧
      NaturalRun program (3*q+1) (state heap next a b c d stack source 7) []
        (state (heap++ext) (next+q) a' b' c d stack source 10) ∧
      IndexSpine (heap++ext) b' (m+q) := by
  induction q generalizing heap a b m next with
  | zero =>
      cases cursor with
      | nil hc =>
          refine ⟨[],a,b,rfl,?_,?_⟩
          · have t : tickNatural program (state heap next a b c d stack source 7) =
                some ⟨state heap next a b c d stack source 10,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hc,tagBranch]
            simpa using NaturalRun.step t (NaturalRun.done _)
          · simpa using acc
  | succ q ih =>
      cases cursor with
      | @cons a payload tail q hc ht =>
          let heap' : NaturalHeap := heap++[.pair c b]
          have hn' : next+1 = heap'.length := by simp [heap',hn]
          have cursor' : IndexSpine heap' tail q := indexSpine_extend ht _
          have acc' : IndexSpine heap' next (m+1) :=
            .cons (payload := c) (by simp [heap',hn]) (indexSpine_extend acc _)
          obtain ⟨ext,a',b',hlen,run,rep⟩ := ih cursor' acc' (next+1) hn'
          refine ⟨[.pair c b]++ext,a',b',?_,?_,?_⟩
          · simp [hlen]
          · have t7 : tickNatural program (state heap next a b c d stack source 7) =
                some ⟨state heap next a b c d stack source 8,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hc,tagBranch]
            have t8 : tickNatural program (state heap next a b c d stack source 8) =
                some ⟨state heap' (next+1) a next c d stack source 9,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,heap']
            have t9 : tickNatural program (state heap' (next+1) a next c d stack source 9) =
                some ⟨state heap' (next+1) tail next c d stack source 7,[],0⟩ := by
              have hc' := lookup_extend hc [.pair c b]
              simp [tickNatural,program,state,Registers.get,Registers.set,heap',hc']
            have count : 3*(q+1)+1 = ((3*q+1)+1)+1+1 := by omega
            have cursorCount : next+(q+1) = (next+1)+q := by omega
            simpa only [count,cursorCount,heap',List.append_assoc,List.nil_append] using
              NaturalRun.step t7 (NaturalRun.step t8 (NaturalRun.step t9 run))
          · simpa [heap',List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rep

/-- The digit test and return use the saved bit pointer and a real caller. -/
theorem finish_digit {heap : NaturalHeap} {bit : Bool} {b c m : ℕ}
    (flag : heap[c]? = some (.flag bit)) (acc : IndexSpine heap b m)
    (next a d : ℕ) (hn : next = heap.length) (saved : Registers ℕ)
    (pc : Fin 17) (stack : List (Frame ℕ 17)) (source : Bits) :
    ∃ ext root, ext.length = bit.toNat ∧
      NaturalRun program (bit.toNat+3)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10) []
        (state (heap++ext) (next+bit.toNat) saved.a saved.b saved.c root stack source pc) ∧
      IndexSpine (heap++ext) root (m+bit.toNat) := by
  cases bit with
  | false =>
      refine ⟨[],b,rfl,?_,?_⟩
      · have t10 : tickNatural program
            (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10) =
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 13,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,flag,tagBranch]
        have t13 : tickNatural program
            (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 13) =
            some ⟨state heap next a b c b (⟨pc,.r3,saved⟩::stack) source 15,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        have t15 : tickNatural program
            (state heap next a b c b (⟨pc,.r3,saved⟩::stack) source 15) =
            some ⟨state heap next saved.a saved.b saved.c b stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        simpa using NaturalRun.step t10 (NaturalRun.step t13 (NaturalRun.step t15 (NaturalRun.done _)))
      · simpa using acc
  | true =>
      let heap' : NaturalHeap := heap++[.pair c b]
      refine ⟨[.pair c b],next,rfl,?_,?_⟩
      · have t10 : tickNatural program
            (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10) =
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,flag,tagBranch]
        have t11 : tickNatural program
            (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11) =
            some ⟨state heap' (next+1) a next c d (⟨pc,.r3,saved⟩::stack) source 13,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,heap']
        have t13 : tickNatural program
            (state heap' (next+1) a next c d (⟨pc,.r3,saved⟩::stack) source 13) =
            some ⟨state heap' (next+1) a next c next (⟨pc,.r3,saved⟩::stack) source 15,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        have t15 : tickNatural program
            (state heap' (next+1) a next c next (⟨pc,.r3,saved⟩::stack) source 15) =
            some ⟨state heap' (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        simpa [heap'] using NaturalRun.step t10 (NaturalRun.step t11
          (NaturalRun.step t13 (NaturalRun.step t15 (NaturalRun.done _))))
      · exact .cons (payload := c) (by simp [hn]) (indexSpine_extend acc _)


/-- Structural induction constructs an actual run through the fixed table.
The incoming frame is genuinely popped; all its other registers are restored. -/
theorem convert_return {heap : NaturalHeap} {a : ℕ} {bs : Bits}
    (table : BoolList heap a bs) (next b c d : ℕ) (hn : next = heap.length)
    (saved : Registers ℕ) (pc : Fin 17) (stack : List (Frame ℕ 17)) (source : Bits) :
    ∃ ext root, ext.length = cells bs ∧
      NaturalRun program (steps bs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
        (state (heap++ext) (next+cells bs) saved.a saved.b saved.c root stack source pc) ∧
      IndexSpine (heap++ext) root (value bs) := by
  induction bs generalizing heap a next b c d saved pc stack with
  | nil =>
      cases table with
      | nil ht =>
          refine ⟨[.nil],next,rfl,?_,?_⟩
          · have t0 : tickNatural program
                (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) =
                some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,ht,tagBranch]
            have t1 : tickNatural program
                (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1) =
                some ⟨state (heap++[.nil]) (next+1) a b c next
                  (⟨pc,.r3,saved⟩::stack) source 15,[],0⟩ := by
              simp [tickNatural,program,state,Recipe.cell,allocateNatural,Registers.set]
            have t15 : tickNatural program
                (state (heap++[.nil]) (next+1) a b c next
                  (⟨pc,.r3,saved⟩::stack) source 15) =
                some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set]
            simpa [steps,cells] using
              NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t15 (NaturalRun.done _)))
          · exact .nil (by simp [hn])
  | cons bit bs ih =>
      cases table with
      | @cons a head tail bit bs hp hf ht =>
          let frame : Frame ℕ 17 := ⟨pc,.r3,saved⟩
          obtain ⟨ext1,root1,len1,recRun,recRep⟩ :=
            ih ht next b head d hn ⟨tail,b,head,d⟩ 5 (frame::stack)
          have hn1 : next+cells bs = (heap++ext1).length := by simp [len1,hn]
          obtain ⟨ext2,cur,root2,len2,copyRun,copyRep⟩ :=
            copy_loop recRep recRep (next+cells bs) head root1 hn1 (frame::stack) source
          have hn2 : next+cells bs+value bs = ((heap++ext1)++ext2).length := by
            simp [len1,len2,hn,Nat.add_assoc]
          have flag2 : ((heap++ext1)++ext2)[head]? = some (.flag bit) :=
            lookup_extend (lookup_extend hf ext1) ext2
          obtain ⟨ext3,root3,len3,finishRun,finishRep⟩ :=
            finish_digit flag2 copyRep (next+cells bs+value bs) cur root1 hn2 saved pc stack source
          refine ⟨ext1++ext2++ext3,root3,?_,?_,?_⟩
          · simp [List.length_append,len1,len2,len3,cells,Nat.add_assoc]
          · have t0 : tickNatural program
                (state heap next a b c d (frame::stack) source 0) =
                some ⟨state heap next a b c d (frame::stack) source 2,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hp,tagBranch]
            have t2 : tickNatural program
                (state heap next a b c d (frame::stack) source 2) =
                some ⟨state heap next a b head d (frame::stack) source 3,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,hp]
            have t3 : tickNatural program
                (state heap next a b head d (frame::stack) source 3) =
                some ⟨state heap next tail b head d (frame::stack) source 4,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,hp]
            have t4 : tickNatural program
                (state heap next tail b head d (frame::stack) source 4) =
                some ⟨state heap next tail b head d
                  (⟨5,.r3,⟨tail,b,head,d⟩⟩::frame::stack) source 0,[],0⟩ := by
              simp [tickNatural,program,state]
            have t5 : tickNatural program
                (state (heap++ext1) (next+cells bs) tail b head root1 (frame::stack) source 5) =
                some ⟨state (heap++ext1) (next+cells bs) root1 b head root1
                  (frame::stack) source 6,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set]
            have t6 : tickNatural program
                (state (heap++ext1) (next+cells bs) root1 b head root1 (frame::stack) source 6) =
                some ⟨state (heap++ext1) (next+cells bs) root1 root1 head root1
                  (frame::stack) source 7,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set]
            have suffix := run_append copyRun finishRun
            have afterRec := NaturalRun.step t5 (NaturalRun.step t6 suffix)
            have body := run_append recRun afterRec
            have count : steps (bit::bs) =
                (steps bs+(3*value bs+1+(bit.toNat+3)+1+1))+1+1+1+1 := by
              simp only [steps]
              omega
            simpa only [count,cells,List.append_assoc,Nat.add_assoc,List.nil_append] using
              NaturalRun.step t0 (NaturalRun.step t2 (NaturalRun.step t3 (NaturalRun.step t4 body)))
          · simpa [List.append_assoc,value,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
              using finishRep


/-- The enclosing caller resumes at an actual halt. The source, input word,
and every old heap cell survive the append-only execution. -/
theorem convert_high {bs : Bits} (initial : NaturalState 17)
    (pc0 : initial.pc = 0) (hn : initial.next = initial.heap.length)
    (table : BoolList initial.heap initial.registers.a bs)
    (saved : Registers ℕ) (stack : List (Frame ℕ 17))
    (frames : initial.stack = ⟨16,.r3,saved⟩::stack) :
    ∃ final, NaturalRun program (steps bs) initial [] final ∧
      IndexSpine final.heap final.registers.d (value bs) ∧
      BoolList final.heap initial.registers.a bs ∧
      final.source = initial.source ∧ final.pc = 16 ∧
      final.next = final.heap.length ∧
      (∃ ext, final.heap = initial.heap++ext ∧ ext.length = cells bs) ∧
      final.stack = stack ∧ tickNatural program final = none := by
  cases initial with
  | mk heap next regs st pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn table frames
          subst pc
          subst st
          obtain ⟨ext,root,len,run,rep⟩ :=
            convert_return table next b c d hn saved 16 stack source
          refine ⟨state (heap++ext) (next+cells bs) saved.a saved.b saved.c root stack source 16,
            run,rep,boolList_extend table ext,rfl,rfl,?_,⟨ext,rfl,len⟩,rfl,?_⟩
          · simp [state,hn,len]
          · simp [tickNatural,program,state]

/-- A directly represented lower input executes the same table, including
actual recursive frame copies and allocation/cursor bit operations. Its final
halt attempt is charged by the existing terminal accounting theorem. -/
theorem convert_bit {bs : Bits} {H B : ℕ} (initial : BitState 17)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 0)
    (hn : value initial.next = initial.heap.length)
    (table : BoolList (eraseState initial).heap (eraseState initial).registers.a bs)
    (saved : Registers Bits) (stack : List (Frame Bits 17))
    (frames : initial.stack = ⟨16,.r3,saved⟩::stack) :
    ∃ charge out, Run program (steps bs) charge initial [] out ∧
      IndexSpine (eraseState out).heap (eraseState out).registers.d (value bs) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a bs ∧
      out.source = initial.source ∧ out.pc = 16 ∧
      value out.next = out.heap.length ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext ∧ ext.length = cells bs) ∧
      steps bs ≤ 3*value bs+10*bs.length+3 ∧ cells bs ≤ value bs+1 ∧
      out.Bounded (H+steps bs) (B+steps bs) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 17 H B (steps bs) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have frames' : (eraseState initial).stack =
      ⟨16,.r3,saved.map value⟩::stack.map (Frame.map value) := by
    simp [eraseState,State.map,frames,Frame.map]
  obtain ⟨final,high,rep,word,src,pc,dense,ext,_,halt⟩ :=
    convert_high (eraseState initial) pc0 hn' table (saved.map value) (stack.map (Frame.map value)) frames'
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,steps_bound bs,cells_bound bs,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact rep
  · rw [erase]; exact word
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).next = (eraseState out).heap.length := by rw [erase]; exact dense
    simpa [eraseState,State.map] using h
  · rw [erase]; exact ext

end DirectedFlowCutGap.BinaryCounterProgram
