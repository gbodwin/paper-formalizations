import DirectedFlowCutGap.BinaryAdditionProgram

/-! A literal schoolbook multiplication table. The first operand is scanned
through its actual heap cells; a true bit invokes the already verified ripple
carry program on the retained second operand and the shifted recursive result.
The result retains the exact padding of `BinaryArithmetic.mul`. -/
namespace DirectedFlowCutGap.BinaryMultiplicationProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def addLabel (pc : Fin 64) : Fin 96 := ⟨pc.val,by omega⟩

/-- The old addition halt becomes a real return. Every multiplication control
operation, saved frame and allocation appears in this finite table. -/
def program : Program 96 := fun pc =>
  if pc.val = 63 then .ret .r3
  else if h : pc.val < 64 then
    ReferenceProgramLabels.instruction addLabel (BinaryAdditionProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 64 => .branch .r0 65 95 95 68
  | 65 => .make .r3 .nil 66
  | 66 => .ret .r3
  | 68 => .field .r2 .r0 false 69
  | 69 => .field .r0 .r0 true 70
  | 70 => .call 64 71 .r3
  | 71 => .make .r0 (.flag false) 72
  | 72 => .make .r3 (.pair .r0 .r3) 73
  | 73 => .branch .r2 95 74 75 95
  | 74 => .ret .r3
  | 75 => .move .r0 .r1 76
  | 76 => .move .r1 .r3 77
  | 77 => .call 60 78 .r3
  | 78 => .ret .r3
  | 94 => .call 64 95 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 96)) (source : Bits) (pc : Fin 96) : NaturalState 96 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- Proof-side counts do not compute any machine register or output. -/
def steps : Bits → Bits → ℕ
  | [],_ => 3
  | x::xs,ys => steps xs ys + if x then
      BinaryAdditionProgram.steps false ys (false::(mul xs ys).1)+13 else 8

def cells : Bits → Bits → ℕ
  | [],_ => 1
  | x::xs,ys => cells xs ys + 2 + if x then
      BinaryAdditionProgram.cells false ys (false::(mul xs ys).1) else 0

theorem steps_bound (xs ys : Bits) :
    steps xs ys+1 ≤ 64*(xs.length+1)*(xs.length+ys.length+2) := by
  induction xs with
  | nil => simp [steps]; omega
  | cons x xs ih =>
      have hm := (mul_spec xs ys).2.1
      have ha := BinaryAdditionProgram.steps_bound false ys (false::(mul xs ys).1)
      simp only [List.length_cons] at ha ⊢
      cases x <;> simp only [steps,Bool.false_eq_true,ite_false,ite_true] <;> nlinarith

theorem cells_bound (xs ys : Bits) :
    cells xs ys ≤ 8*(xs.length+1)*(xs.length+ys.length+2) := by
  induction xs with
  | nil => simp [cells]; omega
  | cons x xs ih =>
      have hm := (mul_spec xs ys).2.1
      have ha := BinaryAdditionProgram.cells_bound false ys (false::(mul xs ys).1)
      simp only [List.length_cons] at ha ⊢
      cases x <;> simp only [cells,Bool.false_eq_true,ite_false,ite_true] <;> nlinarith

theorem run_append {s u v : NaturalState 96} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem addition_slots (pc : Fin 64) (h : BinaryAdditionProgram.program pc ≠ .halt) :
    program (addLabel pc)=ReferenceProgramLabels.instruction addLabel
      (BinaryAdditionProgram.program pc) := by
  have hn : pc.val ≠ 63 := by
    intro he
    have eq : pc=63 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,addLabel,hn,pc.isLt]

/-- The real addition top call runs above the caller's saved stack. Its old
halt is followed by one actual return into the multiplication continuation. -/
theorem addition_return {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    ∃ ext root, ext.length=BinaryAdditionProgram.cells false xs ys ∧
      NaturalRun program (BinaryAdditionProgram.steps false xs ys+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 60) []
        (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys)
          saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (add false xs ys).1 := by
  obtain ⟨ext,root,len,old,rep⟩ := BinaryAdditionProgram.add_return left right false
    next c d hn ⟨a,b,c,d⟩ 63 [] source
  have top : tickNatural BinaryAdditionProgram.program
      (BinaryAdditionProgram.state heap next a b c d [] source 60)=
      some ⟨BinaryAdditionProgram.state heap next a b c d
        [⟨63,.r3,⟨a,b,c,d⟩⟩] source 16,[],0⟩ := by
    simp [tickNatural,BinaryAdditionProgram.program,BinaryAdditionProgram.state]
  have relocated := ReferenceProgramLabels.run addLabel BinaryAdditionProgram.program
    program addition_slots (NaturalRun.step top old)
  have framed := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) relocated
  have body : NaturalRun program (BinaryAdditionProgram.steps false xs ys+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 60) []
      (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys) a b c root
        (⟨pc,.r3,saved⟩::stack) source 63) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      addLabel,BinaryAdditionProgram.state,BinaryAdditionProgram.entry,state] using framed
  have ret : tickNatural program
      (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys) a b c root
        (⟨pc,.r3,saved⟩::stack) source 63)=
      some ⟨state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys)
        saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  simpa [Nat.add_assoc] using run_append body (NaturalRun.step ret (NaturalRun.done _))

/-- Four actual instructions inspect the first operand and save the recursive
continuation while retaining the second operand and the current flag root. -/
theorem cons_prefix {heap : NaturalHeap} (next a b c d hx tx : ℕ)
    (pair : heap[a]?=some (.pair hx tx)) (stack : List (Frame ℕ 96)) (source : Bits) :
    NaturalRun program 4 (state heap next a b c d stack source 64) []
      (state heap next tx b hx d (⟨71,.r3,⟨tx,b,hx,d⟩⟩::stack) source 64) := by
  have t0 : tickNatural program (state heap next a b c d stack source 64)=
      some ⟨state heap next a b c d stack source 68,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,pair,tagBranch]
  have t1 : tickNatural program (state heap next a b c d stack source 68)=
      some ⟨state heap next a b hx d stack source 69,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair]
  have t2 : tickNatural program (state heap next a b hx d stack source 69)=
      some ⟨state heap next tx b hx d stack source 70,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair]
  have t3 : tickNatural program (state heap next tx b hx d stack source 70)=
      some ⟨state heap next tx b hx d (⟨71,.r3,⟨tx,b,hx,d⟩⟩::stack) source 64,[],0⟩ := by
    simp [tickNatural,program,state]
  exact .step t0 (.step t1 (.step t2 (.step t3 (.done _))))

/-- Two actual allocations construct the false low bit and shifted list. -/
theorem shift {heap : NaturalHeap} {bs : Bits} (next a b c d : ℕ)
    (hn : next=heap.length) (rep : BoolList heap d bs)
    (stack : List (Frame ℕ 96)) (source : Bits) :
    let ext : NaturalHeap := [.flag false,.pair next d]
    NaturalRun program 2 (state heap next a b c d stack source 71) []
      (state (heap++ext) (next+2) next b c (next+1) stack source 73) ∧
    BoolList (heap++ext) (next+1) (false::bs) := by
  dsimp only
  constructor
  · have t0 : tickNatural program (state heap next a b c d stack source 71)=
        some ⟨state (heap++[.flag false]) (next+1) next b c d stack source 72,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t1 : tickNatural program
        (state (heap++[.flag false]) (next+1) next b c d stack source 72)=
        some ⟨state (heap++[.flag false,.pair next d]) (next+2)
          next b c (next+1) stack source 73,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,
        Registers.set,List.append_assoc,Nat.add_assoc]
    exact .step t0 (.step t1 (.done _))
  · apply BoolList.cons (head := next) (tail := d)
    · rw [List.getElem?_append_right (by omega)];simp [hn]
    · simp [hn]
    · exact boolList_extend rep _

/-- Actual recursive caller contract. The output is the literal schoolbook
word, with append-only storage and all caller registers restored except d. -/
theorem mul_return {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    ∃ ext root, ext.length=cells xs ys ∧
      NaturalRun program (steps xs ys)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 64) []
        (state (heap++ext) (next+cells xs ys)
          saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mul xs ys).1 := by
  induction xs generalizing heap a b next c d saved pc stack with
  | nil =>
      cases left with
      | nil ht =>
          have t0 : tickNatural program
              (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 64)=
              some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 65,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,ht,tagBranch]
          have t1 : tickNatural program
              (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 65)=
              some ⟨state (heap++[.nil]) (next+1) a b c next
                (⟨pc,.r3,saved⟩::stack) source 66,[],0⟩ := by
            simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
          have t2 : tickNatural program
              (state (heap++[.nil]) (next+1) a b c next
                (⟨pc,.r3,saved⟩::stack) source 66)=
              some ⟨state (heap++[.nil]) (next+1)
                saved.a saved.b saved.c next stack source pc,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          refine ⟨[.nil],next,rfl,.step t0 (.step t1 (.step t2 (.done _))),?_⟩
          apply BoolList.nil
          simp [hn]
  | cons x xs ih =>
      cases left with
      | @cons a hx tx x xs px fx lx =>
          let frame : Frame ℕ 96 := ⟨pc,.r3,saved⟩
          obtain ⟨ext,root,len,recRun,recRep⟩ :=
            ih lx right next hx d hn ⟨tx,b,hx,d⟩ 71 (frame::stack)
          let n := next+cells xs ys
          have hn' : n=(heap++ext).length := by simp [n,hn,len]
          obtain ⟨shiftRun,shiftRep⟩ := shift n tx b hx root hn' recRep (frame::stack) source
          let sh : NaturalHeap := [.flag false,.pair n root]
          let h2 := (heap++ext)++sh
          have hflag : h2[hx]?=some (.flag x) := lookup_extend (lookup_extend fx ext) sh
          have hright : BoolList h2 b ys := boolList_extend (boolList_extend right ext) sh
          have hshift : BoolList h2 (n+1) (false::(mul xs ys).1) := shiftRep
          have hn2 : n+2=h2.length := by simp [h2,sh,hn',Nat.add_assoc]
          have preRun := cons_prefix next a b c d hx tx px (frame::stack) source
          cases x with
          | false =>
              have t0 : tickNatural program (state h2 (n+2) n b hx (n+1) (frame::stack) source 73)=
                  some ⟨state h2 (n+2) n b hx (n+1) (frame::stack) source 74,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hflag,tagBranch]
              have t1 : tickNatural program (state h2 (n+2) n b hx (n+1) (frame::stack) source 74)=
                  some ⟨state h2 (n+2) saved.a saved.b saved.c (n+1) stack source pc,[],0⟩ := by
                simp [tickNatural,program,state,frame,Registers.get,Registers.set]
              refine ⟨ext++sh,n+1,?_,?_,?_⟩
              · simp [cells,len,sh]
              · have all := run_append preRun (run_append recRun
                    (run_append shiftRun (.step t0 (.step t1 (.done _)))))
                convert all using 1 <;> simp [steps,cells,n,h2,sh,List.append_assoc,Nat.add_assoc]; omega
              · simpa [mul,h2,List.append_assoc] using hshift
          | true =>
              obtain ⟨more,sum,mlen,addRun,addRep⟩ := addition_return hright hshift
                (n+2) hx (n+1) hn2 ⟨b,n+1,hx,n+1⟩ 78 (frame::stack) source
              have t0 : tickNatural program (state h2 (n+2) n b hx (n+1) (frame::stack) source 73)=
                  some ⟨state h2 (n+2) n b hx (n+1) (frame::stack) source 75,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hflag,tagBranch]
              have t1 : tickNatural program (state h2 (n+2) n b hx (n+1) (frame::stack) source 75)=
                  some ⟨state h2 (n+2) b b hx (n+1) (frame::stack) source 76,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set]
              have t2 : tickNatural program (state h2 (n+2) b b hx (n+1) (frame::stack) source 76)=
                  some ⟨state h2 (n+2) b (n+1) hx (n+1) (frame::stack) source 77,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set]
              have t3 : tickNatural program (state h2 (n+2) b (n+1) hx (n+1) (frame::stack) source 77)=
                  some ⟨state h2 (n+2) b (n+1) hx (n+1)
                    (⟨78,.r3,⟨b,n+1,hx,n+1⟩⟩::frame::stack) source 60,[],0⟩ := by
                simp [tickNatural,program,state]
              have ret : tickNatural program
                  (state (h2++more) ((n+2)+BinaryAdditionProgram.cells false ys (false::(mul xs ys).1))
                    b (n+1) hx sum (frame::stack) source 78)=
                  some ⟨state (h2++more) ((n+2)+BinaryAdditionProgram.cells false ys (false::(mul xs ys).1))
                    saved.a saved.b saved.c sum stack source pc,[],0⟩ := by
                simp [tickNatural,program,state,frame,Registers.get,Registers.set]
              refine ⟨ext++sh++more,sum,?_,?_,?_⟩
              · simp [cells,len,sh,mlen]; omega
              · have tailRun := NaturalRun.step t0 (.step t1 (.step t2 (.step t3
                    (run_append addRun (.step ret (.done _))))))
                have all := run_append preRun (run_append recRun (run_append shiftRun tailRun))
                convert all using 1 <;> simp [steps,cells,n,h2,sh,List.append_assoc,Nat.add_assoc]; omega
              · simpa [mul,h2,List.append_assoc] using addRep

/-- The top-level call creates its own frame. Both old input words coexist
with the exact padded product in one append-only output heap. -/
theorem mul_high {xs ys : Bits} (initial : NaturalState 96)
    (pc0 : initial.pc = 94) (hn : initial.next = initial.heap.length)
    (left : BoolList initial.heap initial.registers.a xs)
    (right : BoolList initial.heap initial.registers.b ys) (frames : initial.stack = []) :
    ∃ final, NaturalRun program (steps xs ys+1) initial [] final ∧
      BoolList final.heap final.registers.d (mul xs ys).1 ∧
      BoolList final.heap initial.registers.a xs ∧
      BoolList final.heap initial.registers.b ys ∧
      final.source = initial.source ∧ final.pc = 95 ∧ final.stack = [] ∧
      final.registers.a = initial.registers.a ∧ final.registers.b = initial.registers.b ∧
      final.registers.c = initial.registers.c ∧ final.next = final.heap.length ∧
      (∃ ext, final.heap = initial.heap++ext ∧ ext.length = cells xs ys) ∧
      tickNatural program final = none := by
  cases initial with
  | mk heap next regs st pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn left right frames
          subst pc
          subst st
          obtain ⟨ext,root,len,run,rep⟩ :=
            mul_return left right next c d hn ⟨a,b,c,d⟩ 95 [] source
          have top : tickNatural program (state heap next a b c d [] source (94)) =
              some ⟨state heap next a b c d [⟨95,.r3,⟨a,b,c,d⟩⟩] source (64),[],0⟩ := by
            simp [tickNatural,program,state]
          refine ⟨state (heap++ext) (next+cells xs ys) a b c root [] source 95,
            ?_,rep,boolList_extend left ext,boolList_extend right ext,
            rfl,rfl,rfl,rfl,rfl,rfl,?_,⟨ext,rfl,len⟩,?_⟩
          · simpa [state] using NaturalRun.step top run
          · simp [state,hn,len]
          · simp [tickNatural,program,state]

/-- The actual bit interpreter executes every branch, saved frame, allocation
and return, with one paid final halt. Input representation remains explicit. -/
theorem mul_bit {xs ys : Bits} {H B : ℕ} (initial : BitState 96)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 94)
    (hn : value initial.next = initial.heap.length)
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.b ys)
    (frames : initial.stack = []) :
    ∃ charge out, Run program (steps xs ys+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (mul xs ys).1 ∧
      value (mul xs ys).1 = value xs*value ys ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b ys ∧
      out.source = initial.source ∧ out.pc = 95 ∧ out.stack = [] ∧
      value out.next = out.heap.length ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext ∧
        ext.length = cells xs ys) ∧
      steps xs ys+1 ≤ 64*(xs.length+1)*(xs.length+ys.length+2) ∧
      cells xs ys ≤ 8*(xs.length+1)*(xs.length+ys.length+2) ∧
      out.Bounded (H+(steps xs ys+1)) (B+(steps xs ys+1)) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 96 H B (steps xs ys+1) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have frames' : (eraseState initial).stack = [] := by simp [eraseState,State.map,frames]
  obtain ⟨final,high,rep,lword,rword,src,pc,stack,_,_,_,dense,ext,halt⟩ :=
    mul_high (eraseState initial) pc0 hn' left right frames'
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,(mul_spec xs ys).1,?_,?_,source.trans src,?_,?_,?_,?_,
    steps_bound xs ys,cells_bound xs ys,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact rep
  · rw [erase]; exact lword
  · rw [erase]; exact rword
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack = [] := by rw [erase]; exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next = (eraseState out).heap.length := by rw [erase]; exact dense
    simpa [eraseState,State.map] using h
  · rw [erase]; exact ext


end DirectedFlowCutGap.BinaryMultiplicationProgram
