import DirectedFlowCutGap.BinaryIncrementProgram
import DirectedFlowCutGap.ReferenceProgramLabels
import DirectedFlowCutGap.ReferenceProgramStack

/-! A literal finite ripple-carry addition table. Two entry labels encode carry;
all eight Boolean cases are instruction branches. The returned list is exactly
`BinaryArithmetic.add`, including high zero padding. This is one primitive,
not a multiplication, input-packing, or graph-runtime theorem. -/
namespace DirectedFlowCutGap.BinaryAdditionProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

/-- Slots 0–13 and 15 are the existing increment body; its old halt 14 is
an actual return to the addition caller. Slots 60 and 61 create top callers. -/
def program : Program 64 := fun pc => match pc.val with
  | 0 => .branch .r0 1 14 14 4
  | 1 => .make .r2 (.flag true) 2
  | 2 => .make .r3 .nil 3
  | 3 => .make .r3 (.pair .r2 .r3) 13
  | 4 => .field .r1 .r0 false 5
  | 5 => .field .r0 .r0 true 6
  | 6 => .branch .r1 14 7 10 14
  | 7 => .make .r2 (.flag true) 8
  | 8 => .make .r3 (.pair .r2 .r0) 13
  | 10 => .call 0 11 .r3
  | 11 => .make .r2 (.flag false) 12
  | 12 => .make .r3 (.pair .r2 .r3) 13
  | 13 => .ret .r3
  | 14 => .ret .r3
  | 15 => .call 0 14 .r3
  | 16 => .branch .r0 44 63 63 17
  | 17 => .branch .r1 46 63 63 18
  | 18 => .field .r2 .r0 false 19
  | 19 => .field .r0 .r0 true 20
  | 20 => .field .r3 .r1 false 21
  | 21 => .field .r1 .r1 true 22
  | 22 => .branch .r2 63 23 24 63
  | 23 => .branch .r3 63 32 33 63
  | 24 => .branch .r3 63 33 34 63
  | 25 => .branch .r0 45 63 63 26
  | 26 => .branch .r1 47 63 63 27
  | 27 => .field .r2 .r0 false 28
  | 28 => .field .r0 .r0 true 29
  | 29 => .field .r3 .r1 false 30
  | 30 => .field .r1 .r1 true 31
  | 31 => .branch .r2 63 35 36 63
  | 32 => .call 16 38 .r3
  | 33 => .call 16 40 .r3
  | 34 => .call 25 38 .r3
  | 35 => .branch .r3 63 33 34 63
  | 36 => .branch .r3 63 34 37 63
  | 37 => .call 25 40 .r3
  | 38 => .make .r2 (.flag false) 39
  | 39 => .make .r3 (.pair .r2 .r3) 42
  | 40 => .make .r2 (.flag true) 41
  | 41 => .make .r3 (.pair .r2 .r3) 42
  | 42 => .ret .r3
  | 44 => .ret .r1
  | 45 => .move .r0 .r1 15
  | 46 => .ret .r0
  | 47 => .move .r0 .r0 15
  | 60 => .call 16 63 .r3
  | 61 => .call 25 63 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 64)) (source : Bits) (pc : Fin 64) : NaturalState 64 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def entry (carry : Bool) : Fin 64 := if carry then 25 else 16

def topEntry (carry : Bool) : Fin 64 := if carry then 61 else 60

def finishEntry (bit : Bool) : Fin 64 := if bit then 40 else 38

/-- Ghost counts never compute the output word. -/
def steps : Bool → Bits → Bits → ℕ
  | c, [], ys => if c then BinaryIncrementProgram.steps ys + 4 else 2
  | c, x::xs, [] => if c then BinaryIncrementProgram.steps (x::xs) + 5 else 3
  | c, x::xs, y::ys => steps (fullAdder x y c).2 xs ys + 12

def cells : Bool → Bits → Bits → ℕ
  | c, [], ys => if c then BinaryIncrementProgram.cells ys else 0
  | c, x::xs, [] => if c then BinaryIncrementProgram.cells (x::xs) else 0
  | c, x::xs, y::ys => cells (fullAdder x y c).2 xs ys + 2

theorem steps_bound (carry : Bool) (xs ys : Bits) :
    steps carry xs ys + 1 ≤ 12 * (xs.length + ys.length + 1) := by
  induction xs generalizing carry ys with
  | nil =>
      have h := BinaryIncrementProgram.steps_bound ys
      cases carry <;> simp only [steps,List.length_nil,zero_add,Bool.false_eq_true,ite_false,ite_true] <;> omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := BinaryIncrementProgram.steps_bound (x::xs)
          cases carry <;> simp only [steps,List.length_nil,List.length_cons,add_zero,
            Bool.false_eq_true,ite_false,ite_true] at * <;> omega
      | cons y ys =>
          have h := ih (fullAdder x y carry).2 ys
          simp only [steps,List.length_cons]; omega

theorem cells_bound (carry : Bool) (xs ys : Bits) :
    cells carry xs ys ≤ 2 * (xs.length + ys.length) + 3 := by
  induction xs generalizing carry ys with
  | nil =>
      have h := BinaryIncrementProgram.cells_bound ys
      cases carry <;> simp only [cells,List.length_nil,zero_add,Bool.false_eq_true,ite_false,ite_true] <;> omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := BinaryIncrementProgram.cells_bound (x::xs)
          cases carry <;> simp only [cells,List.length_nil,List.length_cons,add_zero,
            Bool.false_eq_true,ite_false,ite_true] at * <;> omega
      | cons y ys =>
          have h := ih (fullAdder x y carry).2 ys
          simp only [cells,List.length_cons]; omega

theorem run_append {s u v : NaturalState 64} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

def incLabel (pc : Fin 16) : Fin 64 := ⟨pc.val,by omega⟩

theorem increment_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc ≠ .halt) :
    program (incLabel pc) =
      ReferenceProgramLabels.instruction incLabel (BinaryIncrementProgram.program pc) := by
  fin_cases pc <;> simp_all [program,BinaryIncrementProgram.program,
    ReferenceProgramLabels.instruction,incLabel]

/-- The old self-contained increment entry runs under an actual additional
caller. Its old halt slot then executes a paid return to that caller. -/
theorem increment_return {heap : NaturalHeap} {a : ℕ} {bs : Bits}
    (table : BoolList heap a bs) (next b c d : ℕ) (hn : next = heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root, ext.length = BinaryIncrementProgram.cells bs ∧
      NaturalRun program (BinaryIncrementProgram.steps bs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 15) []
        (state (heap++ext) (next+BinaryIncrementProgram.cells bs)
          saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (increment true bs).1 := by
  obtain ⟨ext,root,len,old,rep⟩ := BinaryIncrementProgram.increment_return table
    next b c d hn ⟨a,b,c,d⟩ 14 [] source
  have top : tickNatural BinaryIncrementProgram.program
      (BinaryIncrementProgram.state heap next a b c d [] source 15) =
      some ⟨BinaryIncrementProgram.state heap next a b c d
        [⟨14,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
    simp [tickNatural,BinaryIncrementProgram.program,BinaryIncrementProgram.state]
  have relocated := ReferenceProgramLabels.run incLabel BinaryIncrementProgram.program
    program increment_slots (NaturalRun.step top old)
  have framed := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) relocated
  have ret : tickNatural program
      (state (heap++ext) (next+BinaryIncrementProgram.cells bs) a b c root
        (⟨pc,.r3,saved⟩::stack) source 14) =
      some ⟨state (heap++ext) (next+BinaryIncrementProgram.cells bs)
        saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  have body : NaturalRun program (BinaryIncrementProgram.steps bs+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 15) []
      (state (heap++ext) (next+BinaryIncrementProgram.cells bs) a b c root
        (⟨pc,.r3,saved⟩::stack) source 14) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,incLabel,
      BinaryIncrementProgram.state,state] using framed
  simpa [Nat.add_assoc] using run_append body (NaturalRun.step ret (NaturalRun.done _))

/-- Bounded execution of this literal table, accumulating its actual events. -/
def runSteps : ℕ → NaturalState 64 → Option (NaturalState 64 × List Event)
  | 0,s => some (s,[])
  | n+1,s => (tickNatural program s).bind fun r =>
      (runSteps n r.state).map fun v => (v.1,r.events++v.2)

theorem runSteps_sound {n : ℕ} {s out : NaturalState 64} {events : List Event}
    (h : runSteps n s = some (out,events)) : NaturalRun program n s events out := by
  induction n generalizing s out events with
  | zero => simp only [runSteps,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; exact .done _
  | succ n ih =>
      simp only [runSteps] at h
      cases ht : tickNatural program s with
      | none => simp [ht] at h
      | some r =>
          simp only [ht,Option.bind_some] at h
          cases hr : runSteps n r.state with
          | none => simp [hr] at h
          | some v =>
              rcases v with ⟨u,ev⟩
              simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact .step ht (ih hr)

/-- Nine real instructions read both cells, branch on both flags, and save
an actual recursive caller. `fullAdder` occurs only in this specification. -/
theorem cons_prefix (carry x y : Bool) {heap : NaturalHeap}
    (next a b c d hx tx hy ty : ℕ)
    (px : heap[a]? = some (.pair hx tx)) (fx : heap[hx]? = some (.flag x))
    (py : heap[b]? = some (.pair hy ty)) (fy : heap[hy]? = some (.flag y))
    (stack : List (Frame ℕ 64)) (source : Bits) :
    NaturalRun program 9 (state heap next a b c d stack source (entry carry)) []
      (state heap next tx ty hx hy
        (⟨finishEntry (fullAdder x y carry).1,.r3,⟨tx,ty,hx,hy⟩⟩::stack)
        source (entry (fullAdder x y carry).2)) := by
  let p1 : Fin 64 := if carry then 26 else 17
  let p2 : Fin 64 := if carry then 27 else 18
  let p3 : Fin 64 := if carry then 28 else 19
  let p4 : Fin 64 := if carry then 29 else 20
  let p5 : Fin 64 := if carry then 30 else 21
  let p6 : Fin 64 := if carry then 31 else 22
  let p7 : Fin 64 := if carry then (if x then 36 else 35) else (if x then 24 else 23)
  let p8 : Fin 64 := if carry then
    (if x then (if y then 37 else 34) else (if y then 34 else 33)) else
    (if x then (if y then 34 else 33) else (if y then 33 else 32))
  have t0 : tickNatural program (state heap next a b c d stack source (entry carry)) =
      some ⟨state heap next a b c d stack source p1,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,entry,p1,Registers.get,px,tagBranch]
  have t1 : tickNatural program (state heap next a b c d stack source p1) =
      some ⟨state heap next a b c d stack source p2,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,p1,p2,Registers.get,py,tagBranch]
  have t2 : tickNatural program (state heap next a b c d stack source p2) =
      some ⟨state heap next a b hx d stack source p3,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,p2,p3,Registers.get,Registers.set,px]
  have t3 : tickNatural program (state heap next a b hx d stack source p3) =
      some ⟨state heap next tx b hx d stack source p4,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,p3,p4,Registers.get,Registers.set,px]
  have t4 : tickNatural program (state heap next tx b hx d stack source p4) =
      some ⟨state heap next tx b hx hy stack source p5,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,p4,p5,Registers.get,Registers.set,py]
  have t5 : tickNatural program (state heap next tx b hx hy stack source p5) =
      some ⟨state heap next tx ty hx hy stack source p6,[],0⟩ := by
    cases carry <;> simp [tickNatural,program,state,p5,p6,Registers.get,Registers.set,py]
  have t6 : tickNatural program (state heap next tx ty hx hy stack source p6) =
      some ⟨state heap next tx ty hx hy stack source p7,[],0⟩ := by
    cases carry <;> cases x <;> simp [tickNatural,program,state,p6,p7,Registers.get,fx,tagBranch]
  have t7 : tickNatural program (state heap next tx ty hx hy stack source p7) =
      some ⟨state heap next tx ty hx hy stack source p8,[],0⟩ := by
    cases carry <;> cases x <;> cases y <;>
      simp [tickNatural,program,state,p7,p8,Registers.get,fy,tagBranch]
  have t8 : tickNatural program (state heap next tx ty hx hy stack source p8) =
      some ⟨state heap next tx ty hx hy
        (⟨finishEntry (fullAdder x y carry).1,.r3,⟨tx,ty,hx,hy⟩⟩::stack)
        source (entry (fullAdder x y carry).2),[],0⟩ := by
    cases carry <;> cases x <;> cases y <;>
      simp [tickNatural,program,state,p8,entry,finishEntry,fullAdder]
  exact NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2
    (NaturalRun.step t3 (NaturalRun.step t4 (NaturalRun.step t5
      (NaturalRun.step t6 (NaturalRun.step t7 (NaturalRun.step t8 (NaturalRun.done _)))))))))

/-- Both literal sum continuations append a flag and a pair, then restore
the incoming caller, changing only its designated result register. -/
theorem prepend_return {heap : NaturalHeap} {bs : Bits} (bit : Bool)
    (next a b c d : ℕ) (hn : next = heap.length) (table : BoolList heap d bs)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    let ext : NaturalHeap := [.flag bit,.pair next d]
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (finishEntry bit)) []
      (state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc) ∧
    BoolList (heap++ext) (next+1) (bit::bs) := by
  dsimp only
  constructor
  · apply runSteps_sound
    cases bit <;> simp [runSteps,tickNatural,program,state,finishEntry,allocateNatural,
      Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  · apply BoolList.cons (head := next) (tail := d)
    · rw [List.getElem?_append_right (by omega)]; simp [hn]
    · simp [hn]
    · exact boolList_extend table _

/-- Main caller contract: arbitrary padded words, append-only dense heap,
unchanged source, and a literal stack pop restoring all non-result registers. -/
theorem add_return {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (carry : Bool) (next c d : ℕ) (hn : next = heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root, ext.length = cells carry xs ys ∧
      NaturalRun program (steps carry xs ys)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (entry carry)) []
        (state (heap++ext) (next+cells carry xs ys)
          saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (add carry xs ys).1 := by
  induction xs generalizing heap a b ys carry next c d saved pc stack with
  | nil =>
      cases left with
      | nil ht =>
          cases carry with
          | false =>
              refine ⟨[],b,rfl,?_,?_⟩
              · apply runSteps_sound
                simp [steps,cells,runSteps,tickNatural,program,state,entry,
                  Registers.get,Registers.set,ht,tagBranch]
              · simpa [add,increment] using right
          | true =>
              obtain ⟨ext,root,len,inc,rep⟩ := increment_return right next b c d hn saved pc stack source
              have preRun : NaturalRun program 2
                  (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (entry true)) []
                  (state heap next b b c d (⟨pc,.r3,saved⟩::stack) source 15) := by
                apply runSteps_sound
                simp [runSteps,tickNatural,program,state,entry,Registers.get,Registers.set,ht,tagBranch]
              refine ⟨ext,root,len,?_,?_⟩
              · convert run_append preRun inc using 1 <;> simp [steps,cells]; omega
              · simpa [add] using rep
  | cons x xs ih =>
      cases left with
      | @cons a hx tx x xs px fx lx =>
          cases ys with
          | nil =>
              cases right with
              | nil ht =>
                  cases carry with
                  | false =>
                      refine ⟨[],a,rfl,?_,?_⟩
                      · apply runSteps_sound
                        simp [steps,cells,runSteps,tickNatural,program,state,entry,
                          Registers.get,Registers.set,ht,px,tagBranch]
                      · simpa [add,increment] using (BoolList.cons px fx lx)
                  | true =>
                      obtain ⟨ext,root,len,inc,rep⟩ := increment_return (BoolList.cons px fx lx)
                        next b c d hn saved pc stack source
                      have preRun : NaturalRun program 3
                          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (entry true)) []
                          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 15) := by
                        apply runSteps_sound
                        simp [runSteps,tickNatural,program,state,entry,Registers.get,Registers.set,ht,px,tagBranch]
                      refine ⟨ext,root,len,?_,?_⟩
                      · convert run_append preRun inc using 1 <;> simp [steps,cells]; omega
                      · simpa [add] using rep
          | cons y ys =>
              cases right with
              | @cons b hy ty y ys py fy ly =>
                  let frame : Frame ℕ 64 := ⟨pc,.r3,saved⟩
                  let sum := (fullAdder x y carry).1
                  let co := (fullAdder x y carry).2
                  obtain ⟨ext,root,len,recRun,recRep⟩ :=
                    ih lx ly co next hx hy hn ⟨tx,ty,hx,hy⟩ (finishEntry sum) (frame::stack)
                  have hn' : next+cells co xs ys = (heap++ext).length := by simp [hn,len]
                  obtain ⟨finish,rep⟩ := prepend_return sum (next+cells co xs ys)
                    tx ty hx root hn' recRep saved pc stack source
                  have preRun := cons_prefix carry x y next a b c d hx tx hy ty px fx py fy (frame::stack) source
                  refine ⟨ext++[.flag sum,.pair (next+cells co xs ys) root],
                    next+cells co xs ys+1,?_,?_,?_⟩
                  · simp [cells,len,co]
                  · have body := run_append preRun (run_append recRun finish)
                    convert body using 1 <;> simp [steps,cells,co,sum,List.append_assoc,Nat.add_assoc]; omega
                  · simpa [add,co,sum,List.append_assoc] using rep

/-- The top-level call creates its own frame. Both old input words coexist
with the exact padded sum in one append-only output heap. -/
theorem add_high {xs ys : Bits} (carry : Bool) (initial : NaturalState 64)
    (pc0 : initial.pc = topEntry carry) (hn : initial.next = initial.heap.length)
    (left : BoolList initial.heap initial.registers.a xs)
    (right : BoolList initial.heap initial.registers.b ys) (frames : initial.stack = []) :
    ∃ final, NaturalRun program (steps carry xs ys+1) initial [] final ∧
      BoolList final.heap final.registers.d (add carry xs ys).1 ∧
      BoolList final.heap initial.registers.a xs ∧
      BoolList final.heap initial.registers.b ys ∧
      final.source = initial.source ∧ final.pc = 63 ∧ final.stack = [] ∧
      final.registers.a = initial.registers.a ∧ final.registers.b = initial.registers.b ∧
      final.registers.c = initial.registers.c ∧ final.next = final.heap.length ∧
      (∃ ext, final.heap = initial.heap++ext ∧ ext.length = cells carry xs ys) ∧
      tickNatural program final = none := by
  cases initial with
  | mk heap next regs st pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn left right frames
          subst pc
          subst st
          obtain ⟨ext,root,len,run,rep⟩ :=
            add_return left right carry next c d hn ⟨a,b,c,d⟩ 63 [] source
          have top : tickNatural program (state heap next a b c d [] source (topEntry carry)) =
              some ⟨state heap next a b c d [⟨63,.r3,⟨a,b,c,d⟩⟩] source (entry carry),[],0⟩ := by
            cases carry <;> simp [tickNatural,program,state,topEntry,entry]
          refine ⟨state (heap++ext) (next+cells carry xs ys) a b c root [] source 63,
            ?_,rep,boolList_extend left ext,boolList_extend right ext,
            rfl,rfl,rfl,rfl,rfl,rfl,?_,⟨ext,rfl,len⟩,?_⟩
          · simpa [state] using NaturalRun.step top run
          · simp [state,hn,len]
          · simp [tickNatural,program,state]

/-- The actual bit interpreter executes every branch, saved frame, allocation
and return, with one paid final halt. Input representation remains explicit. -/
theorem add_bit {xs ys : Bits} {H B : ℕ} (carry : Bool) (initial : BitState 64)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = topEntry carry)
    (hn : value initial.next = initial.heap.length)
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.b ys)
    (frames : initial.stack = []) :
    ∃ charge out, Run program (steps carry xs ys+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (add carry xs ys).1 ∧
      value (add carry xs ys).1 = value xs+value ys+carry.toNat ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b ys ∧
      out.source = initial.source ∧ out.pc = 63 ∧ out.stack = [] ∧
      value out.next = out.heap.length ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext ∧
        ext.length = cells carry xs ys) ∧
      steps carry xs ys+1 ≤ 12*(xs.length+ys.length+1) ∧
      cells carry xs ys ≤ 2*(xs.length+ys.length)+3 ∧
      out.Bounded (H+(steps carry xs ys+1)) (B+(steps carry xs ys+1)) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 64 H B (steps carry xs ys+1) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have frames' : (eraseState initial).stack = [] := by simp [eraseState,State.map,frames]
  obtain ⟨final,high,rep,lword,rword,src,pc,stack,_,_,_,dense,ext,halt⟩ :=
    add_high carry (eraseState initial) pc0 hn' left right frames'
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,(add_spec carry xs ys).1,?_,?_,source.trans src,?_,?_,?_,?_,
    steps_bound carry xs ys,cells_bound carry xs ys,bound,stop,
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

end DirectedFlowCutGap.BinaryAdditionProgram
