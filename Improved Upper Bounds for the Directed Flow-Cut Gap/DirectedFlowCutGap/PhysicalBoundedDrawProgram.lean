import DirectedFlowCutGap.PhysicalFairWordProgram
import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.BinaryBoundedSampler

/-!
# Physical bounded rejection

The bound word supplies both the candidate width and comparison operand.
The represented trial spine controls rejection fuel. The result is a
binary index paired with a flag for the legal zero default. Successful
runs exhibit every request and the exact unread tape.
-/

namespace DirectedFlowCutGap.PhysicalBoundedDrawProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor

def wordLabel (pc : Fin 10) : Fin 78 := ⟨20+pc.val,by omega⟩
def comparisonLabel (pc : Fin 48) : Fin 78 := ⟨30+pc.val,by omega⟩

def program : Program 78 := fun pc =>
  if pc.val < 20 then
    match pc.val with
    | 0 => .branch .r1 1 19 19 5
    | 1 => .make .r2 .nil 2
    | 2 => .make .r3 (.flag true) 3
    | 3 => .make .r3 (.pair .r2 .r3) 4
    | 4 => .ret .r3
    | 5 => .call (wordLabel 8) 6 .r2
    | 6 => .call 15 7 .r3
    | 7 => .branch .r3 19 12 8 19
    | 8 => .field .r1 .r1 true 9
    | 9 => .call 0 4 .r3
    | 12 => .make .r3 (.flag false) 3
    | 15 => .move .r1 .r2 16
    | 16 => .call (comparisonLabel 30) 17 .r3
    | 17 => .ret .r3
    | 18 => .call 0 19 .r3
    | _ => .halt
  else if pc.val=29 ∨ pc.val=76 then .ret .r3
  else if h : pc.val<30 then
    ReferenceProgramLabels.instruction wordLabel (PhysicalFairWordProgram.program ⟨pc.val-20,by omega⟩)
  else ReferenceProgramLabels.instruction comparisonLabel
    (BinaryComparisonProgram.program ⟨pc.val-30,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 78))
    (tape : Bits) (pc : Fin 78) : NaturalState 78 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

structure Outcome where
  index : Bits
  failed : Bool
  requests : Bits
  suffix : Bits
  deriving Repr, DecidableEq

def outcome (bound : Bits) : ℕ → Bits → Outcome
  | 0,tape => ⟨[],true,[],tape⟩
  | k+1,tape =>
    let x := PhysicalFairWordProgram.digits bound.length tape
    let rest := tape.drop bound.length
    if (lessEqual bound x).1 then
      let next := outcome bound k rest
      { next with requests := x++next.requests }
    else ⟨x,false,x,rest⟩

def instructions (bound : Bits) : ℕ → Bits → ℕ
  | 0,_ => 5
  | k+1,tape =>
    let x := PhysicalFairWordProgram.digits bound.length tape
    6*bound.length + BinaryComparisonProgram.steps bound x + 19 +
      if (lessEqual bound x).1 then instructions bound k (tape.drop bound.length) else 0

def ResultAt (heap : NaturalHeap) (root : ℕ) (v : Outcome) : Prop :=
  ∃ x tag, heap[root]?=some (.pair x tag) ∧ BoolList heap x v.index ∧ heap[tag]?=some (.flag v.failed)

theorem index_lt (bound : Bits) (fuel : ℕ) (tape : Bits) (positive : 0<value bound) :
    value (outcome bound fuel tape).index < value bound := by
  induction fuel generalizing tape with
  | zero => simpa [outcome,value] using positive
  | succ fuel ih =>
    simp only [outcome]
    split
    · exact ih _
    · rename_i h
      exact Nat.lt_of_not_ge (fun hp => h ((lessEqual_spec _ _).1.mpr hp))

theorem exact_requests (bound : Bits) (fuel : ℕ) (tape : Bits) :
    let out := outcome bound fuel tape
    out.requests = PhysicalFairWordProgram.digits out.requests.length tape ∧
      out.suffix=tape.drop out.requests.length ∧ out.requests.length ≤ fuel*bound.length := by
  have digits_append (i j : ℕ) (ts : Bits) :
      PhysicalFairWordProgram.digits (i+j) ts =
        PhysicalFairWordProgram.digits i ts ++ PhysicalFairWordProgram.digits j (ts.drop i) := by
    induction i generalizing ts with
    | zero => simp [PhysicalFairWordProgram.digits]
    | succ i ih =>
      rw [show i+1+j=i+j+1 by omega]
      simp only [PhysicalFairWordProgram.digits,← List.drop_tail,List.cons_append,ih]
  induction fuel generalizing tape with
  | zero => simp [outcome,PhysicalFairWordProgram.digits]
  | succ fuel ih =>
    dsimp only [outcome]
    split
    · obtain ⟨hr,hs,hl⟩ := ih (tape.drop bound.length)
      simp only [List.length_append,PhysicalFairWordProgram.digits_length]
      refine ⟨?_,?_,?_⟩
      · rw [digits_append,← hr]
      · rw [hs,List.drop_drop]
      · rw [Nat.add_mul,Nat.one_mul]
        omega
    · simp only [PhysicalFairWordProgram.digits_length]
      exact ⟨True.intro,True.intro,by rw [Nat.add_mul,Nat.one_mul]; omega⟩

def instructionBound (width fuel : ℕ) : ℕ := fuel*(6*width+16*(2*width+1)+19)+6

theorem instructions_le (bound : Bits) (fuel : ℕ) (tape : Bits) :
    instructions bound fuel tape+1 ≤ instructionBound bound.length fuel := by
  have h (k : ℕ) (ts : Bits) :
      instructions bound k ts ≤ k*(6*bound.length+16*(2*bound.length+1)+19)+5 := by
    induction k generalizing ts with
    | zero => simp [instructions]
    | succ k ih =>
      have hcmp := BinaryComparisonProgram.steps_bound bound (PhysicalFairWordProgram.digits bound.length ts)
      rw [PhysicalFairWordProgram.digits_length] at hcmp
      have tail := ih (ts.drop bound.length)
      simp only [instructions,Nat.add_mul,Nat.one_mul]
      split <;> omega
  exact Nat.add_le_add_right (h fuel tape) 1

private theorem word_slots (pc : Fin 10) (h : PhysicalFairWordProgram.program pc≠.halt) :
    program (wordLabel pc) =
      ReferenceProgramLabels.instruction wordLabel (PhysicalFairWordProgram.program pc) := by
  by_cases hp : pc.val=9
  · have eq : pc=9 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,wordLabel,show ¬20+pc.val<20 by omega,show 20+pc.val≠29 by omega,
      show 20+pc.val≠76 by omega,show 20+pc.val<30 by omega]

private theorem compare_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (comparisonLabel pc) =
      ReferenceProgramLabels.instruction comparisonLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=46
  · have eq : pc=46 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,comparisonLabel,show ¬30+pc.val<20 by omega,show 30+pc.val≠29 by omega,
      show 30+pc.val≠76 by omega,show ¬30+pc.val<30 by omega]

private theorem join {s u v : NaturalState 78} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem word_return {heap : NaturalHeap} {r : Registers ℕ} {w : ℕ}
    (width : IndexSpine heap r.a w) (caller : Frame ℕ 78) (stack : List (Frame ℕ 78)) (tape : Bits) :
    ∃ ext x, BoolList (heap++ext) x (PhysicalFairWordProgram.digits w tape) ∧
      NaturalRun program (6*w+5) (state heap r (caller::stack) tape (wordLabel 8))
        ((PhysicalFairWordProgram.digits w tape).map Event.request)
        (state (heap++ext) (caller.saved.set caller.destination x) stack (tape.drop w) caller.continuation) := by
  obtain ⟨ext,root,rep,_,body⟩ := PhysicalFairWordProgram.natural_word width tape
  have lift := ReferenceProgramLabels.run wordLabel PhysicalFairWordProgram.program program word_slots body
  have lift := ReferenceProgramStack.run program (caller::stack) lift
  let before := state (heap++ext) (r.set .r3 root) (caller::stack) (tape.drop w) (wordLabel 9)
  let after := state (heap++ext) (caller.saved.set caller.destination root) stack (tape.drop w) caller.continuation
  have run : NaturalRun program (6*w+4) (state heap r (caller::stack) tape (wordLabel 8))
      ((PhysicalFairWordProgram.digits w tape).map Event.request) before := by
    simpa [state,before,PhysicalFairWordProgram.state,PhysicalFairWordProgram.instructions,
      ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := by
    cases r
    simp [before,after,state,tickNatural,program,wordLabel,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  simpa only [List.append_nil,Nat.add_assoc] using join run (.step ret (.done after))

private theorem compare_return {heap : NaturalHeap} {r : Registers ℕ} {left right : Bits}
    (ha : BoolList heap r.a left) (hb : BoolList heap r.b right)
    (caller : Frame ℕ 78) (stack : List (Frame ℕ 78)) (tape : Bits) :
    ∃ ext flag, (heap++ext)[flag]?=some (.flag (lessEqual left right).1) ∧
      NaturalRun program (BinaryComparisonProgram.steps left right+4)
        (state heap r (caller::stack) tape (comparisonLabel 30)) []
        (state (heap++ext) (caller.saved.set caller.destination flag) stack tape caller.continuation) := by
  let initial := BinaryComparisonProgram.state heap heap.length r.a r.b r.c r.d [] tape 30
  obtain ⟨out,run,flag,_,_,h₁,h₂,h₃,hstack,htape,hpc,hdense,⟨ext,he,_⟩,_⟩ :=
    BinaryComparisonProgram.compare_high initial rfl rfl ha hb rfl
  have shape : out=BinaryComparisonProgram.state (heap++ext) (heap++ext).length r.a r.b r.c out.registers.d [] tape 46 := by
    cases out with
    | mk hp np rs sp pc tape =>
      cases rs
      simp_all [initial,BinaryComparisonProgram.state]
  have lift := ReferenceProgramLabels.run comparisonLabel BinaryComparisonProgram.program program compare_slots run
  have lift := ReferenceProgramStack.run program (caller::stack) lift
  rw [shape] at lift
  let before := state (heap++ext) ⟨r.a,r.b,r.c,out.registers.d⟩ (caller::stack) tape (comparisonLabel 46)
  let after := state (heap++ext) (caller.saved.set caller.destination out.registers.d) stack tape caller.continuation
  have body : NaturalRun program (BinaryComparisonProgram.steps left right+3)
      (state heap r (caller::stack) tape (comparisonLabel 30)) [] before := by
    cases r
    simpa [initial,before,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,BinaryComparisonProgram.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := rfl
  exact ⟨ext,out.registers.d,by simpa only [he,initial,BinaryComparisonProgram.state] using flag,
    by simpa only [List.append_nil,Nat.add_assoc] using join body (.step ret (.done after))⟩

private theorem reject_flag {heap : NaturalHeap} {r : Registers ℕ} {bound word : Bits}
    (hb : BoolList heap r.a bound) (hx : BoolList heap r.c word) (caller : Frame ℕ 78)
    (stack : List (Frame ℕ 78)) (tape : Bits) :
    ∃ ext flag, (heap++ext)[flag]?=some (.flag (lessEqual bound word).1) ∧
      NaturalRun program (BinaryComparisonProgram.steps bound word+7) (state heap r (caller::stack) tape 15) []
        (state (heap++ext) (caller.saved.set caller.destination flag) stack tape caller.continuation) := by
  let saved := caller::stack
  let args := r.set .r1 r.c
  let frame : Frame ℕ 78 := ⟨17,.r3,args⟩
  have ha : BoolList heap args.a bound := by cases r; exact hb
  have hw : BoolList heap args.b word := by cases r; exact hx
  obtain ⟨ext,flag,hflag,hrun⟩ := compare_return ha hw frame saved tape
  have move : tickNatural program (state heap r saved tape 15) =
      some ⟨state heap args saved tape 16,[],0⟩ := rfl
  have call : tickNatural program (state heap args saved tape 16) =
      some ⟨state heap args (frame::saved) tape (comparisonLabel 30),[],0⟩ := rfl
  have ret : tickNatural program (state (heap++ext) (args.set .r3 flag) saved tape 17) =
      some ⟨state (heap++ext) (caller.saved.set caller.destination flag) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [args,saved,state,tickNatural,program,Registers.get,Registers.set]
  exact ⟨ext,flag,hflag,NaturalRun.step move (NaturalRun.step call (join hrun (.step ret (.done _))))⟩

private theorem finish {heap : NaturalHeap} {r : Registers ℕ} {x : Bits}
    (input : BoolList heap r.c x) (failed : Bool) (caller : Frame ℕ 78)
    (stack : List (Frame ℕ 78)) (tape : Bits) :
    let ext : NaturalHeap := [.flag failed,.pair r.c heap.length]
    ResultAt (heap++ext) (heap.length+1) ⟨x,failed,[],tape⟩ ∧
      NaturalRun program 3 (state heap r (caller::stack) tape (if failed then 2 else 12)) []
        (state (heap++ext) (caller.saved.set caller.destination (heap.length+1)) stack tape caller.continuation) := by
  let saved := caller::stack
  let mid := heap++[Cell.flag failed]
  let full := mid++[Cell.pair r.c heap.length]
  let r1 := r.set .r3 heap.length
  let r2 := r1.set .r3 (heap.length+1)
  have flag : tickNatural program (state heap r saved tape (if failed then 2 else 12)) =
      some ⟨state mid r1 saved tape 3,[],0⟩ := by
    cases failed <;> simp [mid,r1,state,tickNatural,program,allocateNatural,Recipe.cell]
  have pair : tickNatural program (state mid r1 saved tape 3) =
      some ⟨state full r2 saved tape 4,[],0⟩ := by
    cases r
    simp [mid,full,r1,r2,state,tickNatural,program,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have done : tickNatural program (state full r2 saved tape 4) =
      some ⟨state full (caller.saved.set caller.destination (heap.length+1)) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [r1,r2,saved,state,tickNatural,program,Registers.get,Registers.set]
  have isFlag : mid[heap.length]? = some (.flag failed) := by simp [mid]
  have isPair : full[heap.length+1]? = some (.pair r.c heap.length) := by
    have h : mid.length=heap.length+1 := by simp [mid]
    rw [← h]
    simp [full]
  refine ⟨?_,?_⟩
  · have rep : ResultAt full (heap.length+1) ⟨x,failed,[],tape⟩ :=
      ⟨r.c,heap.length,isPair,boolList_extend (boolList_extend input _) _,lookup_extend isFlag _⟩
    simpa only [full,mid,List.append_assoc,List.singleton_append] using rep
  · have body := NaturalRun.step flag (NaturalRun.step pair (NaturalRun.step done (.done _)))
    simpa only [full,mid,List.append_assoc,List.singleton_append,List.append_nil] using body

private theorem preserve_observation {heap : NaturalHeap} {root : ℕ} {a b : Outcome}
    (h : ResultAt heap root a) (hi : a.index=b.index) (hf : a.failed=b.failed) : ResultAt heap root b := by
  unfold ResultAt at *
  rwa [← hi,← hf]

theorem draw_return {heap : NaturalHeap} {r : Registers ℕ} {fuel : ℕ} {bound : Bits}
    (hb : BoolList heap r.a bound) (hf : IndexSpine heap r.b fuel)
    (caller : Frame ℕ 78) (stack : List (Frame ℕ 78)) (tape : Bits) :
    ∃ ext root, ResultAt (heap++ext) root (outcome bound fuel tape) ∧
      NaturalRun program (instructions bound fuel tape) (state heap r (caller::stack) tape 0)
        ((outcome bound fuel tape).requests.map Event.request)
        (state (heap++ext) (caller.saved.set caller.destination root) stack
          (outcome bound fuel tape).suffix caller.continuation) := by
  induction fuel generalizing heap r caller stack tape with
  | zero =>
    cases hf with
    | nil h0 =>
      let saved := caller::stack
      let mid := heap++[Cell.nil]
      let args := r.set .r2 heap.length
      have test : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,h0]
      have empty : tickNatural program (state heap r saved tape 1) =
          some ⟨state mid args saved tape 2,[],0⟩ := by
        simp [mid,args,state,tickNatural,program,allocateNatural,Recipe.cell]
      have rep : BoolList mid args.c [] := by
        cases r
        exact .nil (by simp [mid,args,Registers.set])
      obtain ⟨hfinish,hret⟩ := finish rep true caller stack tape
      let ext : NaturalHeap := [.nil,.flag true,.pair heap.length mid.length]
      have hargs : args.c=heap.length := by cases r; rfl
      refine ⟨ext,mid.length+1,?_,?_⟩
      · simpa only [ext,mid,hargs,List.append_assoc,List.singleton_append,outcome] using hfinish
      · have trace := NaturalRun.step test (NaturalRun.step empty hret)
        simpa only [ext,mid,hargs,List.append_assoc,List.singleton_append,List.nil_append,
          instructions,outcome,List.map_nil] using trace
  | succ fuel ih =>
    cases hf with
    | @cons _ item tail _ hpair htail =>
      let saved := caller::stack
      let w := bound.length
      let x := PhysicalFairWordProgram.digits w tape
      let suffix := tape.drop w
      let fword : Frame ℕ 78 := ⟨6,.r2,r⟩
      obtain ⟨ew,valueRoot,wordRep,hword⟩ := word_return (boolList_spine hb) fword saved tape
      let mid := heap++ew
      let readArgs := r.set .r2 valueRoot
      let fcmp : Frame ℕ 78 := ⟨7,.r3,readArgs⟩
      have keptBound : BoolList mid readArgs.a bound := by
        cases r
        exact boolList_extend hb ew
      have keptWord : BoolList mid readArgs.c x := by
        cases r
        exact wordRep
      obtain ⟨ec,bit,hflag,hcmp⟩ := reject_flag keptBound keptWord fcmp saved suffix
      let grown := mid++ec
      let tested := readArgs.set .r3 bit
      have t0 : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 5,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hpair]
      have t5 : tickNatural program (state heap r saved tape 5) =
          some ⟨state heap r (fword::saved) tape (wordLabel 8),[],0⟩ := rfl
      have t6 : tickNatural program (state mid readArgs saved suffix 6) =
          some ⟨state mid readArgs (fcmp::saved) suffix 15,[],0⟩ := rfl
      have testedRun : NaturalRun program (6*w+BinaryComparisonProgram.steps bound x+15)
          (state heap r saved tape 0) (x.map Event.request) (state grown tested saved suffix 7) := by
        have trace := NaturalRun.step t0 (NaturalRun.step t5 (join hword (NaturalRun.step t6 hcmp)))
        convert trace using 1 <;> first | rfl | omega | (simp only [List.nil_append,List.append_nil]; rfl)
      cases reject : (lessEqual bound x).1 with
      | false =>
        have rejectRaw : (lessEqual bound (PhysicalFairWordProgram.digits bound.length tape)).1=false := reject
        have t7 : tickNatural program (state grown tested saved suffix 7) =
            some ⟨state grown tested saved suffix 12,[],0⟩ := by
          cases r
          simp [tested,readArgs,grown,state,tickNatural,program,Registers.get,Registers.set,tagBranch,hflag,reject]
        have wordHere : BoolList grown tested.c x := by
          cases r
          exact boolList_extend keptWord ec
        obtain ⟨hfinish,hret⟩ := finish wordHere false caller stack suffix
        let added : NaturalHeap := [.flag false,.pair tested.c grown.length]
        have hvalue : outcome bound (fuel+1) tape = ⟨x,false,x,suffix⟩ := by
          simp only [outcome,rejectRaw,Bool.false_eq_true,ite_false]
          rfl
        refine ⟨ew++ec++added,grown.length+1,?_,?_⟩
        · rw [hvalue]
          have rep := preserve_observation hfinish (b := ⟨x,false,x,suffix⟩) rfl rfl
          simpa only [added,grown,mid,List.append_assoc] using rep
        · have trace := join testedRun (NaturalRun.step t7 hret)
          rw [hvalue]
          simp only [instructions,rejectRaw,Bool.false_eq_true,ite_false,Nat.add_zero]
          dsimp only [x,w] at trace
          convert trace using 1 <;> first | rfl | omega |
            (simp only [added,grown,mid,List.append_assoc,List.append_nil] <;> rfl)
      | true =>
        have rejectRaw : (lessEqual bound (PhysicalFairWordProgram.digits bound.length tape)).1=true := reject
        let args := tested.set .r1 tail
        let frame : Frame ℕ 78 := ⟨4,.r3,args⟩
        have t7 : tickNatural program (state grown tested saved suffix 7) =
            some ⟨state grown tested saved suffix 8,[],0⟩ := by
          cases r
          simp [tested,readArgs,grown,state,tickNatural,program,Registers.get,Registers.set,tagBranch,hflag,reject]
        have t8 : tickNatural program (state grown tested saved suffix 8) =
            some ⟨state grown args saved suffix 9,[],0⟩ := by
          have hp : grown[r.b]?=some (.pair item tail) := lookup_extend (lookup_extend hpair ew) ec
          cases r
          simp [args,tested,readArgs,state,tickNatural,program,Registers.get,Registers.set,hp]
        have t9 : tickNatural program (state grown args saved suffix 9) =
            some ⟨state grown args (frame::saved) suffix 0,[],0⟩ := rfl
        have boundHere : BoolList grown args.a bound := by
          cases r
          exact boolList_extend keptBound ec
        have restFuel : IndexSpine grown args.b fuel := by
          cases r
          exact indexSpine_extend (indexSpine_extend htail ew) ec
        obtain ⟨ee,root,hrep,again⟩ := ih boundHere restFuel frame saved suffix
        let more := outcome bound fuel suffix
        have ret : tickNatural program (state (grown++ee) (args.set .r3 root) saved more.suffix 4) =
            some ⟨state (grown++ee) (caller.saved.set caller.destination root)
              stack more.suffix caller.continuation,[],0⟩ := by
          cases r
          simp [args,tested,readArgs,saved,state,tickNatural,program,Registers.get,Registers.set]
        have hvalue : outcome bound (fuel+1) tape = {more with requests := x++more.requests} := by
          simp only [outcome,rejectRaw,ite_true]
          rfl
        refine ⟨ew++ec++ee,root,?_,?_⟩
        · rw [hvalue]
          have rep := preserve_observation hrep (b := {more with requests := x++more.requests}) rfl rfl
          simpa only [grown,mid,List.append_assoc] using rep
        · have trace := join testedRun (NaturalRun.step t7 (NaturalRun.step t8
            (NaturalRun.step t9 (join again (.step ret (.done _))))))
          rw [hvalue]
          simp only [instructions,rejectRaw,ite_true,List.map_append]
          dsimp only [x,w,suffix] at trace
          convert trace using 1 <;> first | rfl | omega |
            (simp only [grown,mid,List.append_assoc,List.append_nil,List.nil_append] <;> rfl)

theorem natural_draw {heap : NaturalHeap} {r : Registers ℕ} {fuel : ℕ} {bound : Bits}
    (hb : BoolList heap r.a bound) (hf : IndexSpine heap r.b fuel) (tape : Bits) :
    let observed := outcome bound fuel tape
    ∃ ext root, ResultAt (heap++ext) root observed ∧
      NaturalRun program (instructions bound fuel tape+1) (state heap r [] tape 18)
        (observed.requests.map Event.request) (state (heap++ext) (r.set .r3 root) [] observed.suffix 19) := by
  let frame : Frame ℕ 78 := ⟨19,.r3,r⟩
  obtain ⟨ext,root,rep,body⟩ := draw_return hb hf frame [] tape
  have call : tickNatural program (state heap r [] tape 18) =
      some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,rep,.step call body⟩

private theorem at_entry (s : NaturalState 78) (hp : s.pc=18) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 18 := by
  cases s
  simp_all [state]

theorem physical_draw {H A fuel : ℕ} {bound : Bits} (initial : BitState 78)
    (bounded : initial.Bounded H A) (hp : initial.pc=18) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (hb : BoolList (eraseState initial).heap (eraseState initial).registers.a bound)
    (hf : IndexSpine (eraseState initial).heap (eraseState initial).registers.b fuel) :
    let observed := outcome bound fuel initial.source
    ∃ charge out, Run program (instructions bound fuel initial.source+1) charge initial (observed.requests.map Event.request) out ∧
      ResultAt (eraseState out).heap (eraseState out).registers.d observed ∧
      out.source=observed.suffix ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=19 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 78 H A (instructionBound bound.length fuel) := by
  let old := eraseState initial
  let observed := outcome bound fuel initial.source
  obtain ⟨ext,root,hrep,hbody⟩ := natural_draw hb hf old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] observed.suffix 19
  have trace : NaturalRun program (instructions bound fuel initial.source+1) old
      (observed.requests.map Event.request) final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final = none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have hsteps := instructions_le bound fuel initial.source
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.PhysicalBoundedDrawProgram
