import DirectedFlowCutGap.BinaryZeroProgram
import DirectedFlowCutGap.ReferenceProgramLabels
import DirectedFlowCutGap.ReferenceProgramStack

/-! A literal padded binary comparison. Recursive calls inspect the more
significant suffix first. Saved low-bit references are stored as a real pair;
zero tests handle unequal lengths without normalization or a value oracle. -/
namespace DirectedFlowCutGap.BinaryComparisonProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def zeroLabel (pc : Fin 9) : Fin 48 := ⟨pc.val+32,by omega⟩
def program : Program 48 := fun pc =>
  if pc.val=40 then .ret .r3
  else if h : 32 ≤ pc.val ∧ pc.val < 41 then
    ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val-32,by omega⟩)
  else match pc.val with
  | 0 => .branch .r0 1 47 47 5
  | 1 => .move .r0 .r1 2
  | 2 => .call 39 3 .r3
  | 3 => .branch .r3 47 21 20 47
  | 4 => .branch .r3 47 22 20 47
  | 5 => .branch .r1 6 47 47 8
  | 6 => .call 39 4 .r3
  | 8 => .field .r2 .r0 false 9
  | 9 => .field .r3 .r1 false 10
  | 10 => .make .r2 (.pair .r2 .r3) 11
  | 11 => .field .r0 .r0 true 12
  | 12 => .field .r1 .r1 true 13
  | 13 => .call 0 14 .r3
  | 14 => .branch .r3 15 23 23 47
  | 15 => .field .r0 .r2 false 16
  | 16 => .field .r1 .r2 true 17
  | 17 => .branch .r0 47 18 19 47
  | 18 => .branch .r1 47 20 21 47
  | 19 => .branch .r1 47 22 20 47
  | 20 => .make .r3 .nil 24
  | 21 => .make .r3 (.flag false) 24
  | 22 => .make .r3 (.flag true) 24
  | 23 => .ret .r3
  | 24 => .ret .r3
  | 30 => .call 0 31 .r3
  | 31 => .branch .r3 44 44 45 47
  | 44 => .make .r3 (.flag true) 46
  | 45 => .make .r3 (.flag false) 46
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 48)) (source : Bits) (pc : Fin 48) : NaturalState 48 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def tag : Ordering → Cell ℕ
  | .lt => .flag false
  | .eq => .nil
  | .gt => .flag true

def choose (less equal : Bool) : Ordering := if less then .lt else if equal then .eq else .gt
def order (xs ys : Bits) : Ordering := choose (BinaryArithmetic.compare xs ys).less (BinaryArithmetic.compare xs ys).equal
def lowOrder (x y : Bool) : Ordering := if x==y then .eq else if x then .gt else .lt

theorem order_nil (ys : Bits) : order [] ys=if (isZero ys).1 then .eq else .lt := by
  cases h : (isZero ys).1 <;> simp [order,choose,BinaryArithmetic.compare,h]
theorem order_cons_nil (x : Bool) (xs : Bits) :
    order (x::xs) []=if (isZero (x::xs)).1 then .eq else .gt := by
  cases h : (isZero (x::xs)).1 <;> simp [order,choose,BinaryArithmetic.compare,h]
theorem order_cons (x y : Bool) (xs ys : Bits) :
    order (x::xs) (y::ys)=if order xs ys=.eq then lowOrder x y else order xs ys := by
  cases hl : (BinaryArithmetic.compare xs ys).less <;> cases he : (BinaryArithmetic.compare xs ys).equal <;>
    cases x <;> cases y <;> simp [order,choose,BinaryArithmetic.compare,lowOrder,hl,he]

def finishSteps (r : Ordering) : ℕ := if r=.eq then 7 else 2
def finishCells (r : Ordering) : ℕ := if r=.eq then 1 else 0
def steps : Bits → Bits → ℕ
  | [],ys => BinaryZeroProgram.steps ys+8
  | x::xs,[] => BinaryZeroProgram.steps (x::xs)+8
  | _::xs,_::ys => 8+steps xs ys+finishSteps (order xs ys)
def cells : Bits → Bits → ℕ
  | [],_ => 2
  | _::_,[] => 2
  | _::xs,_::ys => 1+cells xs ys+finishCells (order xs ys)

theorem steps_bound (xs ys : Bits) : steps xs ys ≤ 16*(xs.length+ys.length+1) := by
  induction xs generalizing ys with
  | nil => have h := BinaryZeroProgram.steps_bound ys; simp only [steps,List.length_nil];omega
  | cons x xs ih =>
    cases ys with
    | nil => have h := BinaryZeroProgram.steps_bound (x::xs); simp only [steps,List.length_nil];omega
    | cons y ys =>
      have h := ih ys
      have hf : finishSteps (order xs ys) ≤ 7 := by unfold finishSteps;split <;> omega
      simp only [steps,List.length_cons]
      omega

theorem cells_bound (xs ys : Bits) : cells xs ys ≤ xs.length+ys.length+2 := by
  induction xs generalizing ys with
  | nil => simp [cells]
  | cons x xs ih =>
    cases ys with
    | nil => simp [cells]
    | cons y ys =>
      have h := ih ys
      have hf : finishCells (order xs ys) ≤ 1 := by unfold finishCells;split <;> omega
      simp only [cells,List.length_cons]
      omega

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc ≠ .halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  fin_cases pc <;> simp_all [program,zeroLabel,BinaryZeroProgram.program]

theorem run_append {s u v : NaturalState 48} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The relocated zero program is a genuine callable body: its former halt
returns through the caller below the zero program's own saved frame. -/
theorem zero_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 48) (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 39) []
      (state (heap++[.flag (isZero word).1]) (next+1)
        saved.a saved.b saved.c next stack source pc) := by
  have z0 := BinaryZeroProgram.zero_return input next b c d hn ⟨a,b,c,d⟩ 8 [] source
  have z1 := ReferenceProgramLabels.run zeroLabel BinaryZeroProgram.program program zero_slots z0
  have z2 := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) z1
  have z : NaturalRun program (BinaryZeroProgram.steps word)
      (state heap next a b c d (⟨40,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 32) []
      (state (heap++[.flag (isZero word).1]) (next+1) a b c next
        (⟨pc,.r3,saved⟩::stack) source 40) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryZeroProgram.state,zeroLabel,state] using z2
  have t39 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 39)=
      some ⟨state heap next a b c d (⟨40,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 32,[],0⟩ := by
    simp [tickNatural,program,state,ReferenceProgramLabels.instruction,zeroLabel,BinaryZeroProgram.program]
  have t40 : tickNatural program
      (state (heap++[.flag (isZero word).1]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 40)=
      some ⟨state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  simpa [Nat.add_assoc] using NaturalRun.step t39 (run_append z (.step t40 (.done _)))

/-- Equal higher suffixes are resolved by actual saved low bits; a strict
higher result is returned without allocating or inspecting the low bits. -/
theorem finish_return {heap : NaturalHeap} {a b pair result xRoot yRoot : ℕ}
    (r : Ordering) (x y : Bool) (next : ℕ) (hn : next=heap.length)
    (hp : heap[pair]?=some (.pair xRoot yRoot))
    (hx : heap[xRoot]?=some (.flag x)) (hy : heap[yRoot]?=some (.flag y))
    (hr : heap[result]?=some (tag r)) (saved : Registers ℕ) (pc : Fin 48)
    (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root, ext.length=finishCells r ∧
      NaturalRun program (finishSteps r)
        (state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 14) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (tag (if r=.eq then lowOrder x y else r)) := by
  cases r with
  | lt | gt =>
    have t14 : tickNatural program
        (state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 14)=
        some ⟨state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 23,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hr,tag,tagBranch]
    have t23 : tickNatural program
        (state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 23)=
        some ⟨state heap next saved.a saved.b saved.c result stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    refine ⟨[],result,rfl,?_,?_⟩
    · simpa [finishSteps,state] using NaturalRun.step t14 (.step t23 (.done _))
    · simpa [tag] using hr
  | eq =>
    have t14 : tickNatural program
        (state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 14)=
        some ⟨state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 15,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hr,tag,tagBranch]
    have t15 : tickNatural program
        (state heap next a b pair result (⟨pc,.r3,saved⟩::stack) source 15)=
        some ⟨state heap next xRoot b pair result (⟨pc,.r3,saved⟩::stack) source 16,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t16 : tickNatural program
        (state heap next xRoot b pair result (⟨pc,.r3,saved⟩::stack) source 16)=
        some ⟨state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source 17,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    let branch : Fin 48 := if x then 19 else 18
    let alloc : Fin 48 := if x==y then 20 else if x then 22 else 21
    have t17 : tickNatural program
        (state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source 17)=
        some ⟨state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source branch,[],0⟩ := by
      cases x <;> simp [tickNatural,program,state,Registers.get,hx,tagBranch,branch]
    have tb : tickNatural program
        (state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source branch)=
        some ⟨state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source alloc,[],0⟩ := by
      cases x <;> cases y <;> simp [tickNatural,program,state,Registers.get,hy,tagBranch,branch,alloc]
    have ta : tickNatural program
        (state heap next xRoot yRoot pair result (⟨pc,.r3,saved⟩::stack) source alloc)=
        some ⟨state (heap++[tag (lowOrder x y)]) (next+1) xRoot yRoot pair next (⟨pc,.r3,saved⟩::stack) source 24,[],0⟩ := by
      cases x <;> cases y <;>
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,alloc,lowOrder,tag]
    have t24 : tickNatural program
        (state (heap++[tag (lowOrder x y)]) (next+1) xRoot yRoot pair next (⟨pc,.r3,saved⟩::stack) source 24)=
        some ⟨state (heap++[tag (lowOrder x y)]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    refine ⟨[tag (lowOrder x y)],next,rfl,?_,?_⟩
    · exact .step t14 (.step t15 (.step t16 (.step t17 (.step tb (.step ta (.step t24 (.done _)))))))
    · simp [hn]

def allocPC : Ordering → Fin 48 | .lt => 21 | .eq => 20 | .gt => 22

theorem make_return (r : Ordering) (heap : NaturalHeap) (next a b c d : ℕ)
    (saved : Registers ℕ) (pc : Fin 48) (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program 2 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (allocPC r)) []
      (state (heap++[tag r]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have t : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (allocPC r))=
      some ⟨state (heap++[tag r]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 24,[],0⟩ := by
    cases r <;> simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,allocPC,tag]
  have ret : tickNatural program (state (heap++[tag r]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 24)=
      some ⟨state (heap++[tag r]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step t (.step ret (.done _))

/-- Every recursive low-bit pair and every comparison result cell is allocated
by the real instructions. The full caller and source are restored on return. -/
theorem compare_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 48)
    (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root, ext.length=cells xs ys ∧ NaturalRun program (steps xs ys)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (tag (order xs ys)) := by
  induction xs generalizing ys heap a b next c d saved pc stack with
  | nil =>
    cases left with
    | nil hnil =>
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
      have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
          some ⟨state heap next b b c d (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t2 : tickNatural program (state heap next b b c d (⟨pc,.r3,saved⟩::stack) source 2)=
          some ⟨state heap next b b c d (⟨3,.r3,⟨b,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 39,[],0⟩ := by
        simp [tickNatural,program,state]
      have z := zero_return right next b c d hn ⟨b,b,c,d⟩ 3 (⟨pc,.r3,saved⟩::stack) source
      have t3 : tickNatural program
          (state (heap++[.flag (isZero ys).1]) (next+1) b b c next (⟨pc,.r3,saved⟩::stack) source 3)=
          some ⟨state (heap++[.flag (isZero ys).1]) (next+1) b b c next
            (⟨pc,.r3,saved⟩::stack) source (allocPC (order [] ys)),[],0⟩ := by
        rw [order_nil]
        cases h : (isZero ys).1 <;> simp [tickNatural,program,state,Registers.get,hn,tagBranch,allocPC]
      have tail := make_return (order [] ys) (heap++[.flag (isZero ys).1]) (next+1) b b c next saved pc stack source
      refine ⟨[.flag (isZero ys).1,tag (order [] ys)],next+1,rfl,?_,?_⟩
      · have run := NaturalRun.step t0 (.step t1 (.step t2 (run_append z (.step t3 tail))))
        convert run using 1 <;> simp [steps,List.append_assoc,Nat.add_assoc]
      · simp [hn]
  | cons x xs ih =>
    cases ys with
    | nil =>
      cases right with
      | nil hnil =>
        cases left with
        | @cons a head tail x xs hp hf ht =>
          have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
              some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 5,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t5 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 5)=
              some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 6,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
          have t6 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 6)=
              some ⟨state heap next a b c d (⟨4,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 39,[],0⟩ := by
            simp [tickNatural,program,state]
          have z := zero_return (BoolList.cons hp hf ht) next b c d hn ⟨a,b,c,d⟩ 4 (⟨pc,.r3,saved⟩::stack) source
          have t4 : tickNatural program
              (state (heap++[.flag (isZero (x::xs)).1]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 4)=
              some ⟨state (heap++[.flag (isZero (x::xs)).1]) (next+1) a b c next
                (⟨pc,.r3,saved⟩::stack) source (allocPC (order (x::xs) [])),[],0⟩ := by
            rw [order_cons_nil]
            cases h : (isZero (x::xs)).1 <;> simp [tickNatural,program,state,Registers.get,hn,tagBranch,allocPC]
          have tailRun := make_return (order (x::xs) []) (heap++[.flag (isZero (x::xs)).1]) (next+1) a b c next saved pc stack source
          refine ⟨[.flag (isZero (x::xs)).1,tag (order (x::xs) [])],next+1,rfl,?_,?_⟩
          · have run := NaturalRun.step t0 (.step t5 (.step t6 (run_append z (.step t4 tailRun))))
            convert run using 1 <;> simp [steps,List.append_assoc,Nat.add_assoc]
          · simp [hn]
    | cons y ys =>
      cases left with
      | @cons a xHead xTail x xs hx hxf hxt =>
        cases right with
        | @cons b yHead yTail y ys hy hyf hyt =>
          let frame : Frame ℕ 48 := ⟨pc,.r3,saved⟩
          let more : NaturalHeap := [.pair xHead yHead]
          have t0 : tickNatural program (state heap next a b c d (frame::stack) source 0)=
              some ⟨state heap next a b c d (frame::stack) source 5,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hx,tagBranch]
          have t5 : tickNatural program (state heap next a b c d (frame::stack) source 5)=
              some ⟨state heap next a b c d (frame::stack) source 8,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hy,tagBranch]
          have t8 : tickNatural program (state heap next a b c d (frame::stack) source 8)=
              some ⟨state heap next a b xHead d (frame::stack) source 9,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hx]
          have t9 : tickNatural program (state heap next a b xHead d (frame::stack) source 9)=
              some ⟨state heap next a b xHead yHead (frame::stack) source 10,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hy]
          have t10 : tickNatural program (state heap next a b xHead yHead (frame::stack) source 10)=
              some ⟨state (heap++more) (next+1) a b next yHead (frame::stack) source 11,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,more]
          have t11 : tickNatural program (state (heap++more) (next+1) a b next yHead (frame::stack) source 11)=
              some ⟨state (heap++more) (next+1) xTail b next yHead (frame::stack) source 12,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hx more]
          have t12 : tickNatural program (state (heap++more) (next+1) xTail b next yHead (frame::stack) source 12)=
              some ⟨state (heap++more) (next+1) xTail yTail next yHead (frame::stack) source 13,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hy more]
          have t13 : tickNatural program (state (heap++more) (next+1) xTail yTail next yHead (frame::stack) source 13)=
              some ⟨state (heap++more) (next+1) xTail yTail next yHead
                (⟨14,.r3,⟨xTail,yTail,next,yHead⟩⟩::frame::stack) source 0,[],0⟩ := by
            simp [tickNatural,program,state]
          obtain ⟨ext,root,len,rec,hr⟩ := ih (boolList_extend hxt more) (boolList_extend hyt more)
            (next+1) next yHead (by simp [hn,more]) ⟨xTail,yTail,next,yHead⟩ 14 (frame::stack)
          have pair : (heap++more++ext)[next]?=some (.pair xHead yHead) :=
            lookup_extend (by simp [hn,more]) ext
          have hx' := lookup_extend (lookup_extend hxf more) ext
          have hy' := lookup_extend (lookup_extend hyf more) ext
          obtain ⟨last,lastRoot,lastLen,finish,tagged⟩ := finish_return (a:=xTail) (b:=yTail)
            (order xs ys) x y (next+1+ext.length) (by simp [hn,more,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]) pair hx' hy' hr saved pc stack source
          refine ⟨more++ext++last,lastRoot,?_,?_,?_⟩
          · simp [cells,more,len,lastLen,Nat.add_assoc,Nat.add_comm]
          · have body := run_append rec finish
            have run := NaturalRun.step t0 (.step t5 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 body)))))))
            convert run using 1 <;> simp [steps,more,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
            omega
          · simpa [order_cons,List.append_assoc] using tagged

def leFlag : Ordering → Bool | .gt => false | _ => true

theorem leFlag_order (xs ys : Bits) : leFlag (order xs ys)=(lessEqual xs ys).1 := by
  cases hl : (BinaryArithmetic.compare xs ys).less <;>
    cases he : (BinaryArithmetic.compare xs ys).equal <;>
    simp [leFlag,order,choose,lessEqual,hl,he]

theorem le_finish {heap : NaturalHeap} (next a b c d : ℕ)
    (r : Ordering) (hr : heap[d]?=some (tag r)) (source : Bits) :
    NaturalRun program 2 (state heap next a b c d [] source 31) []
      (state (heap++[.flag (leFlag r)]) (next+1) a b c next [] source 46) := by
  let dest : Fin 48 := if r=.gt then 45 else 44
  have t31 : tickNatural program (state heap next a b c d [] source 31)=
      some ⟨state heap next a b c d [] source dest,[],0⟩ := by
    cases r <;> simp [tickNatural,program,state,Registers.get,hr,tag,tagBranch,dest]
  have t44 : tickNatural program (state heap next a b c d [] source dest)=
      some ⟨state (heap++[.flag (leFlag r)]) (next+1) a b c next [] source 46,[],0⟩ := by
    cases r <;> simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,dest,leFlag]
  exact NaturalRun.step t31 (.step t44 (.done _))

/-- Both padded operands remain in the same append-only heap as the actual
comparison flag. No canonical-representation premise is needed. -/
theorem compare_high {xs ys : Bits} (initial : NaturalState 48)
    (pc0 : initial.pc=30) (hn : initial.next=initial.heap.length)
    (left : BoolList initial.heap initial.registers.a xs)
    (right : BoolList initial.heap initial.registers.b ys) (empty : initial.stack=[]) :
    ∃ final, NaturalRun program (steps xs ys+3) initial [] final ∧
      final.heap[final.registers.d]?=some (.flag (lessEqual xs ys).1) ∧
      BoolList final.heap initial.registers.a xs ∧
      BoolList final.heap initial.registers.b ys ∧
      final.registers.a=initial.registers.a ∧ final.registers.b=initial.registers.b ∧
      final.registers.c=initial.registers.c ∧ final.stack=[] ∧
      final.source=initial.source ∧ final.pc=46 ∧ final.next=final.heap.length ∧
      (∃ ext,final.heap=initial.heap++ext ∧ ext.length=cells xs ys+1) ∧
      tickNatural program final=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      obtain ⟨ext,root,len,rec,tagged⟩ := compare_return left right next c d hn ⟨a,b,c,d⟩ 31 [] source
      have top : tickNatural program (state heap next a b c d [] source 30)=
          some ⟨state heap next a b c d [⟨31,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      have dense : next+ext.length=(heap++ext).length := by simp [hn]
      have finish := le_finish (next+ext.length) a b c root (order xs ys) tagged source
      refine ⟨state (heap++ext++[.flag (leFlag (order xs ys))]) (next+ext.length+1)
        a b c (next+ext.length) [] source 46,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
      · simpa [state,Nat.add_assoc] using NaturalRun.step top (run_append rec finish)
      · simp [state,dense,leFlag_order]
      · exact boolList_extend (boolList_extend left ext) _
      · exact boolList_extend (boolList_extend right ext) _
      · simp [state,hn,Nat.add_assoc]
      · exact ⟨ext++[.flag (leFlag (order xs ys))],by simp [state,List.append_assoc],by simp [len]⟩
      · simp [tickNatural,program,state]

/-- The lower interpreter returns the same numerical comparison and retains
both original inputs and source. Its final halt is included in the charge. -/
theorem compare_bit {xs ys : Bits} {H B : ℕ} (initial : BitState 48)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=30)
    (hn : value initial.next=initial.heap.length)
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.b ys)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (steps xs ys+3) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (lessEqual xs ys).1) ∧
      ((lessEqual xs ys).1=true ↔ value xs ≤ value ys) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b ys ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=46 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs ys+1) ∧
      steps xs ys+3 ≤ 19*(xs.length+ys.length+1) ∧
      cells xs ys+1 ≤ xs.length+ys.length+3 ∧
      out.Bounded (H+(steps xs ys+3)) (B+(steps xs ys+3)) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 48 H B (steps xs ys+3) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,flag,lword,rword,_,_,_,stack,source,pc,_,ext,halt⟩ :=
    compare_high (eraseState initial) pc0 hn' left right empty'
  obtain ⟨charge,out,run,erase,bound,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,(lessEqual_spec xs ys).1,?_,?_,src.trans source,?_,?_,?_,?_,?_,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact flag
  · rw [erase];exact lword
  · rw [erase];exact rword
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc
  · rw [erase];exact ext
  · have := steps_bound xs ys;omega
  · have := cells_bound xs ys;omega

end DirectedFlowCutGap.BinaryComparisonProgram
