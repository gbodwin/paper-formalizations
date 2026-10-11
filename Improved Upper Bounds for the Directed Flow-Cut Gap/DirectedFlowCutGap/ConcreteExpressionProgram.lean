import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.BinaryBudgetExpression

/-! Construction of a finite instruction table for a static arithmetic
expression. All node calls, word literals and arithmetic calls are actual
immutable-reference instructions. The closed exports discharge all opcode
agreement premises for the constructed table. -/
namespace DirectedFlowCutGap.ConcreteExpressionProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

inductive Term where
  | input : Fin 3 → Term
  | nil : Term
  | cons : Bool → Term → Term
  | binary : Bool → Term → Term → Term

def literal : Bits → Term
  | [] => .nil
  | b::bs => .cons b (literal bs)
def translate : BinaryBudgetExpression.Expr → Term
  | .input i => .input i
  | .literal bs => literal bs
  | .plus a b => .binary false (translate a) (translate b)
  | .times a b => .binary true (translate a) (translate b)

def evaluate (inputs : Fin 3 → Bits) : Term → Bits
  | .input i => inputs i
  | .nil => []
  | .cons b t => b::evaluate inputs t
  | .binary multiply a b => if multiply then
      (mul (evaluate inputs a) (evaluate inputs b)).1 else
      (add false (evaluate inputs a) (evaluate inputs b)).1

def size : Term → ℕ
  | .input _ => 1
  | .nil => 2
  | .cons _ t => 4+size t
  | .binary _ a b => 6+size a+size b

theorem size_pos (t : Term) : 0 < size t := by cases t <;> simp [size]

def label {C : ℕ} (hC : 0 < C) (n : ℕ) : Fin C := ⟨n%C,Nat.mod_lt n hC⟩
def inputReg (i : Fin 3) : Reg := if i.val=0 then .r0 else if i.val=1 then .r1 else .r2

/-- Every target is a literal control label. Bounds proved at the final table
ensure the modular constructor never wraps a used expression target. -/
def block {C : ℕ} (hC : 0 < C) : Term → ℕ → ℕ → Instruction C
  | .input i,base,pc => if pc=base then .ret (inputReg i) else .halt
  | .nil,base,pc => if pc=base then .make .r3 .nil (label hC (base+1))
      else if pc=base+1 then .ret .r3 else .halt
  | .cons bit t,base,pc => if pc < base+4 then match pc-base with
      | 0 => .call (label hC (base+4)) (label hC (base+1)) .r3
      | 1 => .make .r0 (.flag bit) (label hC (base+2))
      | 2 => .make .r3 (.pair .r0 .r3) (label hC (base+3))
      | _ => .ret .r3
      else block hC t (base+4) pc
  | .binary multiply a b,base,pc => if pc < base+6 then match pc-base with
      | 0 => .call (label hC (base+6)) (label hC (base+1)) .r3
      | 1 => .call (label hC (base+6+size a)) (label hC (base+2)) .r2
      | 2 => .move .r0 .r3 (label hC (base+3))
      | 3 => .move .r1 .r2 (label hC (base+4))
      | 4 => .call (label hC (if multiply then 94 else 60)) (label hC (base+5)) .r3
      | _ => .ret .r3
      else if pc < base+6+size a then block hC a (base+6) pc
      else block hC b (base+6+size a) pc

def capacity (t : Term) : ℕ := 96+size t+2
theorem capacity_pos (t : Term) : 0 < capacity t := by dsimp [capacity];omega

def mathLabel (t : Term) (pc : Fin 96) : Fin (capacity t) := label (capacity_pos t) pc.val

def program (t : Term) : Program (capacity t) := fun pc =>
  if pc.val=95 then .ret .r3
  else if h : pc.val < 96 then
    ReferenceProgramLabels.instruction (mathLabel t) (BinaryMultiplicationProgram.program ⟨pc.val,h⟩)
  else if pc.val=96+size t then
    .call (label (capacity_pos t) 96) (label (capacity_pos t) (96+size t+1)) .r3
  else if pc.val=96+size t+1 then .halt
  else block (capacity_pos t) t 96 pc.val

def Agree {C : ℕ} (hC : 0 < C) (p : Program C) (t : Term) (base : ℕ) : Prop :=
  ∀ i, i < size t → p (label hC (base+i))=block hC t base (base+i)

theorem program_agree (t : Term) : Agree (capacity_pos t) (program t) t 96 := by
  intro i hi
  have hlt : 96+i < capacity t := by dsimp [capacity];omega
  simp [program,label,Nat.mod_eq_of_lt hlt,show 96+i ≠ 95 by omega,
    show ¬ 96+i < 96 by omega,ne_of_lt hi,
    show 96+i ≠ 96+size t+1 by omega]

theorem agree_cons {C : ℕ} {hC : 0 < C} {p : Program C} {bit : Bool} {t : Term} {base : ℕ}
    (h : Agree hC p (.cons bit t) base) : Agree hC p t (base+4) := by
  intro i hi
  have hh := h (4+i) (by simp [size];omega)
  simpa [block,show ¬ base+(4+i) < base+4 by omega,Nat.add_assoc] using hh

theorem agree_left {C : ℕ} {hC : 0 < C} {p : Program C} {m : Bool} {a b : Term} {base : ℕ}
    (h : Agree hC p (.binary m a b) base) : Agree hC p a (base+6) := by
  intro i hi
  have hh := h (6+i) (by simp [size];omega)
  simpa [block,show ¬ base+(6+i) < base+6 by omega,
    hi,Nat.add_assoc] using hh

theorem agree_right {C : ℕ} {hC : 0 < C} {p : Program C} {m : Bool} {a b : Term} {base : ℕ}
    (h : Agree hC p (.binary m a b) base) : Agree hC p b (base+6+size a) := by
  intro i hi
  have hh := h (6+size a+i) (by simp [size];omega)
  simpa [block,show ¬ base+(6+size a+i) < base+6 by omega,
    show ¬ base+(6+size a+i) < base+6+size a by omega,Nat.add_assoc] using hh

theorem evaluate_literal (inputs : Fin 3 → Bits) (xs : Bits) : evaluate inputs (literal xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [literal,evaluate,ih]

theorem evaluate_translate (inputs : Fin 3 → Bits) (e : BinaryBudgetExpression.Expr) :
    evaluate inputs (translate e)=(BinaryBudgetExpression.evaluate inputs e).1 := by
  induction e with
  | input i => simp [translate,evaluate,BinaryBudgetExpression.evaluate,BinaryBudgetExpression.copy_spec]
  | literal xs => simp [translate,evaluate_literal,BinaryBudgetExpression.evaluate,BinaryBudgetExpression.copy_spec]
  | plus a b ha hb => simp [translate,evaluate,BinaryBudgetExpression.evaluate,ha,hb]
  | times a b ha hb => simp [translate,evaluate,BinaryBudgetExpression.evaluate,ha,hb]

def embed {C D : ℕ} (hC : 0 < C) (pc : Fin D) : Fin C := label hC pc.val

theorem program_add_slots (t : Term) (pc : Fin 64) (h : BinaryAdditionProgram.program pc ≠ .halt) :
    program t (embed (capacity_pos t) pc)=ReferenceProgramLabels.instruction
      (embed (capacity_pos t)) (BinaryAdditionProgram.program pc) := by
  have hlt : pc.val < capacity t := by have := pc.isLt;dsimp [capacity];omega
  have hn : pc.val ≠ 95 := by have := pc.isLt;omega
  calc
    _ = ReferenceProgramLabels.instruction (mathLabel t)
        (BinaryMultiplicationProgram.program (BinaryMultiplicationProgram.addLabel pc)) := by
      simp [program,embed,label,Nat.mod_eq_of_lt hlt,hn,
        show pc.val < 96 by have := pc.isLt;omega,BinaryMultiplicationProgram.addLabel]
    _ = _ := by
      rw [BinaryMultiplicationProgram.addition_slots pc h]
      cases BinaryAdditionProgram.program pc <;> rfl

theorem program_mul_slots (t : Term) (pc : Fin 96) (h : BinaryMultiplicationProgram.program pc ≠ .halt) :
    program t (embed (capacity_pos t) pc)=ReferenceProgramLabels.instruction
      (embed (capacity_pos t)) (BinaryMultiplicationProgram.program pc) := by
  have hlt : pc.val < capacity t := by have := pc.isLt;dsimp [capacity];omega
  have hn : pc.val ≠ 95 := by
    intro he
    have eq : pc=95 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,embed,label,Nat.mod_eq_of_lt hlt,hn,pc.isLt]
  rfl

def state {C : ℕ} (heap : NaturalHeap) (next : ℕ) (regs : Registers ℕ)
    (stack : List (Frame ℕ C)) (source : Bits) (pc : Fin C) : NaturalState C :=
  ⟨heap,next,regs,stack,pc,source⟩

theorem append_run {C : ℕ} {p : Program C} {s u v : NaturalState C} {t k : ℕ} {events more : List Event}
    (h : NaturalRun p t s events u) (g : NaturalRun p k u more v) :
    NaturalRun p (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The constructed expression table's shared addition block returns into any
actual caller destination, with the caller's other registers restored. -/
theorem addition_return (t : Term) {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (dest : Reg)
    (pc : Fin (capacity t)) (stack : List (Frame ℕ (capacity t))) (source : Bits) :
    ∃ ext root, ext.length=BinaryAdditionProgram.cells false xs ys ∧
      NaturalRun (program t) (BinaryAdditionProgram.steps false xs ys+2)
        (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 60)) []
        (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys)
          (saved.set dest root) stack source pc) ∧ BoolList (heap++ext) root (add false xs ys).1 := by
  obtain ⟨ext,root,len,old,rep⟩ := BinaryAdditionProgram.add_return left right false next c d hn
    ⟨a,b,c,d⟩ 63 [] source
  have top : tickNatural BinaryAdditionProgram.program
      (BinaryAdditionProgram.state heap next a b c d [] source 60)=
      some ⟨BinaryAdditionProgram.state heap next a b c d [⟨63,.r3,⟨a,b,c,d⟩⟩] source 16,[],0⟩ := by
    simp [tickNatural,BinaryAdditionProgram.program,BinaryAdditionProgram.state]
  have relocated := ReferenceProgramLabels.run (embed (capacity_pos t)) BinaryAdditionProgram.program
    (program t) (program_add_slots t) (NaturalRun.step top old)
  have extra := ReferenceProgramStack.run (program t) (⟨pc,dest,saved⟩::stack) relocated
  have body : NaturalRun (program t) (BinaryAdditionProgram.steps false xs ys+1)
      (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 60)) []
      (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys) ⟨a,b,c,root⟩
        (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 63)) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      embed,BinaryAdditionProgram.state,BinaryAdditionProgram.entry,state] using extra
  have hlt : 63 < capacity t := by dsimp [capacity];omega
  have ret : tickNatural (program t)
      (state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys) ⟨a,b,c,root⟩
        (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 63))=
      some ⟨state (heap++ext) (next+BinaryAdditionProgram.cells false xs ys)
        (saved.set dest root) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,label,Nat.mod_eq_of_lt hlt,
      BinaryMultiplicationProgram.program,ReferenceProgramLabels.instruction,Registers.get]
  refine ⟨ext,root,len,?_,rep⟩
  simpa [Nat.add_assoc] using append_run body (NaturalRun.step ret (.done _))

/-- The concrete shared multiplication body has the same real arbitrary-
destination caller contract; no external compiler or arithmetic oracle is used. -/
theorem multiplication_return (t : Term) {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (dest : Reg)
    (pc : Fin (capacity t)) (stack : List (Frame ℕ (capacity t))) (source : Bits) :
    ∃ ext root, ext.length=BinaryMultiplicationProgram.cells xs ys ∧
      NaturalRun (program t) (BinaryMultiplicationProgram.steps xs ys+2)
        (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 94)) []
        (state (heap++ext) (next+BinaryMultiplicationProgram.cells xs ys)
          (saved.set dest root) stack source pc) ∧ BoolList (heap++ext) root (mul xs ys).1 := by
  obtain ⟨ext,root,len,old,rep⟩ := BinaryMultiplicationProgram.mul_return left right next c d hn
    ⟨a,b,c,d⟩ 95 [] source
  have top : tickNatural BinaryMultiplicationProgram.program
      (BinaryMultiplicationProgram.state heap next a b c d [] source 94)=
      some ⟨BinaryMultiplicationProgram.state heap next a b c d [⟨95,.r3,⟨a,b,c,d⟩⟩] source 64,[],0⟩ := by
    simp [tickNatural,BinaryMultiplicationProgram.program,BinaryMultiplicationProgram.state]
  have relocated := ReferenceProgramLabels.run (embed (capacity_pos t)) BinaryMultiplicationProgram.program
    (program t) (program_mul_slots t) (NaturalRun.step top old)
  have extra := ReferenceProgramStack.run (program t) (⟨pc,dest,saved⟩::stack) relocated
  have body : NaturalRun (program t) (BinaryMultiplicationProgram.steps xs ys+1)
      (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 94)) []
      (state (heap++ext) (next+BinaryMultiplicationProgram.cells xs ys) ⟨a,b,c,root⟩
        (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 95)) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      embed,BinaryMultiplicationProgram.state,state] using extra
  have hlt : 95 < capacity t := by dsimp [capacity];omega
  have ret : tickNatural (program t)
      (state (heap++ext) (next+BinaryMultiplicationProgram.cells xs ys) ⟨a,b,c,root⟩
        (⟨pc,dest,saved⟩::stack) source (label (capacity_pos t) 95))=
      some ⟨state (heap++ext) (next+BinaryMultiplicationProgram.cells xs ys)
        (saved.set dest root) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,label,Nat.mod_eq_of_lt hlt,Registers.get]
  refine ⟨ext,root,len,?_,rep⟩
  simpa [Nat.add_assoc] using append_run body (NaturalRun.step ret (.done _))

def arithmeticWord (m : Bool) (xs ys : Bits) : Bits := if m then (mul xs ys).1 else (add false xs ys).1
def arithmeticSteps (m : Bool) (xs ys : Bits) : ℕ :=
  if m then BinaryMultiplicationProgram.steps xs ys+2 else BinaryAdditionProgram.steps false xs ys+2
def arithmeticCells (m : Bool) (xs ys : Bits) : ℕ :=
  if m then BinaryMultiplicationProgram.cells xs ys else BinaryAdditionProgram.cells false xs ys

theorem arithmetic_return (t : Term) (m : Bool) {heap : NaturalHeap} {a b : ℕ} {xs ys : Bits}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (dest : Reg)
    (pc : Fin (capacity t)) (stack : List (Frame ℕ (capacity t))) (source : Bits) :
    ∃ ext root, ext.length=arithmeticCells m xs ys ∧
      NaturalRun (program t) (arithmeticSteps m xs ys)
        (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source
          (label (capacity_pos t) (if m then 94 else 60))) []
        (state (heap++ext) (next+arithmeticCells m xs ys)
          (saved.set dest root) stack source pc) ∧ BoolList (heap++ext) root (arithmeticWord m xs ys) := by
  cases m with
  | false => exact addition_return t left right next c d hn saved dest pc stack source
  | true => exact multiplication_return t left right next c d hn saved dest pc stack source

def runSteps (inputs : Fin 3 → Bits) : Term → ℕ
  | .input _ => 1
  | .nil => 2
  | .cons _ t => runSteps inputs t+4
  | .binary m a b => runSteps inputs a+runSteps inputs b+
      arithmeticSteps m (evaluate inputs a) (evaluate inputs b)+6
def runCells (inputs : Fin 3 → Bits) : Term → ℕ
  | .input _ => 0
  | .nil => 1
  | .cons _ t => runCells inputs t+2
  | .binary m a b => runCells inputs a+runCells inputs b+
      arithmeticCells m (evaluate inputs a) (evaluate inputs b)

def Inputs (heap : NaturalHeap) (a b c : ℕ) (inputs : Fin 3 → Bits) : Prop :=
  BoolList heap a (inputs 0) ∧ BoolList heap b (inputs 1) ∧ BoolList heap c (inputs 2)

theorem inputs_extend {heap : NaturalHeap} {a b c : ℕ} {inputs : Fin 3 → Bits}
    (h : Inputs heap a b c inputs) (extra : NaturalHeap) : Inputs (heap++extra) a b c inputs :=
  ⟨boolList_extend h.1 extra,boolList_extend h.2.1 extra,boolList_extend h.2.2 extra⟩

/-- The recursive proof below uses literal opcode agreement only. Every such
agreement in the closed compiler is discharged by the constructed table's
lookup lemmas; callers never supply an evaluator-correctness premise. -/
theorem node_return (whole : Term) (inputs : Fin 3 → Bits) (t : Term) (base : ℕ)
    (agree : Agree (capacity_pos whole) (program whole) t base)
    (heap : NaturalHeap) (next a b c d : ℕ) (hn : next=heap.length)
    (rep : Inputs heap a b c inputs) (saved : Registers ℕ) (dest : Reg)
    (pc : Fin (capacity whole)) (stack : List (Frame ℕ (capacity whole))) (source : Bits) :
    ∃ ext root, ext.length=runCells inputs t ∧
      NaturalRun (program whole) (runSteps inputs t)
        (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos whole) base)) []
        (state (heap++ext) (next+runCells inputs t) (saved.set dest root) stack source pc) ∧
      BoolList (heap++ext) root (evaluate inputs t) := by
  induction t generalizing base heap next a b c d saved dest pc stack with
  | input i =>
      have slot := agree 0 (by simp [size])
      simp [block] at slot
      let root := (⟨a,b,c,d⟩ : Registers ℕ).get (inputReg i)
      have tick : tickNatural (program whole)
          (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos whole) base))=
          some ⟨state heap next (saved.set dest root) stack source pc,[],0⟩ := by
        simp [tickNatural,state,slot,root]
      refine ⟨[],root,rfl,?_,?_⟩
      · simpa [runSteps,runCells] using NaturalRun.step tick (.done _)
      · fin_cases i
        · simpa [root,inputReg,Registers.get,evaluate] using rep.1
        · simpa [root,inputReg,Registers.get,evaluate] using rep.2.1
        · simpa [root,inputReg,Registers.get,evaluate] using rep.2.2
  | nil =>
      have s0 := agree 0 (by simp [size])
      have s1 := agree 1 (by simp [size])
      simp [block] at s0 s1
      have t0 : tickNatural (program whole)
          (state heap next ⟨a,b,c,d⟩ (⟨pc,dest,saved⟩::stack) source (label (capacity_pos whole) base))=
          some ⟨state (heap++[.nil]) (next+1) ⟨a,b,c,next⟩
            (⟨pc,dest,saved⟩::stack) source (label (capacity_pos whole) (base+1)),[],0⟩ := by
        simp [tickNatural,state,s0,allocateNatural,Recipe.cell,Registers.set]
      have t1 : tickNatural (program whole)
          (state (heap++[.nil]) (next+1) ⟨a,b,c,next⟩
            (⟨pc,dest,saved⟩::stack) source (label (capacity_pos whole) (base+1)))=
          some ⟨state (heap++[.nil]) (next+1) (saved.set dest next) stack source pc,[],0⟩ := by
        simp [tickNatural,state,s1,Registers.get]
      refine ⟨[.nil],next,rfl,.step t0 (.step t1 (.done _)),?_⟩
      apply BoolList.nil
      simp [hn]
  | cons bit t ih =>
      have s0 := agree 0 (by simp [size])
      have s1 := agree 1 (by simp [size];omega)
      have s2 := agree 2 (by simp [size];omega)
      have s3 := agree 3 (by simp [size];omega)
      simp [block] at s0 s1 s2 s3
      let frame : Frame ℕ (capacity whole) := ⟨pc,dest,saved⟩
      obtain ⟨ext,root,len,child,word⟩ := ih (base+4) (agree_cons agree) heap next a b c d hn rep
        ⟨a,b,c,d⟩ .r3 (label (capacity_pos whole) (base+1)) (frame::stack)
      let fresh := next+runCells inputs t
      have hf : fresh=(heap++ext).length := by simp [fresh,hn,len]
      have t0 : tickNatural (program whole)
          (state heap next ⟨a,b,c,d⟩ (frame::stack) source (label (capacity_pos whole) base))=
          some ⟨state heap next ⟨a,b,c,d⟩
            (⟨label (capacity_pos whole) (base+1),.r3,⟨a,b,c,d⟩⟩::frame::stack)
            source (label (capacity_pos whole) (base+4)),[],0⟩ := by
        simp [tickNatural,state,s0]
      have t1 : tickNatural (program whole)
          (state (heap++ext) fresh ⟨a,b,c,root⟩ (frame::stack) source (label (capacity_pos whole) (base+1)))=
          some ⟨state ((heap++ext)++[.flag bit]) (fresh+1) ⟨fresh,b,c,root⟩
            (frame::stack) source (label (capacity_pos whole) (base+2)),[],0⟩ := by
        simp [tickNatural,state,s1,allocateNatural,Recipe.cell,Registers.set]
      have t2 : tickNatural (program whole)
          (state ((heap++ext)++[.flag bit]) (fresh+1) ⟨fresh,b,c,root⟩
            (frame::stack) source (label (capacity_pos whole) (base+2)))=
          some ⟨state ((heap++ext)++[.flag bit,.pair fresh root]) (fresh+2)
            ⟨fresh,b,c,fresh+1⟩ (frame::stack) source (label (capacity_pos whole) (base+3)),[],0⟩ := by
        simp [tickNatural,state,s2,allocateNatural,Recipe.cell,Registers.get,Registers.set,
          List.append_assoc,Nat.add_assoc]
      have t3 : tickNatural (program whole)
          (state ((heap++ext)++[.flag bit,.pair fresh root]) (fresh+2)
            ⟨fresh,b,c,fresh+1⟩ (frame::stack) source (label (capacity_pos whole) (base+3)))=
          some ⟨state ((heap++ext)++[.flag bit,.pair fresh root]) (fresh+2)
            (saved.set dest (fresh+1)) stack source pc,[],0⟩ := by
        simp [tickNatural,state,s3,frame,Registers.get]
      refine ⟨ext++[.flag bit,.pair fresh root],fresh+1,?_,?_,?_⟩
      · simp [runCells,len]
      · have all := NaturalRun.step t0 (append_run child (.step t1 (.step t2 (.step t3 (.done _)))))
        simpa [runSteps,runCells,fresh,List.append_assoc,Nat.add_assoc] using all
      · change BoolList (heap++(ext++[.flag bit,.pair fresh root])) (fresh+1) (bit::evaluate inputs t)
        rw [← List.append_assoc]
        apply BoolList.cons (head := fresh) (tail := root)
        · rw [List.getElem?_append_right (by omega)];simp [hf]
        · simp [hf]
        · exact boolList_extend word _
  | binary m l r ihl ihr =>
      have s0 := agree 0 (by simp [size])
      have s1 := agree 1 (by simp [size];omega)
      have s2 := agree 2 (by simp [size];omega)
      have s3 := agree 3 (by simp [size];omega)
      have s4 := agree 4 (by simp [size];omega)
      have s5 := agree 5 (by simp [size];omega)
      simp [block] at s0 s1 s2 s3 s4 s5
      let frame : Frame ℕ (capacity whole) := ⟨pc,dest,saved⟩
      obtain ⟨ex,rx,lx,left,repX⟩ := ihl (base+6) (agree_left agree) heap next a b c d hn rep
        ⟨a,b,c,d⟩ .r3 (label (capacity_pos whole) (base+1)) (frame::stack)
      let h2 := heap++ex
      let n2 := next+runCells inputs l
      have hn2 : n2=h2.length := by simp [n2,h2,hn,lx]
      obtain ⟨ey,ry,ly,right,repY⟩ := ihr (base+6+size l) (agree_right agree) h2 n2 a b c rx hn2
        (inputs_extend rep ex) ⟨a,b,c,rx⟩ .r2 (label (capacity_pos whole) (base+2)) (frame::stack)
      let h3 := h2++ey
      let n3 := n2+runCells inputs r
      have hn3 : n3=h3.length := by simp [n3,h3,hn2,ly]
      have repX' : BoolList h3 rx (evaluate inputs l) := boolList_extend repX ey
      obtain ⟨ez,rz,lz,arith,repZ⟩ := arithmetic_return whole m repX' repY n3 ry rx hn3
        ⟨rx,ry,ry,rx⟩ .r3 (label (capacity_pos whole) (base+5)) (frame::stack) source
      have t0 : tickNatural (program whole)
          (state heap next ⟨a,b,c,d⟩ (frame::stack) source (label (capacity_pos whole) base))=
          some ⟨state heap next ⟨a,b,c,d⟩
            (⟨label (capacity_pos whole) (base+1),.r3,⟨a,b,c,d⟩⟩::frame::stack)
            source (label (capacity_pos whole) (base+6)),[],0⟩ := by
        simp [tickNatural,state,s0]
      have t1 : tickNatural (program whole)
          (state h2 n2 ⟨a,b,c,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+1)))=
          some ⟨state h2 n2 ⟨a,b,c,rx⟩
            (⟨label (capacity_pos whole) (base+2),.r2,⟨a,b,c,rx⟩⟩::frame::stack)
            source (label (capacity_pos whole) (base+6+size l)),[],0⟩ := by
        simp [tickNatural,state,s1]
      have t2 : tickNatural (program whole)
          (state h3 n3 ⟨a,b,ry,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+2)))=
          some ⟨state h3 n3 ⟨rx,b,ry,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+3)),[],0⟩ := by
        simp [tickNatural,state,s2,Registers.get,Registers.set]
      have t3 : tickNatural (program whole)
          (state h3 n3 ⟨rx,b,ry,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+3)))=
          some ⟨state h3 n3 ⟨rx,ry,ry,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+4)),[],0⟩ := by
        simp [tickNatural,state,s3,Registers.get,Registers.set]
      have t4 : tickNatural (program whole)
          (state h3 n3 ⟨rx,ry,ry,rx⟩ (frame::stack) source (label (capacity_pos whole) (base+4)))=
          some ⟨state h3 n3 ⟨rx,ry,ry,rx⟩
            (⟨label (capacity_pos whole) (base+5),.r3,⟨rx,ry,ry,rx⟩⟩::frame::stack)
            source (label (capacity_pos whole) (if m then 94 else 60)),[],0⟩ := by
        simp [tickNatural,state,s4]
      have t5 : tickNatural (program whole)
          (state (h3++ez) (n3+arithmeticCells m (evaluate inputs l) (evaluate inputs r))
            ⟨rx,ry,ry,rz⟩ (frame::stack) source (label (capacity_pos whole) (base+5)))=
          some ⟨state (h3++ez) (n3+arithmeticCells m (evaluate inputs l) (evaluate inputs r))
            (saved.set dest rz) stack source pc,[],0⟩ := by
        simp [tickNatural,state,s5,frame,Registers.get]
      refine ⟨ex++ey++ez,rz,?_,?_,?_⟩
      · simp [runCells,lx,ly,lz,Nat.add_assoc]
      · have all := NaturalRun.step t0 (append_run left (.step t1
            (append_run right (.step t2 (.step t3 (.step t4 (append_run arith (.step t5 (.done _)))))))))
        convert all using 1 <;> simp [runSteps,runCells,n2,n3,h2,h3,List.append_assoc,Nat.add_assoc]
      · simpa [evaluate,arithmeticWord,h2,h3,List.append_assoc] using repZ

def entry (t : Term) : Fin (capacity t) := label (capacity_pos t) (96+size t)
def exit (t : Term) : Fin (capacity t) := label (capacity_pos t) (96+size t+1)

theorem program_entry (t : Term) : program t (entry t)=
    .call (label (capacity_pos t) 96) (exit t) .r3 := by
  have h : 96+size t < capacity t := by dsimp [capacity];omega
  simp [program,entry,label,Nat.mod_eq_of_lt h,show 96+size t ≠ 95 by omega,
    show ¬ 96+size t < 96 by omega,exit]

theorem program_exit (t : Term) : program t (exit t)=.halt := by
  have h : 96+size t+1 < capacity t := by dsimp [capacity];omega
  simp [program,exit,label,Nat.mod_eq_of_lt h,show 96+size t+1 ≠ 95 by omega,
    show ¬ 96+size t+1 < 96 by omega]

/-- Closed, concrete compiler correctness: the caller supplies only its three
stored input words. Opcode agreement and all recursive frames are internal. -/
theorem evaluate_high (t : Term) (inputs : Fin 3 → Bits) (initial : NaturalState (capacity t))
    (pc0 : initial.pc=entry t) (dense : initial.next=initial.heap.length)
    (rep : Inputs initial.heap initial.registers.a initial.registers.b initial.registers.c inputs)
    (frames : initial.stack=[]) :
    ∃ final, NaturalRun (program t) (runSteps inputs t+1) initial [] final ∧
      BoolList final.heap final.registers.d (evaluate inputs t) ∧
      Inputs final.heap initial.registers.a initial.registers.b initial.registers.c inputs ∧
      final.source=initial.source ∧ final.pc=exit t ∧ final.stack=[] ∧
      final.registers.a=initial.registers.a ∧ final.registers.b=initial.registers.b ∧
      final.registers.c=initial.registers.c ∧ final.next=final.heap.length ∧
      (∃ ext, final.heap=initial.heap++ext ∧ ext.length=runCells inputs t) ∧
      tickNatural (program t) final=none := by
  cases initial with
  | mk heap next regs st pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 dense rep frames
          subst pc
          subst st
          obtain ⟨ext,root,len,run,word⟩ := node_return t inputs t 96 (program_agree t)
            heap next a b c d dense rep ⟨a,b,c,d⟩ .r3 (exit t) [] source
          have top : tickNatural (program t) (state heap next ⟨a,b,c,d⟩ [] source (entry t))=
              some ⟨state heap next ⟨a,b,c,d⟩ [⟨exit t,.r3,⟨a,b,c,d⟩⟩]
                source (label (capacity_pos t) 96),[],0⟩ := by
            simp [tickNatural,state,program_entry]
          refine ⟨state (heap++ext) (next+runCells inputs t) ⟨a,b,c,root⟩ [] source (exit t),
            ?_,word,inputs_extend rep ext,rfl,rfl,rfl,rfl,rfl,rfl,?_,⟨ext,rfl,len⟩,?_⟩
          · simpa [state,Registers.set] using NaturalRun.step top run
          · simp [state,dense,len]
          · simp [tickNatural,state,program_exit]

/-- The same compiled instruction execution in the binary-reference machine,
including its terminal attempt. The complete cost is tied to this output. -/
theorem evaluate_bit (t : Term) (inputs : Fin 3 → Bits) {H B : ℕ}
    (initial : BitState (capacity t)) (bounded : initial.Bounded H B)
    (pc0 : initial.pc=entry t) (dense : value initial.next=initial.heap.length)
    (rep : Inputs (eraseState initial).heap (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c inputs)
    (frames : initial.stack=[]) :
    ∃ charge out, Run (program t) (runSteps inputs t+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (evaluate inputs t) ∧
      Inputs (eraseState out).heap (eraseState initial).registers.a
        (eraseState initial).registers.b (eraseState initial).registers.c inputs ∧
      out.source=initial.source ∧ out.pc=exit t ∧ out.stack=[] ∧
      value out.next=out.heap.length ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=runCells inputs t) ∧
      out.Bounded (H+(runSteps inputs t+1)) (B+(runSteps inputs t+1)) ∧
      (attempt (program t) out).result=none ∧
      charge+(attempt (program t) out).operations ≤
        completeBound (capacity t) H B (runSteps inputs t+1) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have frames' : (eraseState initial).stack=[] := by simp [eraseState,State.map,frames]
  obtain ⟨final,high,word,old,src,pc,stack,_,_,_,hn,ext,halt⟩ :=
    evaluate_high t inputs (eraseState initial) pc0 dense' rep frames'
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt (program t) out).result=none := by
    rw [attempt_result]
    have obs := tick_refines (program t) out
    rw [erase,halt] at obs
    cases ht : tick (program t) out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,?_,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact word
  · rw [erase];exact old
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact hn
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

end DirectedFlowCutGap.ConcreteExpressionProgram
