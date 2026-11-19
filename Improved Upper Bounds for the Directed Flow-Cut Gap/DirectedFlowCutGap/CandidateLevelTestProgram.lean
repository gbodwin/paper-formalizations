import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.ConcreteExpressionProgram
import DirectedFlowCutGap.BinaryComparisonProgram

/-!
# Threshold implication for one candidate cell

Equal points require a descending threshold. Distinct points require
the source level to equal the target level plus the nonnegative shift.
Both tests run on the stored binary words, including padded ones.
-/

namespace DirectedFlowCutGap.CandidateLevelTestProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def addLabel (pc : Fin 64) : Fin 144 := ⟨pc.val+32,by omega⟩
def compareLabel (pc : Fin 48) : Fin 144 := ⟨pc.val+96,by omega⟩

def program : Program 144 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .branch .r3 31 1 8 31
    | 1 => .call 12 2 .r1
    | 2 => .call 20 3 .r3
    | 3 => .branch .r3 10 11 11 31
    | 8 => .call 20 9 .r3
    | 9 => .branch .r3 10 11 10 31
    | 10 => .make .r3 (.flag true) 16
    | 11 => .make .r3 (.flag false) 16
    | 12 => .move .r0 .r1 13
    | 13 => .move .r1 .r2 (addLabel 60)
    | 20 => .call (compareLabel 0) (compareLabel 47) .r3
    | _ => .halt
  else if h : pc.val<96 then
    if pc.val=95 then .ret .r3
    else ReferenceProgramLabels.instruction addLabel (BinaryAdditionProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=143 then .ret .r3
  else ReferenceProgramLabels.instruction compareLabel
    (BinaryComparisonProgram.program ⟨pc.val-96,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 144))
    (tape : Bits) (pc : Fin 144) : NaturalState 144 := ⟨heap,heap.length,r,stack,pc,tape⟩

def delta (same : Bool) (b shift : Bits) : Bits := if same then b else (add false b shift).1

def answer (same : Bool) (a b shift : Bits) : Bool :=
  match BinaryComparisonProgram.order a (delta same b shift) with
  | .eq => true
  | .lt => false
  | .gt => same

theorem order_eq_ite (a b : Bits) : BinaryComparisonProgram.order a b =
    if value a<value b then .lt else if value a=value b then .eq else .gt := by
  have spec := compare_spec a b
  simp only [BinaryComparisonProgram.order,BinaryComparisonProgram.choose,spec.1,spec.2.1]

theorem answer_spec (same : Bool) (a b shift : Bits) : answer same a b shift=true ↔
    (same=true ∧ value b≤value a) ∨ value a=value b+value shift := by
  cases same
  · have num : value (delta false b shift)=value b+value shift := by
      simpa [delta] using (add_spec false b shift).1
    rw [answer,order_eq_ite,num]
    by_cases lt : value a<value b+value shift
    · have neq : value a≠value b+value shift := by omega
      simp [lt,neq]
    · by_cases eq : value a=value b+value shift <;> simp [lt,eq]
  · rw [answer,order_eq_ite]
    simp only [delta,ite_true,true_and]
    by_cases lt : value a<value b
    · have nle : ¬value b≤value a := by omega
      have neq : value a≠value b+value shift := by omega
      simp [lt,nle,neq]
    · have le : value b≤value a := by omega
      by_cases eq : value a=value b <;> simp [lt,le,eq]

def prepareSteps (same : Bool) (b shift : Bits) : ℕ :=
  if same then 1 else BinaryAdditionProgram.steps false b shift+6

def steps (same : Bool) (a b shift : Bits) : ℕ :=
  prepareSteps same b shift+BinaryComparisonProgram.steps a (delta same b shift)+5

theorem steps_le (same : Bool) (a b shift : Bits) : steps same a b shift ≤
    64*(a.length+b.length+shift.length+2) := by
  have hc := BinaryComparisonProgram.steps_bound a (delta same b shift)
  have ha := BinaryAdditionProgram.steps_bound false b shift
  have hm := (add_spec false b shift).2.1
  have hmax : max b.length shift.length≤b.length+shift.length := max_le (by omega) (by omega)
  cases same <;> simp only [steps,prepareSteps,delta,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

private theorem add_slots (pc : Fin 64) (h : BinaryAdditionProgram.program pc ≠ .halt) :
    program (addLabel pc) = ReferenceProgramLabels.instruction addLabel (BinaryAdditionProgram.program pc) := by
  by_cases hp : pc.val=63
  · have he : pc=63 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,addLabel,show ¬pc.val+32<32 by omega,show pc.val+32<96 by omega,show pc.val+32≠95 by omega]

private theorem compare_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc ≠ .halt) :
    program (compareLabel pc) =
      ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,compareLabel,show ¬pc.val+96<32 by omega,show ¬pc.val+96<96 by omega,
      show pc.val+96≠143 by omega]

private theorem prepare {heap : NaturalHeap} {r : Registers ℕ} {a b shift : Bits} {same : Bool}
    (left : BoolList heap r.a a) (right : BoolList heap r.b b) (gap : BoolList heap r.c shift)
    (flag : heap[r.d]?=some (.flag same)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ),BoolList (heap++ext) args.a a ∧
      BoolList (heap++ext) args.b (delta same b shift) ∧
      NaturalRun program (prepareSteps same b shift) (state heap r [] tape 0) []
        (state (heap++ext) args [] tape (if same then 8 else 2)) := by
  cases same
  · let args := (r.set .r0 r.b).set .r1 r.c
    let outer : Frame ℕ 144 := ⟨2,.r1,r⟩
    have setup : NaturalRun program 4 (state heap r [] tape 0) [] (state heap args [outer] tape (addLabel 60)) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,flag,tagBranch,args,outer]
    obtain ⟨ext,root,len,body,rep⟩ := BinaryAdditionProgram.add_return (a:=args.a) (b:=args.b)
      right gap false heap.length args.c args.d rfl args 63 [] tape
    have oldCall : tickNatural BinaryAdditionProgram.program
        (BinaryAdditionProgram.state heap heap.length args.a args.b args.c args.d [] tape 60) =
        some ⟨BinaryAdditionProgram.state heap heap.length args.a args.b args.c args.d
          [⟨63,.r3,args⟩] tape 16,[],0⟩ := by cases r; rfl
    let stop := state (heap++ext) (args.set .r3 root) [outer] tape (addLabel 63)
    have lift := ReferenceProgramLabels.run addLabel BinaryAdditionProgram.program program add_slots (.step oldCall body)
    have lift := ReferenceProgramStack.run program [outer] lift
    have run : NaturalRun program (BinaryAdditionProgram.steps false b shift+1)
        (state heap args [outer] tape (addLabel 60)) [] stop := by
      cases r
      simpa [stop,args,state,BinaryAdditionProgram.state,ReferenceProgramLabels.state,
        ReferenceProgramStack.state,Registers.set,len] using lift
    have ret : tickNatural program stop = some ⟨state (heap++ext) (r.set .r1 root) [] tape 2,[],0⟩ := by
      simp [stop,outer,state,program,addLabel,tickNatural,Registers.get,Registers.set]
    refine ⟨ext,r.set .r1 root,boolList_extend left ext,rep,?_⟩
    have full := append_run setup (append_run run (.step ret (.done _)))
    have counted : 4+(BinaryAdditionProgram.steps false b shift+1+1)=prepareSteps false b shift := by
      simp [prepareSteps]
      omega
    rw [← counted]
    exact full
  · have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [] tape 8,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,flag,tagBranch]
    exact ⟨[],r,by simpa using left,by simpa [delta] using right,by simpa [prepareSteps] using NaturalRun.step enter (.done _)⟩

private theorem compare_call {heap : NaturalHeap} {r : Registers ℕ} {a b : Bits}
    (left : BoolList heap r.a a) (right : BoolList heap r.b b) (tape : Bits) (pc next : Fin 144)
    (call : program pc=.call 20 next .r3) :
    ∃ ext root,(heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order a b)) ∧
      NaturalRun program (BinaryComparisonProgram.steps a b+3) (state heap r [] tape pc) []
        (state (heap++ext) (r.set .r3 root) [] tape next) := by
  obtain ⟨ext,root,len,body,rep⟩ := BinaryComparisonProgram.compare_return left right heap.length
    r.c r.d rfl r 47 [] tape
  let outer : Frame ℕ 144 := ⟨next,.r3,r⟩
  let inner : Frame ℕ 144 := ⟨compareLabel 47,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape pc)=some ⟨state heap r [outer] tape 20,[],0⟩ := by
    simp [state,outer,tickNatural,call]
  have callCore : tickNatural program (state heap r [outer] tape 20)=
      some ⟨state heap r [inner,outer] tape (compareLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (r.set .r3 root) [outer] tape (compareLabel 47)
  have lift := ReferenceProgramLabels.run compareLabel BinaryComparisonProgram.program program compare_slots body
  have lift := ReferenceProgramStack.run program [outer] lift
  have run : NaturalRun program (BinaryComparisonProgram.steps a b)
      (state heap r [inner,outer] tape (compareLabel 0)) [] stop := by
    cases r
    simpa [stop,inner,state,BinaryComparisonProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape next,[],0⟩ := by
    simp [stop,state,outer,program,compareLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (.step callCore (append_run run (.step ret (.done _))))⟩

theorem natural_test {heap : NaturalHeap} {r : Registers ℕ} {a b shift : Bits} {same : Bool}
    (left : BoolList heap r.a a) (right : BoolList heap r.b b) (gap : BoolList heap r.c shift)
    (flag : heap[r.d]?=some (.flag same)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      (heap++ext)[root]?=some (.flag (answer same a b shift)) ∧
      NaturalRun program (steps same a b shift) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 16) := by
  obtain ⟨ep,args,ax,bx,setup⟩ := prepare left right gap flag tape
  have opcode : program (if same then 8 else 2)=.call 20 (if same then 9 else 3) .r3 := by cases same <;> rfl
  obtain ⟨ec,out,rep,compare⟩ := compare_call ax bx tape _ _ opcode
  let grown := heap++ep++ec
  let flagCell : Cell ℕ := .flag (answer same a b shift)
  let root := grown.length
  let before := args.set .r3 out
  have emitFlag : NaturalRun program 2 (state grown before [] tape (if same then 9 else 3)) []
      (state (grown++[flagCell]) (before.set .r3 root) [] tape 16) := by
    have bound : grown[out]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order a (delta same b shift))) := rep
    apply ReferenceProgramSteps.sound
    cases same
    · cases cmp : BinaryComparisonProgram.order a (delta false b shift) <;>
        simp only [cmp,BinaryComparisonProgram.tag] at bound <;>
        simp [ReferenceProgramSteps.run,state,tickNatural,program,tagBranch,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,before,flagCell,answer,root,cmp,bound]
    · cases cmp : BinaryComparisonProgram.order a (delta true b shift) <;>
        simp only [cmp,BinaryComparisonProgram.tag] at bound <;>
        simp [ReferenceProgramSteps.run,state,tickNatural,program,tagBranch,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,before,flagCell,answer,root,cmp,bound]
  refine ⟨ep++ec++[flagCell],before,root,?_,?_⟩
  · have stored : (grown++[flagCell])[root]?=some flagCell := by simp [root]
    simpa only [grown,flagCell,List.append_assoc] using stored
  · have whole := append_run setup (append_run compare emitFlag)
    unfold steps
    convert whole using 1 <;> first | rfl | omega | simp only [grown,List.append_assoc]

end DirectedFlowCutGap.CandidateLevelTestProgram
