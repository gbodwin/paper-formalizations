import DirectedFlowCutGap.EpochActiveFromMaskProgram
import DirectedFlowCutGap.CandidateLevelTestProgram

/-! Compare the two original labels in a stored demand key. -/

namespace DirectedFlowCutGap.EpochPairEqualityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open GraphWalkExtension (Edge edge_extend)

def compareLabel (pc : Fin 48) : Fin 72 := ⟨24+pc.val,by omega⟩

def program : Program 72 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 1 => .branch .r3 4 6 6 23
    | 2 => .branch .r3 5 6 6 23
    | 4 => .call 12 2 .r3
    | 5 => .make .r3 (.flag true) 7
    | 6 => .make .r3 (.flag false) 7
    | 8 => .field .r0 .r0 false 9
    | 9 => .field .r1 .r1 false 10
    | 10 => .call (compareLabel 0) (compareLabel 47) .r3
    | 12 => .field .r0 .r0 true 13
    | 13 => .field .r1 .r1 true 10
    | _ => .halt
  else if pc.val=71 then .ret .r3
  else ReferenceProgramLabels.instruction compareLabel
    (BinaryComparisonProgram.program ⟨pc.val-24,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 72))
    (tape : Bits) (pc : Fin 72) : NaturalState 72 := ⟨heap,heap.length,r,stack,pc,tape⟩

def result (a b : Bits×Bits) : Bool := decide (value a.1=value b.1 ∧ value a.2=value b.2)

def steps (a b : Bits×Bits) : ℕ := BinaryComparisonProgram.steps a.1 b.1+
  if value a.1=value b.1 then BinaryComparisonProgram.steps a.2 b.2+13 else 7

theorem steps_le (a b : Bits×Bits) (W : ℕ) (x : a.1.length≤W) (y : a.2.length≤W)
    (u : b.1.length≤W) (v : b.2.length≤W) : steps a b ≤ 64*W+45 := by
  have first := BinaryComparisonProgram.steps_bound a.1 b.1
  have second := BinaryComparisonProgram.steps_bound a.2 b.2
  unfold steps
  split <;> omega

theorem result_label {n : ℕ} (a b : RetainedGridState.Pair n) :
    result (EpochActiveFromMaskProgram.labelPair a) (EpochActiveFromMaskProgram.labelPair b)=decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  simp [result,EpochActiveFromMaskProgram.labelPair,value_bits,Prod.ext_iff,Fin.ext_iff]

private theorem slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (compareLabel pc)=ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have eq : pc=47 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,compareLabel,show ¬24+pc.val<24 by omega,show 24+pc.val≠71 by omega]

private theorem compare_call {heap : NaturalHeap} {r : Registers ℕ} {a b : Bits×Bits}
    (left : Edge heap r.a a) (right : Edge heap r.b b) (second : Bool) (tape : Bits) :
    let x := if second then a.2 else a.1
    let y := if second then b.2 else b.1
    ∃ ext root,(heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order x y)) ∧
      NaturalRun program (BinaryComparisonProgram.steps x y+5)
        (state heap r [] tape (if second then 4 else 0)) []
        (state (heap++ext) (r.set .r3 root) [] tape (if second then 2 else 1)) := by
  obtain ⟨a0,a1,ap,aw0,aw1⟩ := left
  obtain ⟨b0,b1,bp,bw0,bw1⟩ := right
  let x := if second then a.2 else a.1
  let y := if second then b.2 else b.1
  let args := (r.set .r0 (if second then a1 else a0)).set .r1 (if second then b1 else b0)
  let frame : Frame ℕ 72 := ⟨if second then 2 else 1,.r3,r⟩
  let inner : Frame ℕ 72 := ⟨compareLabel 47,.r3,args⟩
  have setup : NaturalRun program 4 (state heap r [] tape (if second then 4 else 0)) []
      (state heap args [inner,frame] tape (compareLabel 0)) := by
    apply ReferenceProgramSteps.sound
    cases second <;> simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
      args,frame,inner,ap,bp]
  have aw : BoolList heap args.a x := by cases second <;> assumption
  have bw : BoolList heap args.b y := by cases second <;> assumption
  obtain ⟨ext,root,len,body,rep⟩ := BinaryComparisonProgram.compare_return aw bw heap.length args.c args.d rfl args 47 [] tape
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (compareLabel 47)
  have lifted := ReferenceProgramLabels.run compareLabel BinaryComparisonProgram.program program slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (BinaryComparisonProgram.steps x y)
      (state heap args [inner,frame] tape (compareLabel 0)) [] stop := by
    cases r
    simpa [state,stop,args,inner,BinaryComparisonProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape (if second then 2 else 1),[],0⟩ := by
    simp [state,stop,program,compareLabel,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,rep,?_⟩
  let work := BinaryComparisonProgram.steps x y
  have count : 4+(work+1)=work+5 := by omega
  change NaturalRun program (work+5) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem order_eq (x y : Bits) : BinaryComparisonProgram.order x y=.eq ↔ value x=value y := by
  rw [CandidateLevelTestProgram.order_eq_ite]
  by_cases lt : value x<value y
  · simp [lt,lt.ne]
  · simp [lt]

private theorem branch {heap : NaturalHeap} {r : Registers ℕ} {x y : Bits}
    (stored : heap[r.d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order x y)))
    (pc next : Fin 72) (inst : program pc=.branch .r3 next 6 6 23) (tape : Bits) :
    tickNatural program (state heap r [] tape pc)=
      some ⟨state heap r [] tape (if value x=value y then next else 6),[],0⟩ := by
  have eq := order_eq x y
  cases o : BinaryComparisonProgram.order x y <;>
    simp_all [state,tickNatural,Registers.get,tagBranch,BinaryComparisonProgram.tag]

private theorem make_result (heap : NaturalHeap) (r : Registers ℕ) (b : Bool) (tape : Bits) :
    NaturalRun program 1 (state heap r [] tape (if b then 5 else 6)) []
      (state (heap++[.flag b]) (r.set .r3 heap.length) [] tape 7) := by
  apply ReferenceProgramSteps.sound
  cases b <;> simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell]

theorem natural_equality {heap : NaturalHeap} {r : Registers ℕ} {a b : Bits×Bits}
    (left : Edge heap r.a a) (right : Edge heap r.b b) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ), (heap++ext)[root]?=some (.flag (result a b)) ∧
      NaturalRun program (steps a b) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 7) := by
  obtain ⟨ea,first,one,compare⟩ := compare_call left right false tape
  let mid := heap++ea
  let args := r.set .r3 first
  have read : mid[args.d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order a.1 b.1)) := one
  have choose := branch (r:=args) read 1 4 rfl tape
  let k := BinaryComparisonProgram.steps a.1 b.1
  by_cases equal : value a.1=value b.1
  · rw [ite_eq_left equal] at choose
    obtain ⟨eb,second,two,compareNext⟩ := compare_call (r:=args) (edge_extend left ea) (edge_extend right ea) true tape
    let grown := mid++eb
    let ready := args.set .r3 second
    have checked : grown[ready.d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order a.2 b.2)) := two
    have selected := branch (r:=ready) checked 2 5 rfl tape
    let flag := decide (value a.2=value b.2)
    have last : tickNatural program (state grown ready [] tape 2)=
        some ⟨state grown ready [] tape (if flag then 5 else 6),[],0⟩ := by simpa [flag] using selected
    refine ⟨ea++eb++[.flag flag],grown.length,?_,?_⟩
    · simp [grown,mid,result,flag,equal]
    · let j := BinaryComparisonProgram.steps a.2 b.2
      have count : k+5+(j+5+(1+1)+1)=k+(j+13) := by omega
      rw [steps,ite_eq_left equal]
      change NaturalRun program (k+(j+13)) _ [] _
      rw [← count]
      simpa only [k,j,mid,grown,List.append_assoc,List.nil_append,args,ready,Registers.set,
        Bool.false_eq_true,ite_false,ite_true] using
        append_run compare (.step choose (append_run compareNext (.step last (make_result grown ready flag tape))))
  · rw [ite_eq_right equal] at choose
    refine ⟨ea++[.flag false],mid.length,?_,?_⟩
    · simp [mid,result,equal]
    · have count : k+5+(1+1)=k+7 := by omega
      rw [steps,ite_eq_right equal]
      change NaturalRun program (k+7) _ [] _
      rw [← count]
      simpa only [k,mid,args,List.append_assoc,List.nil_append,Registers.set,Bool.false_eq_true,ite_false] using
        append_run compare (.step choose (make_result mid args false tape))

end DirectedFlowCutGap.EpochPairEqualityProgram
