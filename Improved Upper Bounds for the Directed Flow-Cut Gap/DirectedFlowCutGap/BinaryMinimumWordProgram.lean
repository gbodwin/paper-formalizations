import DirectedFlowCutGap.CandidateLevelTestProgram

/-! Compare two stored binary integers and return the existing word for their minimum. -/

namespace DirectedFlowCutGap.BinaryMinimumWordProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def label (pc : Fin 48) : Fin 56 := if pc.val=47 then 1 else ⟨8+pc.val,by omega⟩

def program : Program 56 := fun pc =>
  if pc.val<8 then
    match pc.val with
    | 0 => .call (label 0) 1 .r3
    | 1 => .branch .r3 2 2 3 5
    | 2 => .move .r3 .r0 4
    | 3 => .move .r3 .r1 4
    | _ => .halt
  else ReferenceProgramLabels.instruction label
    (BinaryComparisonProgram.program ⟨pc.val-8,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 56))
    (tape : Bits) (pc : Fin 56) : NaturalState 56 := ⟨heap,heap.length,r,stack,pc,tape⟩

def word (x y : Bits) : Bits := if value x≤value y then x else y

theorem word_value (x y : Bits) : value (word x y)=min (value x) (value y) := by
  unfold word
  split
  · exact (min_eq_left ‹_›).symm
  · exact (min_eq_right (by omega)).symm

theorem word_length (x y : Bits) : (word x y).length≤max x.length y.length := by
  unfold word
  split
  · exact le_max_left _ _
  · exact le_max_right _ _

def steps (x y : Bits) : ℕ := BinaryComparisonProgram.steps x y+3

private theorem slots (pc : Fin 48) (nh : BinaryComparisonProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have eq : pc=47 := Fin.ext hp
    subst pc
    exact (nh rfl).elim
  · simp [program,label,hp,show ¬8+pc.val<8 by omega]

theorem natural_minimum {heap : NaturalHeap} {r : Registers ℕ} {x y : Bits}
    (left : BoolList heap r.a x) (right : BoolList heap r.b y) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),BoolList (heap++ext) root (word x y) ∧
      NaturalRun program (steps x y) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 4) := by
  obtain ⟨ext,cmp,len,comparison,tag⟩ := BinaryComparisonProgram.compare_return left right heap.length
    r.c r.d rfl r 47 [] tape
  let caller : Frame ℕ 56 := ⟨1,.r3,r⟩
  let grown := heap++ext
  let fromCompare := r.set .r3 cmp
  let root := if value x≤value y then r.a else r.b
  have enter : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [caller] tape (label 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run label BinaryComparisonProgram.program program slots comparison
  have compare : NaturalRun program (BinaryComparisonProgram.steps x y)
      (state heap r [caller] tape (label 0)) [] (state grown fromCompare [] tape 1) := by
    cases r
    simpa [caller,grown,fromCompare,state,BinaryComparisonProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,label,Registers.set,len] using lift
  have finish : NaturalRun program 2 (state grown fromCompare [] tape 1) [] (state grown (r.set .r3 root) [] tape 4) := by
    apply ReferenceProgramSteps.sound
    rw [CandidateLevelTestProgram.order_eq_ite] at tag
    have stored : grown[cmp]?=some (BinaryComparisonProgram.tag
      (if value x<value y then .lt else if value x=value y then .eq else .gt)) := tag
    by_cases le : value x≤value y
    · by_cases lt : value x<value y
      · simp only [ite_eq_left lt,BinaryComparisonProgram.tag] at stored
        simp [ReferenceProgramSteps.run,state,program,root,fromCompare,tickNatural,Registers.get,Registers.set,
          tagBranch,le,stored]
      · have eq : value x=value y := by omega
        have equalTag : grown[cmp]?=some (.nil : Cell ℕ) := by simpa [eq,BinaryComparisonProgram.tag] using stored
        simp [ReferenceProgramSteps.run,state,program,root,fromCompare,tickNatural,Registers.get,Registers.set,
          tagBranch,le,equalTag]
    · have lt : ¬value x<value y := by omega
      have eq : ¬value x=value y := by omega
      simp only [ite_eq_right lt,ite_eq_right eq,BinaryComparisonProgram.tag] at stored
      simp [ReferenceProgramSteps.run,state,program,root,fromCompare,tickNatural,Registers.get,Registers.set,
        tagBranch,le,stored]
  refine ⟨ext,root,?_,?_⟩
  · unfold root word
    split
    · exact boolList_extend left ext
    · exact boolList_extend right ext
  · exact .step enter (append_run compare finish)

end DirectedFlowCutGap.BinaryMinimumWordProgram
