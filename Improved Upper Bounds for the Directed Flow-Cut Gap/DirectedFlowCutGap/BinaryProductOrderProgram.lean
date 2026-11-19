import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.ReferenceProgramSteps

/-! Compare an actual stored word with the product of two other stored words. -/

namespace DirectedFlowCutGap.BinaryProductOrderProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def mulLabel (pc : Fin 116) : Fin 180 := ⟨16+pc.val,by omega⟩
def cmpLabel (pc : Fin 48) : Fin 180 := ⟨132+pc.val,by omega⟩

def program : Program 180 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r1
    | 1 => .call (cmpLabel 30) 2 .r3
    | 8 => .move .r0 .r1 9
    | 9 => .move .r1 .r2 10
    | 10 => .call (mulLabel 110) 11 .r3
    | 11 => .ret .r3
    | _ => .halt
  else if h : pc.val<132 then
    if pc.val=131 then .ret .r3
    else ReferenceProgramLabels.instruction mulLabel (CanonicalArithmeticProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=178 then .ret .r3
  else ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val-132,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 180

def product (y f : Bits) : Bits := CanonicalArithmeticProgram.result true y f

def steps (x y f : Bits) : ℕ := CanonicalArithmeticProgram.instructions true y f+
  BinaryComparisonProgram.steps x (product y f)+11

def instructionBound (x y f : ℕ) : ℕ := 200*(y+f+2)^2+16*(x+2*y+f+2)+11

theorem product_value (y f : Bits) : value (product y f)=value f*value y := by
  simp [product,CanonicalArithmeticProgram.result_exact,(canonical_values _ _).2,Nat.mul_comm]

theorem product_width (y f : Bits) : (product y f).length≤2*y.length+f.length+1 :=
  ((trim_spec (mul y f).1).2.2.1).trans (mul_spec y f).2.1

theorem steps_le (x y f : Bits) : steps x y f ≤ instructionBound x.length y.length f.length := by
  have mul := CanonicalArithmeticProgram.instructions_bound true y f
  have cmp := BinaryComparisonProgram.steps_bound x (product y f)
  have width := product_width y f
  unfold steps instructionBound
  omega

private theorem mul_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc≠.halt) :
    program (mulLabel pc)=ReferenceProgramLabels.instruction mulLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases stop : pc.val=115
  · have eq : pc=115 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,mulLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<132 by omega,show 16+pc.val≠131 by omega]

private theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases stop : pc.val=46
  · have eq : pc=46 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,cmpLabel,show ¬132+pc.val<16 by omega,show ¬132+pc.val<132 by omega,show 132+pc.val≠178 by omega]

set_option maxHeartbeats 1500000 in
theorem natural_order {heap : NaturalHeap} {r : Registers ℕ} {x y f : Bits}
    (left : BoolList heap r.a x) (right : BoolList heap r.b y) (factor : BoolList heap r.c f) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      (heap++ext)[root]?=some (.flag (Nat.ble (value x) (value f*value y))) ∧
      NaturalRun program (steps x y f) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 2) := by
  let frame : Frame ℕ 180 := ⟨1,.r1,r⟩
  let mulArgs := (r.set .r0 r.b).set .r1 r.c
  have enter : NaturalRun program 3 (state heap r [] tape 0) [] (state heap mulArgs [frame] tape 10) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  let i : NaturalState 116 := ReferenceProgramInvocation.state heap mulArgs [] tape 110
  obtain ⟨em,mulRoot,_,mulBody,mulRep⟩ := CanonicalArithmeticProgram.canonical_high true i rfl rfl right factor rfl
  have mulBody' : NaturalRun CanonicalArithmeticProgram.program (CanonicalArithmeticProgram.instructions true y f)
      (ReferenceProgramInvocation.state heap mulArgs [] tape 110) []
      (ReferenceProgramInvocation.state (heap++em) (mulArgs.set .r3 mulRoot) [] tape 115) := by
    cases r
    simpa [i,ReferenceProgramInvocation.state,CanonicalArithmeticProgram.state,mulArgs,Registers.set] using mulBody
  have mulRun := ReferenceProgramInvocation.call mulLabel mul_slots (caller:=10) (continuation:=11)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] mulBody'
  let mid := heap++em
  let cmpArgs := r.set .r1 mulRoot
  let mulStop := state mid (mulArgs.set .r3 mulRoot) [frame] tape 11
  have mulTrace : NaturalRun program (CanonicalArithmeticProgram.instructions true y f+2)
      (state heap mulArgs [frame] tape 10) [] mulStop := by
    simpa only [mulStop,mid,Registers.get,Registers.set] using mulRun
  have ret : tickNatural program mulStop=some ⟨state mid cmpArgs [] tape 1,[],0⟩ := by
    simp [mulStop,ReferenceProgramInvocation.state,tickNatural,program,Registers.get,Registers.set,frame,cmpArgs]
  let j : NaturalState 48 := ReferenceProgramInvocation.state mid cmpArgs [] tape 30
  obtain ⟨comp,cmpBody,flag,_,_,aa,bb,cc,stack,suffix,pc,dense,⟨ec,heapEq,_⟩,_⟩ :=
    BinaryComparisonProgram.compare_high j rfl rfl (boolList_extend left em) mulRep rfl
  let root := comp.registers.d
  have out : comp=ReferenceProgramInvocation.state (mid++ec) (cmpArgs.set .r3 root) [] tape 46 := by
    have regs : comp.registers=cmpArgs.set .r3 root := by
      cases h : comp.registers with
      | mk a b c d =>
        simp only [j,ReferenceProgramInvocation.state,h] at aa bb cc
        cases hargs : cmpArgs with
        | mk ac bc cc' dc =>
          simp only [hargs] at aa bb cc
          simp [root,h,Registers.set,aa,bb,cc]
    cases comp
    simp_all [ReferenceProgramInvocation.state,j]
  rw [out] at cmpBody flag
  have cmpRun := ReferenceProgramInvocation.call cmpLabel cmp_slots (caller:=1) (continuation:=2)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] cmpBody
  have relation : (lessEqual x (product y f)).1=Nat.ble (value x) (value f*value y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [(lessEqual_spec _ _).1,Nat.ble_eq,product_value]
  refine ⟨em++ec,cmpArgs,root,?_,?_⟩
  · simpa only [mid,ReferenceProgramInvocation.state,Registers.set,product,← relation,List.append_assoc] using flag
  · let a := CanonicalArithmeticProgram.instructions true y f
    let b := BinaryComparisonProgram.steps x (product y f)
    have total : 3+(a+2+(b+3+2+1))=steps x y f := by simp only [steps,a,b]; omega
    rw [← total]
    simpa only [mid,i,j,a,b,product,Registers.get,Registers.set,List.append_assoc,List.nil_append,Nat.add_assoc] using
      append_run enter (append_run mulTrace (.step ret cmpRun))

end DirectedFlowCutGap.BinaryProductOrderProgram
