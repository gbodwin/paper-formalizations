import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.IntegerEpochParameters

/-! Count powers at most a stored limit, beginning with the base itself. -/

namespace DirectedFlowCutGap.BinaryGeometricCounterProgram

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open BooleanTableRead (IndexSpine BoolList)
open ConcreteExpressionProgram (append_run)

def compareLabel (pc : Fin 48) : Fin 168 := ⟨24+pc.val,by omega⟩
def multiplyLabel (pc : Fin 96) : Fin 168 := ⟨72+pc.val,by omega⟩

def program : Program 168 := fun pc =>
  if h : pc.val < 24 then
    match pc.val with
    | 0 => .call 8 1 .r2
    | 1 => .branch .r2 7 7 2 7
    | 2 => .call 12 3 .r0
    | 3 => .make .r3 (.pair .r2 .r3) 0
    | 8 => .field .r1 .r1 false 9
    | 9 => .call (compareLabel 30) 10 .r3
    | 10 => .ret .r3
    | 12 => .move .r2 .r0 13
    | 13 => .field .r0 .r1 true 14
    | 14 => .move .r1 .r2 15
    | 15 => .call (multiplyLabel 94) 16 .r3
    | 16 => .ret .r3
    | _ => .halt
  else if h : pc.val < 72 then
    if pc.val=70 then .ret .r3
    else ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program ⟨pc.val-24,by omega⟩)
  else if pc.val=167 then .ret .r3
  else ReferenceProgramLabels.instruction multiplyLabel (BinaryMultiplicationProgram.program ⟨pc.val-72,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 168

def Parameters (heap : NaturalHeap) (root : ℕ) (limit base : Bits) : Prop :=
  ∃ x b, heap[root]?=some (.pair x b) ∧ BoolList heap x limit ∧ BoolList heap b base

private theorem parameters_extend {heap : NaturalHeap} {root : ℕ} {limit base : Bits}
    (h : Parameters heap root limit base) (ext : NaturalHeap) : Parameters (heap++ext) root limit base := by
  obtain ⟨x,b,atRoot,xs,bs⟩ := h
  exact ⟨x,b,lookup_extend atRoot ext,boolList_extend xs ext,boolList_extend bs ext⟩

private theorem compare_slots (pc : Fin 48) (used : BinaryComparisonProgram.program pc≠.halt) :
    program (compareLabel pc)=ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases stop : pc.val=46
  · have eq : pc=46 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,compareLabel,show ¬24+pc.val<24 by omega,show 24+pc.val<72 by omega,
      show 24+pc.val≠70 by omega]

private theorem multiply_slots (pc : Fin 96) (used : BinaryMultiplicationProgram.program pc≠.halt) :
    program (multiplyLabel pc)=ReferenceProgramLabels.instruction multiplyLabel (BinaryMultiplicationProgram.program pc) := by
  by_cases stop : pc.val=95
  · have eq : pc=95 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,multiplyLabel,show ¬72+pc.val<24 by omega,show ¬72+pc.val<72 by omega,
      show 72+pc.val≠167 by omega]

set_option maxHeartbeats 1000000 in
private theorem test_power {heap : NaturalHeap} {r : Registers ℕ} {power limit base : Bits}
    (p : BoolList heap r.a power) (cfg : Parameters heap r.b limit base) (tape : Bits) :
    ∃ (ext : NaturalHeap) (flag : ℕ),
      (heap++ext)[flag]?=some (.flag (lessEqual power limit).1) ∧
      NaturalRun program (BinaryComparisonProgram.steps power limit+8) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 flag) [] tape 1) := by
  obtain ⟨x,b,atParams,xs,_⟩ := cfg
  let frame : Frame ℕ 168 := ⟨1,.r2,r⟩
  let args := r.set .r1 x
  have first : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape 9) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atParams]
  let start := @ReferenceProgramInvocation.state 48 heap args [] tape 30
  obtain ⟨out,run,flag,_,_,a,b,c,stack,source,pc,dense,⟨ext,grow,_⟩,_⟩ :=
    BinaryComparisonProgram.compare_high start (by rfl) (by rfl) p xs (by rfl)
  let result := out.registers.d
  have final : out = @ReferenceProgramInvocation.state 48 (heap++ext) (args.set .r3 result) [] tape 46 := by
    cases out with
    | mk h next regs stack pc source =>
      cases regs
      simp_all [ReferenceProgramInvocation.state, Registers.set,start,args,result]
  rw [final] at run flag
  have call := ReferenceProgramInvocation.call compareLabel compare_slots (caller:=9) (continuation:=10)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] run
  have ret : tickNatural program (state (heap++ext) (args.set .r3 result) [frame] tape 10) =
      some ⟨state (heap++ext) (r.set .r2 result) [] tape 1,[],0⟩ := rfl
  refine ⟨ext,result,flag,?_⟩
  have count : BinaryComparisonProgram.steps power limit+8 =
      2+((BinaryComparisonProgram.steps power limit+3+2)+1) := by omega
  rw [count]
  simpa only [List.nil_append,Registers.get,Registers.set, Nat.add_assoc] using
    append_run first (append_run call (NaturalRun.step ret (.done _)))

set_option maxHeartbeats 1000000 in
private theorem update_power {heap : NaturalHeap} {r : Registers ℕ} {power limit base : Bits}
    {count : ℕ} (p : BoolList heap r.a power) (cfg : Parameters heap r.b limit base)
    (spine : IndexSpine heap r.d count) (flag : heap[r.c]?=some (.flag true)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (newPower newCount : ℕ),
      BoolList (heap++ext) newPower (mul base power).1 ∧ IndexSpine (heap++ext) newCount (count+1) ∧
      NaturalRun program (BinaryMultiplicationProgram.steps base power+10) (state heap r [] tape 1) []
        (state (heap++ext) ((r.set .r0 newPower).set .r3 newCount) [] tape 0) := by
  obtain ⟨x,b,atParams,_,bs⟩ := cfg
  let frame : Frame ℕ 168 := ⟨3,.r0,r⟩
  let args : Registers ℕ := ⟨b,r.a,r.a,r.d⟩
  have first : NaturalRun program 5 (state heap r [] tape 1) [] (state heap args [frame] tape 15) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atParams,flag,tagBranch]
  let start := @ReferenceProgramInvocation.state 96 heap args [] tape 94
  obtain ⟨out,run,word,_,_,source,pc,stack,a,b,c,dense,⟨ext,grow,_⟩,_⟩ :=
    BinaryMultiplicationProgram.mul_high start (by rfl) (by rfl) bs p (by rfl)
  let result := out.registers.d
  have final : out = @ReferenceProgramInvocation.state 96 (heap++ext) (args.set .r3 result) [] tape 95 := by
    cases out with
    | mk h next regs stack pc source =>
      cases regs
      simp_all [ReferenceProgramInvocation.state,Registers.set,start,args,result]
  rw [final] at run word
  change BoolList (heap++ext) result (mul base power).1 at word
  have call := ReferenceProgramInvocation.call multiplyLabel multiply_slots (caller:=15) (continuation:=16)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] run
  let mid := heap++ext
  let newCell : Cell ℕ := .pair r.c r.d
  have ret : tickNatural program (state mid (args.set .r3 result) [frame] tape 16) =
      some ⟨state mid (r.set .r0 result) [] tape 3,[],0⟩ := rfl
  have advance : tickNatural program (state mid (r.set .r0 result) [] tape 3) =
      some ⟨state (mid++[newCell]) ((r.set .r0 result).set .r3 mid.length) [] tape 0,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,newCell]
  refine ⟨ext++[newCell],result,mid.length,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using boolList_extend word [newCell]
  · have rep : IndexSpine (mid++[newCell]) mid.length (count+1) :=
      .cons (payload:=r.c) (by simp [newCell]) (indexSpine_extend (indexSpine_extend spine ext) [newCell])
    simpa only [mid,List.append_assoc] using rep
  · have cost : BinaryMultiplicationProgram.steps base power+10 =
        5+((BinaryMultiplicationProgram.steps base power+1+2)+2) := by omega
    rw [cost]
    simpa only [mid,List.append_assoc,List.nil_append,Registers.get,Registers.set,Nat.add_assoc] using
      append_run first (append_run call (.step ret (.step advance (.done _))))

def stepBound (W : ℕ) : ℕ := 16*(2*W+1)+64*(W+1)*(2*W+2)+18

set_option maxHeartbeats 1200000 in
private theorem count_loop {heap : NaturalHeap} {r : Registers ℕ} {power limit base : Bits} {count W j : ℕ}
    (remaining : ℕ) (p : BoolList heap r.a power) (cfg : Parameters heap r.b limit base)
    (spine : IndexSpine heap r.d count) (basePos : 1 < value base) (jPos : 1 ≤ j)
    (powerValue : value power = value base ^ j) (countdown : j+remaining = Nat.log (value base) (value limit)+1)
    (baseWidth : base.length ≤ W) (limitWidth : limit.length ≤ W)
    (powerWidth : power.length+remaining*(2*base.length+1) ≤ W) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ),
      IndexSpine (heap++ext) out.d (count+remaining) ∧ k ≤ (remaining+1)*stepBound W ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) out [] tape 7) := by
  induction remaining generalizing heap r power count j <;>
    obtain ⟨ex,flag,test,check⟩ := test_power p cfg tape <;>
    let mid := heap++ex <;>
    let tested := r.set .r2 flag <;>
    have tc : BinaryComparisonProgram.steps power limit+9 ≤ 16*(2*W+1)+9 :=
      (Nat.add_le_add_right (BinaryComparisonProgram.steps_bound _ _) _).trans (by omega)
  case zero =>
    have done : value limit < value power := by
      rw [powerValue,show j=Nat.log (value base) (value limit)+1 by omega]
      exact Nat.lt_pow_succ_log_self basePos _
    have flagFalse : mid[flag]?=some (.flag false) := by
      have truth : (lessEqual power limit).1=false := Bool.eq_false_iff.mpr
        (fun h => Nat.not_le_of_gt done ((lessEqual_spec power limit).1.mp h))
      rw [truth] at test
      exact test
    have stop : tickNatural program (state mid tested [] tape 1)=some ⟨state mid tested [] tape 7,[],0⟩ := by
      simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tested,flagFalse,tagBranch]
    refine ⟨ex,tested,BinaryComparisonProgram.steps power limit+9,?_,?_,?_⟩
    · exact indexSpine_extend spine ex
    · simp only [Nat.zero_add,Nat.one_mul,stepBound]
      omega
    · simpa only [Nat.add_assoc,List.nil_append] using append_run check (.step stop (.done _))
  case succ remaining ih =>
    have limitPos : value limit≠0 := by
      intro hz
      rw [hz,Nat.log_zero_right] at countdown
      omega
    have le : value power ≤ value limit := by
      rw [powerValue]
      exact Nat.pow_le_of_le_log limitPos (by omega)
    have flagTrue : mid[tested.c]?=some (.flag true) := by
      simpa only [tested,Registers.set,(lessEqual_spec _ _).1.mpr le] using test
    obtain ⟨extra,np,nc,word,next,advance⟩ := update_power (r:=tested)
      (boolList_extend p ex) (parameters_extend cfg ex) (indexSpine_extend spine ex) flagTrue tape
    let nextRegs := (tested.set .r0 np).set .r3 nc
    have nextValue : value (mul base power).1 = value base^(j+1) := by
      rw [(mul_spec _ _).1,powerValue,pow_succ,Nat.mul_comm]
    have nextWidth : (mul base power).1.length+remaining*(2*base.length+1) ≤ W := by
      rw [Nat.succ_mul] at powerWidth
      have := (mul_spec base power).2.1
      omega
    have nextClock : (j+1)+remaining=Nat.log (value base) (value limit)+1 := by omega
    obtain ⟨rest,out,k,output,spent,loop⟩ := ih (r:=nextRegs) word
      (parameters_extend (parameters_extend cfg ex) extra) next (by omega) nextValue nextClock nextWidth
    have mulCost : BinaryMultiplicationProgram.steps base power+10 ≤ 64*(W+1)*(2*W+2)+9 := by
      have b := BinaryMultiplicationProgram.steps_bound base power
      have h := Nat.mul_le_mul
        (Nat.mul_le_mul_left 64 (Nat.add_le_add_right baseWidth 1))
        (show base.length+power.length+2 ≤ 2*W+2 by omega)
      omega
    have here : BinaryComparisonProgram.steps power limit+8+
        (BinaryMultiplicationProgram.steps base power+10) ≤ stepBound W := by
      unfold stepBound
      omega
    refine ⟨ex++extra++rest,out,BinaryComparisonProgram.steps power limit+8+
      (BinaryMultiplicationProgram.steps base power+10)+k,?_,?_,?_⟩
    · have lengthEq : count+1+remaining=count+(remaining+1) := by omega
      simpa only [List.append_assoc,lengthEq,mid] using output
    · rw [Nat.succ_add, Nat.succ_mul]
      omega
    · simpa only [List.append_assoc,List.nil_append,Nat.add_assoc,mid,nextRegs] using
        append_run (append_run check advance) loop

/-- The count is the exact integer logarithm plus the length of the seed
spine. Each multiplication puts the fixed base first, so retained padding
increases by at most a fixed additive width per iteration. -/
theorem natural_count {heap : NaturalHeap} {r : Registers ℕ} {limit base : Bits} {seed : ℕ}
    (p : BoolList heap r.a base) (cfg : Parameters heap r.b limit base)
    (spine : IndexSpine heap r.d seed) (basePos : 1 < value base) (tape : Bits) :
    let logs := Nat.log (value base) (value limit)
    let W := base.length+limit.length+logs*(2*base.length+1)
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ),
      IndexSpine (heap++ext) out.d (seed+logs) ∧ k ≤ (logs+1)*stepBound W ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) out [] tape 7) := by
  dsimp only
  apply count_loop _ p cfg spine basePos (j:=1) (by omega)
  · rw [pow_one]
  · omega
  · omega
  · omega
  · omega

end DirectedFlowCutGap.BinaryGeometricCounterProgram
