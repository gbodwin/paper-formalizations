import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.BinaryPointerListRead

/-! Construct a list of references to one existing payload. -/

namespace DirectedFlowCutGap.RepeatPointerProgram

open BooleanTableRead (IndexSpine)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open BinaryPointerListRead (PointerList pointerList_extend)
open ConcreteExpressionProgram (append_run)

def program : Program 16 := fun pc => match pc.val with
  | 0 => .call 8 1 .r3
  | 8 => .branch .r0 9 15 15 10
  | 9 => .make .r3 .nil 13
  | 10 => .field .r0 .r0 true 11
  | 11 => .call 8 12 .r3
  | 12 => .make .r3 (.pair .r1 .r3) 13
  | 13 => .ret .r3
  | _ => .halt

abbrev state := @ReferenceProgramInvocation.state 16

def steps (size : ℕ) : ℕ := 5*size+4

private theorem loop {size : ℕ} {heap : NaturalHeap} {r : Registers ℕ} (input : IndexSpine heap r.a size)
    (frame : Frame ℕ 16) (stack : List (Frame ℕ 16)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=size+1 ∧ PointerList (heap++ext) root (List.replicate size r.b) ∧
      NaturalRun program (5*size+3) (state heap r (frame::stack) tape 8) []
        (state (heap++ext) (frame.saved.set frame.destination root) stack tape frame.continuation) := by
  induction size generalizing heap r frame stack with
  | zero =>
    cases input with
    | nil atNil =>
      let ext : NaturalHeap := [.nil]
      refine ⟨ext,heap.length,rfl,.nil (by simp [ext]),?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        atNil,tagBranch,allocateNatural,Recipe.cell,ext]
  | succ size ih =>
    cases input with
    | cons atPair rest =>
      rename_i payload tail
      let saved := frame::stack
      let args := r.set .r0 tail
      let inner : Frame ℕ 16 := ⟨12,.r3,args⟩
      have beginRun : NaturalRun program 3 (state heap r saved tape 8) [] (state heap args (inner::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          atPair,tagBranch,args,inner]
      obtain ⟨ext,root,len,rep,body⟩ := ih (r:=args) rest inner saved
      let mid := heap++ext
      let last : Cell ℕ := .pair r.b root
      have finish : NaturalRun program 2 (state mid (args.set .r3 root) saved tape 12) []
          (state (mid++[last]) (frame.saved.set frame.destination mid.length) stack tape frame.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          args,saved,last,allocateNatural,Recipe.cell]
      refine ⟨ext++[last],mid.length,by simp [len],?_,?_⟩
      · have out : PointerList (mid++[last]) mid.length (r.b::List.replicate size r.b) :=
          .cons (by simp [last]) (pointerList_extend rep [last])
        simpa only [mid,List.append_assoc,List.replicate_succ] using out
      · have count : 3+((5*size+3)+2)=5*(size+1)+3 := by omega
        rw [← count]
        simpa only [mid,List.append_assoc,List.nil_append] using
          append_run beginRun (append_run body finish)

theorem natural_repeat {size : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (input : IndexSpine heap r.a size) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=size+1 ∧ PointerList (heap++ext) root (List.replicate size r.b) ∧
      NaturalRun program (steps size) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let caller : Frame ℕ 16 := ⟨1,.r3,r⟩
  have start : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,len,data,run⟩ := loop input caller [] tape
  exact ⟨ext,root,len,data,.step start run⟩

end DirectedFlowCutGap.RepeatPointerProgram
