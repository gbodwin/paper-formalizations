import DirectedFlowCutGap.RoundWordTablesProgram
import DirectedFlowCutGap.ReferenceProgramInvocation

/-! Allocate one shared zero row, with one entry per stored vertex. -/

namespace DirectedFlowCutGap.ZeroWeightRowProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open GraphDiscoveryProgram (Vertices)
open PathCostMaterialization (WordList list_extend)

def program : Program 16 := fun pc => match pc.val with
  | 0 => .make .r1 .nil 1
  | 1 => .call 8 2 .r3
  | 8 => .branch .r0 9 15 15 11
  | 9 => .move .r3 .r1 10
  | 10 => .ret .r3
  | 11 => .field .r0 .r0 true 12
  | 12 => .call 8 13 .r3
  | 13 => .make .r3 (.pair .r1 .r3) 10
  | _ => .halt

abbrev state := @ReferenceProgramInvocation.state 16

def steps (n : ℕ) : ℕ := 5*n+5

private theorem zeros_return {heap : NaturalHeap} {r : Registers ℕ} {vertices : List Bits}
    (labels : Vertices heap r.a vertices) (empty : heap[r.b]?=some .nil)
    (caller : Frame ℕ 16) (stack : List (Frame ℕ 16)) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (List.replicate vertices.length []) ∧
      NaturalRun program (5*vertices.length+3) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction vertices generalizing heap r caller stack with
  | nil =>
    cases labels with
    | nil read =>
      refine ⟨[],r.b,by simpa using WordList.nil empty,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,read]
  | cons v vs ih =>
    cases labels with
    | @cons _ head tail _ _ atFirst _ rest =>
      let saved := caller::stack
      let smaller := r.set .r0 tail
      let frame : Frame ℕ 16 := ⟨13,.r3,smaller⟩
      have enter : NaturalRun program 3 (state heap r saved tape 8) [] (state heap smaller (frame::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          tagBranch,atFirst,smaller,frame]
      obtain ⟨em,result,rep,body⟩ := ih (r:=smaller) rest empty frame saved
      let mid := heap++em
      let cell : Cell ℕ := .pair r.b result
      have finish : NaturalRun program 2 (state mid (smaller.set .r3 result) saved tape 13) []
          (state (mid++[cell]) (caller.saved.set caller.destination mid.length) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,smaller,saved,cell]
      have stored : WordList (mid++[cell]) mid.length (List.replicate (v::vs).length []) := by
        exact .cons (by simp [cell]) (.nil (lookup_extend (lookup_extend empty em) [cell])) (list_extend rep [cell])
      refine ⟨em++[cell],mid.length,?_,?_⟩
      · simpa only [mid,List.append_assoc] using stored
      · have count : 3+(5*vs.length+3+2)=5*(v::vs).length+3 := by simp [Nat.mul_add]; omega
        rw [← count]
        simpa only [mid,List.append_assoc,List.nil_append] using append_run enter (append_run body finish)

theorem natural_zero_row {heap : NaturalHeap} {r : Registers ℕ} {vertices : List Bits}
    (labels : Vertices heap r.a vertices) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),WordList (heap++ext) root (List.replicate vertices.length []) ∧
      NaturalRun program (steps vertices.length) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) := by
  let mid := heap++[.nil]
  let args := r.set .r1 heap.length
  let caller : Frame ℕ 16 := ⟨2,.r3,args⟩
  have enter : NaturalRun program 2 (state heap r [] tape 0) [] (state mid args [caller] tape 8) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,mid,args,caller]
  obtain ⟨ext,root,rep,run⟩ := zeros_return (r:=args) (GraphDiscoveryProgram.vertices_extend labels [.nil])
    (by simp [args,Registers.set]) caller [] tape
  refine ⟨[.nil]++ext,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have count : 2+(5*vertices.length+3)=steps vertices.length := by unfold steps; omega
    rw [← count]
    simpa only [mid,List.append_assoc,List.nil_append] using append_run enter run

end DirectedFlowCutGap.ZeroWeightRowProgram
