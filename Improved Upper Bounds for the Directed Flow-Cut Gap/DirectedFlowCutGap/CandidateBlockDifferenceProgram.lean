import DirectedFlowCutGap.CandidateCutBlockCountProgram
import DirectedFlowCutGap.CandidateCapacityWords

/-!
# Difference of the two selected threshold counts

The program cancels cells from two unary count lists and converts the
remaining cells to the canonical binary numerator. The first list is the
count for the later point and the second is the count for the earlier point.
-/

namespace DirectedFlowCutGap.CandidateBlockDifferenceProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def countLabel (pc : Fin 32) : Fin 48 := if pc.val=15 then 2 else ⟨16+pc.val,by omega⟩

def program : Program 48 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r0
    | 1 => .call (countLabel 0) 2 .r3
    | 8 => .branch .r1 13 15 15 9
    | 9 => .branch .r0 13 15 15 10
    | 10 => .field .r0 .r0 true 11
    | 11 => .field .r1 .r1 true 8
    | 13 => .ret .r0
    | _ => .halt
  else ReferenceProgramLabels.instruction countLabel (CandidateRemainingCountProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 48))
    (tape : Bits) (pc : Fin 48) : NaturalState 48 := ⟨heap,heap.length,r,stack,pc,tape⟩

def cancellationSteps : ℕ→ℕ→ℕ
  | _,0 => 2
  | 0,_+1 => 3
  | p+1,q+1 => cancellationSteps p q+4

theorem cancellation_le (p q : ℕ) : cancellationSteps p q≤4*q+3 := by
  induction q generalizing p with
  | zero => simp [cancellationSteps]
  | succ q ih =>
    cases p with
    | zero => simp [cancellationSteps]
    | succ p =>
      have bound := ih p
      simp only [cancellationSteps]
      omega

def steps (later earlier : ℕ) : ℕ := cancellationSteps later earlier+
  CandidateRemainingCountProgram.steps (List.replicate (later-earlier) false)+2

private theorem inc_bits (n : ℕ) : (increment true n.bits).1=(n+1).bits := by
  have h := trim_spec n.bits
  have e := normal_bits h.1
  rw [h.2.1,value_bits] at e
  have canonical : Normal n.bits := e ▸ h.1
  simpa [CandidateCapacityWords.word,CandidateCapacityWords.barrier,CandidateCapacityFlags.amount,value_bits]
    using CandidateCapacityWords.canonical canonical false true

theorem word_replicate (n : ℕ) : CandidateRemainingCountProgram.word (List.replicate n false)=n.bits := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [List.replicate_succ,CandidateRemainingCountProgram.word,ih,inc_bits]

private theorem cancel_return {heap : NaturalHeap} {r : Registers ℕ} {later earlier : ℕ}
    (left : BoolList heap r.a (List.replicate later false))
    (right : BoolList heap r.b (List.replicate earlier false))
    (caller : Frame ℕ 48) (stack : List (Frame ℕ 48)) (tape : Bits) :
    ∃ root,BoolList heap root (List.replicate (later-earlier) false) ∧
      NaturalRun program (cancellationSteps later earlier) (state heap r (caller::stack) tape 8) []
        (state heap (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction earlier generalizing later r with
  | zero =>
    cases right with
    | nil hp =>
      refine ⟨r.a,by simpa only [Nat.sub_zero] using left,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,cancellationSteps,tickNatural,Registers.get,tagBranch,hp]
  | succ q ih =>
    cases right with
    | @cons _ flag btail _ _ hp hf hb =>
      cases later with
      | zero =>
        cases left with
        | nil hn =>
          refine ⟨r.a,by simpa only [Nat.zero_sub,List.replicate_zero] using BoolList.nil hn,?_⟩
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,cancellationSteps,tickNatural,Registers.get,tagBranch,hp,hn]
      | succ p =>
        cases left with
        | @cons _ mark atail _ _ ha hm ht =>
          let args := (r.set .r0 atail).set .r1 btail
          have setup : NaturalRun program 4 (state heap r (caller::stack) tape 8) []
              (state heap args (caller::stack) tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,args,ha,hp]
          obtain ⟨root,rep,body⟩ := ih (r:=args) ht hb
          refine ⟨root,by simpa only [Nat.succ_sub_succ_eq_sub] using rep,?_⟩
          have trace := append_run setup body
          simpa [cancellationSteps,Nat.add_comm] using trace

private theorem slots (pc : Fin 32) (h : CandidateRemainingCountProgram.program pc≠.halt) :
    program (countLabel pc)=ReferenceProgramLabels.instruction countLabel (CandidateRemainingCountProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,countLabel,hp,show ¬16+pc.val<16 by omega]

theorem natural_difference {heap : NaturalHeap} {r : Registers ℕ} {later earlier : ℕ}
    (left : BoolList heap r.a (List.replicate later false))
    (right : BoolList heap r.b (List.replicate earlier false)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),BoolList (heap++ext) root (later-earlier).bits ∧
      NaturalRun program (steps later earlier) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) := by
  let caller : Frame ℕ 48 := ⟨1,.r0,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨pointer,current,subtract⟩ := cancel_return left right caller [] tape
  let args := r.set .r0 pointer
  let frame : Frame ℕ 48 := ⟨2,.r3,args⟩
  let previous : Frame ℕ 32 := ⟨15,.r3,args⟩
  obtain ⟨ext,root,rep,body⟩ := CandidateRemainingCountProgram.count_return (r:=args) current previous [] tape
  have call : tickNatural program (state heap args [] tape 1)=some ⟨state heap args [frame] tape (countLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run countLabel CandidateRemainingCountProgram.program program slots body
  have count : NaturalRun program (CandidateRemainingCountProgram.steps (List.replicate (later-earlier) false))
      (state heap args [frame] tape (countLabel 0)) [] (state (heap++ext) (args.set .r3 root) [] tape 2) := by
    simpa [state,frame,previous,CandidateRemainingCountProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,countLabel] using lift
  refine ⟨ext,args,root,?_,?_⟩
  · simpa only [word_replicate] using rep
  · have trace := NaturalRun.step enter (append_run subtract (.step call count))
    have k : cancellationSteps later earlier+
        (CandidateRemainingCountProgram.steps (List.replicate (later-earlier) false)+1)+1=steps later earlier := by
      unfold steps
      omega
    rw [← k]
    exact trace

end DirectedFlowCutGap.CandidateBlockDifferenceProgram
