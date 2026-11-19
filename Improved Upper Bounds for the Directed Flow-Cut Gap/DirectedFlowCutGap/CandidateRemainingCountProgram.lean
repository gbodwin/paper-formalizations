import DirectedFlowCutGap.CandidateBudgetData
import DirectedFlowCutGap.BinaryIncrementProgram

/-!
# Counting the unremoved vertices in a stored mask

The scanner increments a binary word for every false flag. It consumes
the retained removal mask and returns the exact unremoved vertex count.
-/

namespace DirectedFlowCutGap.CandidateRemainingCountProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor

def incLabel (pc : Fin 16) : Fin 32 := ⟨16+pc.val,by omega⟩

def program : Program 32 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .branch .r0 1 15 15 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r2 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .call 0 7 .r3
    | 7 => .branch .r2 15 8 2 15
    | 8 => .move .r0 .r3 9
    | 9 => .call (incLabel 15) 2 .r3
    | 12 => .call 0 15 .r3
    | _ => .halt
  else if pc.val=30 then .ret .r3
  else ReferenceProgramLabels.instruction incLabel
    (BinaryIncrementProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def word : Bits → Bits
  | [] => []
  | b::bs => if b then word bs else (increment true (word bs)).1

theorem word_value (flags : Bits) : value (word flags)=CandidateBudgetData.remaining flags := by
  induction flags with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simp only [word,Bool.false_eq_true,ite_false,CandidateBudgetData.remaining_cons,
        (increment_spec true (word bs)).1,Bool.toNat_true,ih]
    · simp [word,ih]

theorem word_length (flags : Bits) : (word flags).length≤flags.length := by
  induction flags with
  | nil => decide
  | cons b bs ih =>
    cases b
    · exact (increment_spec true (word bs)).2.1.trans (Nat.add_le_add_right ih 1)
    · exact ih.trans (Nat.le_succ _)

def steps : Bits → ℕ
  | [] => 3
  | b::bs => steps bs + (if b then 6 else BinaryIncrementProgram.steps (word bs)+10)

private theorem inc_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incLabel pc) = ReferenceProgramLabels.instruction incLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠30 by omega]

private theorem join {s u v : NaturalState 32} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem increment_call {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits}
    (input : BoolList heap r.a bs) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (increment true bs).1 ∧
      NaturalRun program (BinaryIncrementProgram.steps bs+3) (state heap r stack tape 9) []
        (state (heap++ext) (r.set .r3 root) stack tape 2) := by
  obtain ⟨ext,root,len,body,rep⟩ := BinaryIncrementProgram.increment_return input heap.length
    r.b r.c r.d rfl r 14 [] tape
  let frame : Frame ℕ 32 := ⟨2,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (incLabel 14)
  have first : tickNatural program (state heap r stack tape 9)=
      some ⟨state heap r (frame::stack) tape (incLabel 15),[],0⟩ := rfl
  have enter : tickNatural program (state heap r (frame::stack) tape (incLabel 15))=
      some ⟨state heap r (⟨incLabel 14,.r3,r⟩::frame::stack) tape (incLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run incLabel BinaryIncrementProgram.program program inc_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have run : NaturalRun program (BinaryIncrementProgram.steps bs)
      (state heap r (⟨incLabel 14,.r3,r⟩::frame::stack) tape (incLabel 0)) [] before := by
    cases r
    simpa [before,state,BinaryIncrementProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 2,[],0⟩ := by
    simp [before,frame,state,program,incLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step first (.step enter (join run (.step ret (.done _))))⟩

theorem count_return {heap : NaturalHeap} {r : Registers ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (word flags) ∧
      NaturalRun program (steps flags) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction flags generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      let saved := caller::stack
      let ext : NaturalHeap := [.nil]
      let root := heap.length
      let before := state (heap++ext) (r.set .r3 root) saved tape 2
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have alloc : tickNatural program (state heap r saved tape 1)=some ⟨before,[],0⟩ := by
        simp [ext,root,before,state,program,tickNatural,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state (heap++ext)
          (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      exact ⟨ext,root,.nil (by simp [ext,root]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons b bs ih =>
    cases input with
    | @cons _ bit rest _ _ hp hb ht =>
      let saved := caller::stack
      let first := r.set .r2 bit
      let args := first.set .r0 rest
      let frame : Frame ℕ 32 := ⟨7,.r3,args⟩
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have getHead : tickNatural program (state heap r saved tape 4)=
          some ⟨state heap first saved tape 5,[],0⟩ := by
        simp [first,state,program,tickNatural,Registers.get,hp]
      have getTail : tickNatural program (state heap first saved tape 5)=
          some ⟨state heap args saved tape 6,[],0⟩ := by
        simp [args,first,state,program,tickNatural,Registers.get,Registers.set,hp]
      have descend : tickNatural program (state heap args saved tape 6)=
          some ⟨state heap args (frame::saved) tape 0,[],0⟩ := rfl
      obtain ⟨ext,root,rep,body⟩ := ih (r:=args) ht frame saved
      let mid := heap++ext
      let ready := args.set .r3 root
      let afterCheck : Fin 32 := if b then 2 else 8
      have bitRep : mid[ready.c]?=some (.flag b) := lookup_extend hb _
      have check : tickNatural program (state mid ready saved tape 7)=
          some ⟨state mid ready saved tape afterCheck,[],0⟩ := by
        cases b <;> simp [afterCheck,state,program,tickNatural,Registers.get,tagBranch,bitRep]
      have start := NaturalRun.step branch (.step getHead (.step getTail (.step descend
        (join body (.step check (.done _))))))
      cases b with
      | true =>
        have ret : tickNatural program (state mid ready saved tape 2)=some ⟨state mid
            (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
          simp [ready,saved,state,program,tickNatural,Registers.get,Registers.set]
        refine ⟨ext,root,rep,?_⟩
        have run := join start (.step ret (.done _))
        simp only [steps,ite_true]
        exact run
      | false =>
        let count := ready.set .r0 root
        have move : tickNatural program (state mid ready saved tape 8)=some ⟨state mid count saved tape 9,[],0⟩ := rfl
        obtain ⟨extra,result,correct,trace⟩ := increment_call (r:=count) rep saved tape
        have ret : tickNatural program (state (mid++extra) (count.set .r3 result) saved tape 2)=
            some ⟨state (mid++extra) (caller.saved.set caller.destination result) stack tape caller.continuation,[],0⟩ := by
          simp [saved,state,program,tickNatural,Registers.get,Registers.set]
        refine ⟨ext++extra,result,?_,?_⟩
        · simpa only [word,Bool.false_eq_true,ite_false,mid,List.append_assoc] using correct
        · have run := join start (.step move (join trace (.step ret (.done _))))
          simp only [steps,Bool.false_eq_true,ite_false]
          convert run using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]

theorem natural_count {heap : NaturalHeap} {r : Registers ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (word flags) ∧
      NaturalRun program (steps flags+1) (state heap r [] tape 12) []
        (state (heap++ext) (r.set .r3 root) [] tape 15) := by
  let frame : Frame ℕ 32 := ⟨15,.r3,r⟩
  obtain ⟨ext,root,rep,body⟩ := count_return input frame [] tape
  have call : tickNatural program (state heap r [] tape 12)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,rep,.step call body⟩

theorem steps_bound (flags : Bits) (n : ℕ) (width : flags.length≤n) :
    steps flags+1 ≤ flags.length*(8*n+15)+4 := by
  induction flags with
  | nil => simp [steps]
  | cons b bs ih =>
    have size : bs.length≤n := by simp only [List.length_cons] at width; omega
    have inc := BinaryIncrementProgram.steps_bound (word bs)
    have actual := (word_length bs).trans size
    have tail := ih size
    simp only [steps,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> omega

end DirectedFlowCutGap.CandidateRemainingCountProgram
