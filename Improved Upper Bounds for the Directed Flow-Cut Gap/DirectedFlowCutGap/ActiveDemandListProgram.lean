import DirectedFlowCutGap.RetainedEpochFromMasks
import DirectedFlowCutGap.WordPairProductProgram

/-! Filter the stored row-major demand list by the original active flags. -/

namespace DirectedFlowCutGap.ActiveDemandListProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open GraphWalkExtension (Edge EdgeList)
open RetainedGridState

theorem all_pairs (n : ℕ) : RetainedMassTableProgram.pairOrder n=RetainedTapeInput.allPairs n := by
  rw [RetainedTapeInput.allPairs,List.ofFn_mul]
  simp only [RetainedMassTableProgram.pairOrder,List.product,List.flatMap_def,List.finRange,List.map_ofFn]
  congr 2
  funext i
  change List.ofFn (fun j : Fin n => (i,j))=_
  apply congrArg List.ofFn
  funext j
  symm
  apply (finProdFinEquiv : (Fin n×Fin n) ≃ Fin (n*n)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change i.val*n+j.val=j.val+n*i.val
  ac_rfl

def kept {α : Type*} : Bits → List α → List α
  | true::flags,x::xs => x::kept flags xs
  | false::flags,_::xs => kept flags xs
  | _,_ => []

theorem kept_filter {α : Type*} (test : α→Bool) (xs : List α) :
    kept (xs.map test) xs=xs.filter test := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test x <;> simp [kept,h,ih]

theorem kept_relation {α : Type*} {R : ℕ→α→Prop} {refs : List ℕ} {data : List α}
    (rep : List.Forall₂ R refs data) (test : α→Bool) :
    List.Forall₂ R (kept (data.map test) refs) (data.filter test) := by
  induction rep with
  | nil => exact .nil
  | @cons i v refs data hv _ ih =>
    cases h : test v
    · simpa only [List.map_cons,h,kept,List.filter_cons,Bool.false_eq_true,ite_false] using ih
    · simpa only [List.map_cons,h,kept,List.filter_cons,ite_true] using List.Forall₂.cons hv ih

theorem edge_pointers {heap : NaturalHeap} {root : ℕ} {labels : List (Bits×Bits)} (stored : EdgeList heap root labels) :
    ∃ refs,PointerList heap root refs ∧ List.Forall₂ (Edge heap) refs labels := by
  induction stored with
  | nil read => exact ⟨[],.nil read,.nil⟩
  | @cons _ head _ _ _ pair word _ ih =>
    obtain ⟨refs,list,data⟩ := ih
    exact ⟨head::refs,.cons pair list,.cons word data⟩

def program : Program 32 := fun pc => match pc.val with
  | 0 => .call 8 1 .r3
  | 8 => .branch .r1 9 31 31 12
  | 9 => .make .r3 .nil 10
  | 10 => .ret .r3
  | 12 => .field .r3 .r1 false 13
  | 13 => .branch .r3 31 14 18 31
  | 14 => .field .r0 .r0 true 15
  | 15 => .field .r1 .r1 true 8
  | 18 => .field .r2 .r0 false 19
  | 19 => .field .r0 .r0 true 20
  | 20 => .field .r1 .r1 true 21
  | 21 => .call 8 22 .r3
  | 22 => .make .r3 (.pair .r2 .r3) 10
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 := ⟨heap,heap.length,r,stack,pc,tape⟩

def bodySteps : Bits→ℕ
  | [] => 3
  | false::flags => bodySteps flags+5
  | true::flags => bodySteps flags+9

def steps (flags : Bits) : ℕ := bodySteps flags+1

theorem steps_le (flags : Bits) : steps flags≤9*flags.length+4 := by
  have work : bodySteps flags≤9*flags.length+3 := by
    induction flags with
    | nil => decide
    | cons f fs ih => cases f <;> simp only [bodySteps,List.length_cons,Nat.mul_add,Nat.mul_one] <;> omega
  exact Nat.add_le_add_right work 1

set_option maxHeartbeats 1500000 in
private theorem filter_return {heap : NaturalHeap} {r : Registers ℕ} {items : List ℕ} {flags : Bits}
    (row : PointerList heap r.a items) (mask : BoolList heap r.b flags) (len : flags.length=items.length)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,PointerList (heap++ext) root (kept flags items) ∧
      NaturalRun program (bodySteps flags) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction flags generalizing heap r items caller stack with
  | nil =>
    cases mask with
    | nil zero =>
      have empty : items=[] := List.length_eq_zero_iff.mp len.symm
      subst items
      refine ⟨[.nil],heap.length,.nil (by simp),?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,bodySteps,zero,
        tagBranch,allocateNatural,Recipe.cell]
  | cons b bs ih =>
    cases row with
    | nil _ => simp at len
    | @cons _ ptr next remaining hp rest =>
      cases mask with
      | @cons _ flag tail _ _ entry marker more =>
        let saved := caller::stack
        have count : bs.length=remaining.length := by simpa only [List.length_cons,Nat.succ.injEq] using len
        let trim := (((r.set .r3 flag).set .r0 next).set .r1 tail)
        cases b
        · have start : NaturalRun program 5 (state heap r saved tape 8) [] (state heap trim saved tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,entry,marker,hp,trim]
          obtain ⟨ext,root,out,body⟩ := ih (r:=trim) rest more count caller stack
          refine ⟨ext,root,out,?_⟩
          simpa only [bodySteps,Nat.add_comm 5,List.nil_append] using append_run start body
        · let args := trim.set .r2 ptr
          let frame : Frame ℕ 32 := ⟨22,.r3,args⟩
          let seen := r.set .r3 flag
          have check : NaturalRun program 3 (state heap r saved tape 8) [] (state heap seen saved tape 18) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,entry,marker,seen]
          have advance : NaturalRun program 4 (state heap seen saved tape 18) []
              (state heap args (frame::saved) tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,entry,hp,trim,args,frame,seen]
          have prep : NaturalRun program 7 (state heap r saved tape 8) [] (state heap args (frame::saved) tape 8) :=
            append_run check advance
          obtain ⟨er,tailRoot,out,body⟩ := ih (r:=args) rest more count frame saved
          let mid := heap++er
          let cell : Cell ℕ := .pair ptr tailRoot
          have finish : NaturalRun program 2 (state mid (args.set .r3 tailRoot) saved tape 22) []
              (state (mid++[cell]) (caller.saved.set caller.destination mid.length) stack tape caller.continuation) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,saved,
              allocateNatural,Recipe.cell,cell]
          have output : PointerList (mid++[cell]) mid.length (kept (true::bs) (ptr::remaining)) :=
            .cons (by simp [cell]) (pointerList_extend out [cell])
          refine ⟨er++[cell],mid.length,?_,?_⟩
          · simpa only [mid,List.append_assoc] using output
          · have counted : 7+(bodySteps bs+2)=bodySteps (true::bs) := by simp only [bodySteps]; omega
            rw [← counted]
            simpa only [mid,List.append_assoc,List.nil_append] using append_run prep (append_run body finish)

theorem natural_filter {heap : NaturalHeap} {r : Registers ℕ} {items : List ℕ} {flags : Bits}
    (row : PointerList heap r.a items) (mask : BoolList heap r.b flags) (len : flags.length=items.length) (tape : Bits) :
    ∃ ext root,PointerList (heap++ext) root (kept flags items) ∧
      NaturalRun program (steps flags) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let caller : Frame ℕ 32 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,out,body⟩ := filter_return row mask len caller [] tape
  exact ⟨ext,root,out,.step enter body⟩

end DirectedFlowCutGap.ActiveDemandListProgram
