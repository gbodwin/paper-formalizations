import DirectedFlowCutGap.EpochPermutationData
import DirectedFlowCutGap.BinaryPointerListRead
import DirectedFlowCutGap.ConcreteExpressionProgram
import DirectedFlowCutGap.ReferenceProgramSteps

/-! Read the selected payload and replace its slot with the old head. -/

namespace DirectedFlowCutGap.EpochPrefixSelectionProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open EpochPermutationData (suffix)

def counterLabel (pc : Fin 17) : Fin 65 := ⟨48+pc.val,by omega⟩

def program : Program 65 := fun pc =>
  if pc.val<48 then
    match pc.val with
    | 0 => .call 8 1 .r1
    | 1 => .field .r2 .r0 false 2
    | 2 => .call 20 3 .r3
    | 3 => .field .r0 .r3 true 4
    | 4 => .field .r0 .r0 true 5
    | 5 => .field .r3 .r3 false 6
    | 6 => .make .r3 (.pair .r3 .r0) 7
    | 8 => .move .r0 .r1 9
    | 9 => .call (counterLabel 0) (counterLabel 16) .r3
    | 20 => .branch .r1 24 47 47 30
    | 24 => .field .r3 .r0 false 25
    | 25 => .field .r0 .r0 true 26
    | 26 => .make .r0 (.pair .r2 .r0) 27
    | 27 => .make .r3 (.pair .r3 .r0) 28
    | 28 => .ret .r3
    | 30 => .field .r3 .r0 false 31
    | 31 => .field .r0 .r0 true 32
    | 32 => .field .r1 .r1 true 33
    | 33 => .call 20 34 .r1
    | 34 => .field .r0 .r1 true 35
    | 35 => .make .r0 (.pair .r3 .r0) 36
    | 36 => .field .r1 .r1 false 37
    | 37 => .make .r3 (.pair .r1 .r0) 28
    | _ => .halt
  else if pc.val=64 then .ret .r3
  else ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program ⟨pc.val-48,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 65))
    (tape : Bits) (pc : Fin 65) : NaturalState 65 := ⟨heap,heap.length,r,stack,pc,tape⟩

def Stored (heap : NaturalHeap) (root chosen : ℕ) (rest : List ℕ) : Prop :=
  ∃ listRoot,heap[root]?=some (.pair chosen listRoot) ∧ PointerList heap listRoot rest

def bodySteps (i : ℕ) : ℕ := 10*i+6
def steps (word : Bits) : ℕ := BinaryCounterProgram.steps word+bodySteps (value word)+10

theorem steps_le (word : Bits) : steps word ≤ 13*value word+10*word.length+19 := by
  have b := BinaryCounterProgram.steps_bound word
  unfold steps bodySteps
  omega

private theorem appended_at (heap ext : NaturalHeap) (i : ℕ) :
    (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1600000 in
private theorem replace_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {i : ℕ}
    (row : PointerList heap r.a xs) (index : IndexSpine heap r.b i) (inside : i<xs.length)
    (caller : Frame ℕ 65) (stack : List (Frame ℕ 65)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root xs[i] (xs.set i r.c) ∧
      NaturalRun program (bodySteps i) (state heap r (caller::stack) tape 20) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction i generalizing heap r xs caller stack with
  | zero =>
    cases index with
    | nil empty =>
      cases row with
      | nil _ => simp at inside
      | @cons _ head tail rest pair cells =>
        let i := heap.length
        let a : Cell ℕ := .pair r.c tail
        let b : Cell ℕ := .pair head i
        let ext : NaturalHeap := [a,b]
        let saved := caller::stack
        let ready := (r.set .r3 head).set .r0 tail
        have start : NaturalRun program 3 (state heap r saved tape 20) [] (state heap ready saved tape 26) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,empty,pair,
            tagBranch,ready]
        have finish : NaturalRun program 3 (state heap ready saved tape 26) []
            (state (heap++ext) (caller.saved.set caller.destination (i+1)) stack tape caller.continuation) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,ready,saved,
            allocateNatural,Recipe.cell,i,a,b,ext,List.append_assoc]
        exact ⟨ext,i+1,⟨i,appended_at heap ext 1,.cons (appended_at heap ext 0) (pointerList_extend cells ext)⟩,
          append_run start finish⟩
  | succ i ih =>
    cases index with
    | @cons _ payload countdown _ ip smaller =>
      cases row with
      | nil _ => simp at inside
      | @cons _ head tail rest pair cells =>
        let saved := caller::stack
        let args := (((r.set .r3 head).set .r0 tail).set .r1 countdown)
        let inner : Frame ℕ 65 := ⟨34,.r1,args⟩
        have setup : NaturalRun program 5 (state heap r saved tape 20) [] (state heap args (inner::saved) tape 20) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,ip,pair,
            tagBranch,args,inner]
        have bound : i<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
        obtain ⟨er,root,⟨next,chosen,rep⟩,run⟩ := ih (r:=args) cells smaller bound inner saved
        let mid := heap++er
        let i0 := mid.length
        let a : Cell ℕ := .pair head next
        let b : Cell ℕ := .pair rest[i] i0
        let ext : NaturalHeap := [a,b]
        let stored := args.set .r1 root
        have chosenIn : mid[root]?=some (.pair rest[i] next) := chosen
        have chosenAfter : (mid++[a])[root]?=some (.pair rest[i] next) := lookup_extend chosenIn [a]
        have finish : NaturalRun program 5 (state mid stored saved tape 34) []
            (state (mid++ext) (caller.saved.set caller.destination (i0+1)) stack tape caller.continuation) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,stored,saved,
            chosenIn,chosenAfter,i0,a,b,ext,allocateNatural,Recipe.cell,List.append_assoc]
        have answer : Stored (mid++ext) (i0+1) ((head::rest)[i+1]) ((head::rest).set (i+1) r.c) :=
          ⟨i0,appended_at mid ext 1,.cons (appended_at mid ext 0) (pointerList_extend rep ext)⟩
        refine ⟨er++ext,i0+1,?_,?_⟩
        · simpa only [mid,List.append_assoc] using answer
        · have count : 5+(bodySteps i+5)=bodySteps (i+1) := by unfold bodySteps; omega
          rw [← count]
          simpa only [mid,List.append_assoc,List.nil_append] using append_run setup (append_run run finish)

private theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,counterLabel,show ¬48+pc.val<48 by omega,show 48+pc.val≠64 by omega]

private theorem make_index {heap : NaturalHeap} {r : Registers ℕ} {word : Bits}
    (input : BoolList heap r.b word) (tape : Bits) :
    ∃ ext root,IndexSpine (heap++ext) root (value word) ∧
      NaturalRun program (BinaryCounterProgram.steps word+4) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  let args := r.set .r0 r.b
  let outer : Frame ℕ 65 := ⟨1,.r1,r⟩
  let inner : Frame ℕ 65 := ⟨counterLabel 16,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) []
      (state heap args [inner,outer] tape (counterLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,root,len,body,rep⟩ := BinaryCounterProgram.convert_return (a:=args.a) input heap.length
    args.b args.c args.d rfl args 16 [] tape
  let stop := state (heap++ext) (args.set .r3 root) [outer] tape (counterLabel 16)
  have lifted := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots body
  have lifted := ReferenceProgramStack.run program [outer] lifted
  have run : NaturalRun program (BinaryCounterProgram.steps word)
      (state heap args [inner,outer] tape (counterLabel 0)) [] stop := by
    cases r
    simpa [state,args,inner,outer,stop,BinaryCounterProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,ReferenceProgramLabels.frame,Registers.set,len] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,counterLabel,tickNatural,outer,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 3+(BinaryCounterProgram.steps word+1)=BinaryCounterProgram.steps word+4 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem front {heap : NaturalHeap} {r : Registers ℕ} {head : ℕ} {tail : List ℕ}
    (row : PointerList heap r.a (head::tail)) (tape : Bits) :
    NaturalRun program 2 (state heap r [] tape 1) []
      (state heap (r.set .r2 head) [⟨3,.r3,r.set .r2 head⟩] tape 20) := by
  cases row with
  | cons pair _ =>
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,pair]

private theorem finish_selection {heap : NaturalHeap} {r : Registers ℕ} {head chosen i : ℕ} {tail : List ℕ}
    (selection : Stored heap r.d chosen ((head::tail).set i head)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root chosen (suffix head tail i) ∧
      NaturalRun program 4 (state heap r [] tape 3) [] (state (heap++ext) (args.set .r3 root) [] tape 7) := by
  obtain ⟨whole,entry,rep⟩ := selection
  have form : (head::tail).set i head=head::suffix head tail i := by cases i <;> rfl
  rw [form] at rep
  cases rep with
  | @cons _ front tailRoot _ pair rest =>
    let cell : Cell ℕ := .pair chosen tailRoot
    let args := r.set .r0 tailRoot
    refine ⟨[cell],args,heap.length,⟨tailRoot,by simp [cell],pointerList_extend rest [cell]⟩,?_⟩
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,entry,pair,args,
      cell,allocateNatural,Recipe.cell]

theorem natural_select {heap : NaturalHeap} {r : Registers ℕ} {head : ℕ} {tail : List ℕ} {word : Bits}
    (row : PointerList heap r.a (head::tail)) (input : BoolList heap r.b word)
    (inside : value word<(head::tail).length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Stored (heap++ext) root (head::tail)[value word] (suffix head tail (value word)) ∧
      NaturalRun program (steps word) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 7) := by
  obtain ⟨ei,index,rep,convert⟩ := make_index input tape
  let mid := heap++ei
  let ready := r.set .r1 index
  let args := ready.set .r2 head
  let frame : Frame ℕ 65 := ⟨3,.r3,args⟩
  have extended : PointerList mid ready.a (head::tail) := pointerList_extend row ei
  have setup := front (r:=ready) extended tape
  obtain ⟨es,selected,chosen,swap⟩ := replace_return (r:=args) extended rep inside frame [] tape
  let grown := mid++es
  let returned := args.set .r3 selected
  obtain ⟨ef,regs,root,output,finish⟩ := finish_selection (r:=returned) chosen tape
  refine ⟨ei++es++ef,regs,root,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using output
  · let u := BinaryCounterProgram.steps word
    let v := bodySteps (value word)
    have count : u+4+(2+(v+4))=u+v+10 := by omega
    change NaturalRun program (u+v+10) _ [] _
    rw [← count]
    simpa only [grown,mid,u,v,args,frame,List.append_assoc,List.nil_append] using
      append_run convert (append_run setup (append_run swap finish))

end DirectedFlowCutGap.EpochPrefixSelectionProgram
