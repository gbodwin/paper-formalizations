import DirectedFlowCutGap.CandidateCapacityCellProgram
import DirectedFlowCutGap.CandidateCapacityTableData

/-! Materialize the candidate capacity matrix in exact descriptor order. -/

namespace DirectedFlowCutGap.CandidateCapacityTableProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList list_extend)
open ResidualZeroTableProgram (CapacityRows capacityRows_extend)
open CandidateEnumeration (Network networkOrder)
open CandidateNodeListsProgram (Descriptor Stored descriptor_extend stored_extend)
open CandidateCapacityCellProgram (Inputs inputs_extend)
open CandidateCapacityTableData (row table)
open CandidatePhysicalCut (networkSize capacities numberEquiv)
open EncodedCandidateCapacity (Input)

def cellLabel (pc : Fin 877) : Fin 925 := ⟨48+pc.val,by omega⟩

def program : Program 925 := fun pc =>
  if pc.val<48 then
    match pc.val with
    | 0 => .move .r1 .r0 1
    | 1 => .call 8 2 .r3
    | 8 => .branch .r0 9 47 47 12
    | 9 => .make .r3 .nil 10
    | 10 => .ret .r3
    | 12 => .call 20 13 .r3
    | 13 => .field .r0 .r0 true 14
    | 14 => .call 8 15 .r0
    | 15 => .make .r3 (.pair .r3 .r0) 10
    | 20 => .field .r0 .r0 false 24
    | 24 => .branch .r1 9 47 47 25
    | 25 => .call 32 26 .r3
    | 26 => .field .r1 .r1 true 27
    | 27 => .call 24 28 .r1
    | 28 => .make .r3 (.pair .r3 .r1) 10
    | 32 => .field .r1 .r1 false (cellLabel 0)
    | _ => .halt
  else if pc.val=76 then .ret .r3
  else ReferenceProgramLabels.instruction cellLabel
    (CandidateCapacityCellProgram.program ⟨pc.val-48,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 925))
    (tape : Bits) (pc : Fin 925) : NaturalState 925 := ⟨heap,heap.length,r,stack,pc,tape⟩

def rowBound (columns cell : ℕ) : ℕ := columns*(cell+8)+3
def tableBound (rows columns cell : ℕ) : ℕ := rows*(rowBound columns cell+7)+3

def instructionBound (n L gridWidth boundWidth : ℕ) : ℕ :=
  tableBound (networkSize n L) (networkSize n L) (CandidateCapacityCellProgram.instructionBound n L gridWidth boundWidth)+2

private theorem cell_slots (pc : Fin 877) (h : CandidateCapacityCellProgram.program pc≠.halt) :
    program (cellLabel pc)=ReferenceProgramLabels.instruction cellLabel (CandidateCapacityCellProgram.program pc) := by
  by_cases hp : pc.val=28
  · have eq : pc=28 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cellLabel,show ¬48+pc.val<48 by omega,show 48+pc.val≠76 by omega]

private theorem cell_call {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Network n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits} {head tail : ℕ}
    (first : Descriptor heap r.a a) (second : Descriptor heap head b)
    (pair : heap[r.b]?=some (.pair head tail)) (input : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (stack : List (Frame ℕ 925)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L a) (numberEquiv n L b)).bits ∧
      NaturalRun program k (state heap r stack tape 25) [] (state (heap++ext) (r.set .r3 root) stack tape 26) ∧
      k ≤ CandidateCapacityCellProgram.instructionBound n L grid.length bound.length+3 := by
  let args := r.set .r1 head
  let caller : Frame ℕ 925 := ⟨26,.r3,r⟩
  have setup : NaturalRun program 2 (state heap r stack tape 25) [] (state heap args (caller::stack) tape (cellLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,pair,args,caller]
  obtain ⟨ext,root,k,rep,body,bound⟩ := CandidateCapacityCellProgram.natural_cell (r:=args) first second input scale cap tape
  let stop := state (heap++ext) (args.set .r3 root) (caller::stack) tape (cellLabel 28)
  have lifted := ReferenceProgramLabels.run cellLabel CandidateCapacityCellProgram.program program cell_slots body
  have lifted := ReferenceProgramStack.run program (caller::stack) lifted
  have run : NaturalRun program k (state heap args (caller::stack) tape (cellLabel 0)) [] stop := by
    simpa [state,stop,CandidateCapacityCellProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 26,[],0⟩ := by
    simp [state,stop,program,cellLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext,root,k+3,rep,?_,by omega⟩
  have count : 2+(k+1)=k+3 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem row_return {n L B : ℕ} {D : Input n} {s t : Fin n} {a : Network n L} {bs : List (Network n L)}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (first : Descriptor heap r.a a) (columns : Stored heap r.b bs) (input : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (caller : Frame ℕ 925) (stack : List (Frame ℕ 925)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),WordList (heap++ext) root (row D s t L B a bs) ∧
      NaturalRun program k (state heap r (caller::stack) tape 24) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) ∧
      k ≤ rowBound bs.length (CandidateCapacityCellProgram.instructionBound n L grid.length bound.length) := by
  induction bs generalizing heap r caller stack with
  | nil =>
    cases columns with
    | nil read =>
      refine ⟨[.nil],heap.length,3,.nil (by simp),?_,by simp [rowBound]⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,read,
        allocateNatural,Recipe.cell]
  | cons b bs ih =>
    cases columns with
    | @cons _ head tail _ _ pair desc rest =>
      let saved := caller::stack
      have enter : tickNatural program (state heap r saved tape 24)=some ⟨state heap r saved tape 25,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,pair,tagBranch]
      obtain ⟨ec,word,k,rep,compute,limit⟩ := cell_call first desc pair input scale cap saved tape
      let mid := heap++ec
      let ready := r.set .r3 word
      let args := ready.set .r1 tail
      let frame : Frame ℕ 925 := ⟨28,.r1,args⟩
      have read : mid[r.b]?=some (.pair head tail) := lookup_extend pair ec
      have setup : NaturalRun program 2 (state mid ready saved tape 26) [] (state mid args (frame::saved) tape 24) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,ready,frame,read]
      obtain ⟨er,suffix,j,tailRep,body,bounded⟩ := ih (r:=args) (descriptor_extend first ec) (stored_extend rest ec)
        (inputs_extend input ec) frame saved
      let grown := mid++er
      let cell : Cell ℕ := .pair word suffix
      let root := grown.length
      have finish : NaturalRun program 2 (state grown (args.set .r1 suffix) saved tape 28) []
          (state (grown++[cell]) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,ready,root,cell,saved,
          allocateNatural,Recipe.cell]
      have out : WordList (grown++[cell]) root (row D s t L B a (b::bs)) :=
        .cons (by simp [root,cell]) (boolList_extend (boolList_extend rep er) [cell]) (list_extend tailRep [cell])
      refine ⟨ec++er++[cell],root,k+(2+(j+2))+1,?_,?_,?_⟩
      · simpa only [mid,grown,List.append_assoc] using out
      · simpa only [mid,grown,List.append_assoc,List.nil_append] using
          NaturalRun.step enter (append_run compute (append_run setup (append_run body finish)))
      · simp only [rowBound,List.length_cons,Nat.succ_mul] at bounded ⊢
        omega

private theorem table_return {n L B : ℕ} {D : Input n} {s t : Fin n} {as bs : List (Network n L)}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (rows : Stored heap r.a as) (columns : Stored heap r.b bs) (input : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (caller : Frame ℕ 925) (stack : List (Frame ℕ 925)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),CapacityRows (heap++ext) root (table D s t L B as bs) ∧
      NaturalRun program k (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) ∧
      k ≤ tableBound as.length bs.length (CandidateCapacityCellProgram.instructionBound n L grid.length bound.length) := by
  induction as generalizing heap r caller stack with
  | nil =>
    cases rows with
    | nil read =>
      refine ⟨[.nil],heap.length,3,.nil (by simp),?_,by simp [tableBound]⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,read,
        allocateNatural,Recipe.cell]
  | cons a as ih =>
    cases rows with
    | @cons _ head tail _ _ pair desc rest =>
      let saved := caller::stack
      let args := r.set .r0 head
      let frame : Frame ℕ 925 := ⟨13,.r3,r⟩
      have setup : NaturalRun program 3 (state heap r saved tape 8) [] (state heap args (frame::saved) tape 24) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,pair,args,frame]
      obtain ⟨er,entry,k,rep,compute,limit⟩ := row_return (r:=args) desc columns input scale cap frame saved tape
      let mid := heap++er
      let ready := r.set .r3 entry
      let next := ready.set .r0 tail
      let recur : Frame ℕ 925 := ⟨15,.r0,next⟩
      have read : mid[r.a]?=some (.pair head tail) := lookup_extend pair er
      have shift : NaturalRun program 2 (state mid ready saved tape 13) [] (state mid next (recur::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,read,ready,next,recur]
      obtain ⟨et,suffix,j,tailRep,body,bounded⟩ := ih (r:=next) (stored_extend rest er) (stored_extend columns er)
        (inputs_extend input er) recur saved
      let grown := mid++et
      let cell : Cell ℕ := .pair entry suffix
      let root := grown.length
      have finish : NaturalRun program 2 (state grown (next.set .r0 suffix) saved tape 15) []
          (state (grown++[cell]) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,root,cell,saved,next,ready,
          allocateNatural,Recipe.cell]
      have out : CapacityRows (grown++[cell]) root (table D s t L B (a::as) bs) :=
        .cons (by simp [cell,root]) (list_extend (list_extend rep et) [cell]) (capacityRows_extend tailRep [cell])
      refine ⟨er++et++[cell],root,3+(k+(2+(j+2))),?_,?_,?_⟩
      · simpa only [mid,grown,List.append_assoc] using out
      · simpa only [mid,grown,List.append_assoc,List.nil_append] using
          append_run setup (append_run compute (append_run shift (append_run body finish)))
      · simp only [tableBound,List.length_cons,Nat.succ_mul] at bounded ⊢
        omega

theorem natural_table {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (nodes : Stored heap r.a (networkOrder n L)) (input : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      CapacityRows (heap++ext) root (table D s t L B (networkOrder n L) (networkOrder n L)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) ∧
      k ≤ instructionBound n L grid.length bound.length := by
  let args := r.set .r1 r.a
  let caller : Frame ℕ 925 := ⟨2,.r3,args⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [caller] tape 8) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,root,k,rep,body,limit⟩ := table_return (r:=args) nodes nodes input scale cap caller [] tape
  have len : (networkOrder n L).length=networkSize n L := by
    simpa only [List.length_map,List.length_range] using congrArg List.length (CandidateCapacityTableData.order_indices n L)
  rw [len] at limit
  exact ⟨ext,args,root,2+k,rep,append_run setup body,by unfold instructionBound; omega⟩

end DirectedFlowCutGap.CandidateCapacityTableProgram
