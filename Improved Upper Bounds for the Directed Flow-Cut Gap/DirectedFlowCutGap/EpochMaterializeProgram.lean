import DirectedFlowCutGap.EpochGridTableProgram

/-!
# Physical materialization of one epoch's permutation and grid draws

The permutation and grid assignment share the same original active list.
The returned grid-draw pointer is consumed in original label order.
-/

namespace DirectedFlowCutGap.EpochMaterializeProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open PhysicalBoundedDrawProgram (Outcome)
open PhysicalDrawSequenceProgram (StoredBatch)
open EpochPermutationData (Valid reorder)
open EpochPermutationProgram (indices)
open EpochGridTableProgram (Table table_extend)

def Output (heap : NaturalHeap) (root : ℕ) (order originals : List ℕ) (gridDraws : List Outcome) : Prop :=
  ∃ perm grid,heap[root]?=some (.pair perm grid) ∧ PointerList heap perm order ∧
    Table heap grid (originals.zip (gridDraws.map Outcome.index))

def permLabel (pc : Fin 97) : Fin 145 := ⟨16+pc.val,by omega⟩
def gridLabel (pc : Fin 32) : Fin 145 := ⟨113+pc.val,by omega⟩

def program : Program 145 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (permLabel 0) 1 .r2
    | 1 => .call 8 2 .r3
    | 2 => .field .r2 .r2 false 3
    | 3 => .make .r3 (.pair .r2 .r3) 4
    | 8 => .field .r1 .r2 true (gridLabel 0)
    | _ => .halt
  else if h : pc.val<113 then
    if pc.val=17 then .ret .r3
    else ReferenceProgramLabels.instruction permLabel (EpochPermutationProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=114 then .ret .r3
  else ReferenceProgramLabels.instruction gridLabel
    (EpochGridTableProgram.program ⟨pc.val-113,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 145))
    (tape : Bits) (pc : Fin 145) : NaturalState 145 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (pre : List Outcome) (n : ℕ) : ℕ :=
  EpochPermutationProgram.steps pre+EpochGridTableProgram.steps n+7

private theorem perm_slots (pc : Fin 97) (h : EpochPermutationProgram.program pc≠.halt) :
    program (permLabel pc)=ReferenceProgramLabels.instruction permLabel (EpochPermutationProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,permLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<113 by omega,show 16+pc.val≠17 by omega]

private theorem grid_slots (pc : Fin 32) (h : EpochGridTableProgram.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (EpochGridTableProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,gridLabel,show ¬113+pc.val<16 by omega,show ¬113+pc.val<113 by omega,show 113+pc.val≠114 by omega]

private theorem perm_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {pre post : List Outcome}
    (original : PointerList heap r.a xs) (batch : StoredBatch heap r.b (pre++post))
    (valid : Valid (indices pre) xs.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (order : List ℕ),reorder (indices pre) xs=some order ∧
      EpochPermutationProgram.Output (heap++ext) root order post ∧
      NaturalRun program (EpochPermutationProgram.steps pre+2) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 root) [] tape 1) := by
  obtain ⟨ext,root,order,eq,rep,body⟩ := EpochPermutationProgram.natural_permutation original batch valid tape
  let frame : Frame ℕ 145 := ⟨1,.r2,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (permLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (r.set .r3 root) [frame] tape (permLabel 1)
  have lifted := ReferenceProgramLabels.run permLabel EpochPermutationProgram.program program perm_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (EpochPermutationProgram.steps pre)
      (state heap r [frame] tape (permLabel 0)) [] stop := by
    simpa [state,stop,EpochPermutationProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,permLabel,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,order,eq,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem grid_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {post : List Outcome}
    {permuted remaining : ℕ} (original : PointerList heap r.a xs)
    (pair : heap[r.c]?=some (.pair permuted remaining)) (draws : StoredBatch heap remaining post)
    (count : post.length=xs.length) (tape : Bits) :
    ∃ ext root,Table (heap++ext) root (xs.zip (post.map Outcome.index)) ∧
      NaturalRun program (EpochGridTableProgram.steps xs.length+3) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r3 root) [] tape 2) := by
  let args := r.set .r1 remaining
  let frame : Frame ℕ 145 := ⟨2,.r3,r⟩
  have setup : NaturalRun program 2 (state heap r [] tape 1) [] (state heap args [frame] tape (gridLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,pair]
  obtain ⟨ext,root,rep,body⟩ := EpochGridTableProgram.natural_table (r:=args) original draws count tape
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (gridLabel 1)
  have lifted := ReferenceProgramLabels.run gridLabel EpochGridTableProgram.program program grid_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  let work := EpochGridTableProgram.steps xs.length
  have run : NaturalRun program work (state heap args [frame] tape (gridLabel 0)) [] stop := by
    simpa [state,stop,work,EpochGridTableProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,gridLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have k : 2+(work+1)=work+3 := by omega
  change NaturalRun program (work+3) _ [] _
  rw [← k]
  exact append_run setup (append_run run (.step ret (.done _)))

theorem natural_materialize {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {pre post : List Outcome}
    (original : PointerList heap r.a xs) (batch : StoredBatch heap r.b (pre++post))
    (valid : Valid (indices pre) xs.length) (count : post.length=xs.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ) (order : List ℕ),
      reorder (indices pre) xs=some order ∧ Output (heap++ext) root order xs post ∧
      NaturalRun program (steps pre xs.length) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  obtain ⟨ep,perm,order,exactOrder,⟨elements,draws,pair,ordered,batchTail⟩,permute⟩ := perm_call original batch valid tape
  let mid := heap++ep
  let ready := r.set .r2 perm
  obtain ⟨eg,grid,table,build⟩ := grid_call (r:=ready) (pointerList_extend original ep) pair batchTail count tape
  let done := ready.set .r3 grid
  let grown := mid++eg
  let node : Cell ℕ := .pair elements grid
  let args := done.set .r2 elements
  let root := grown.length
  have store : grown[perm]?=some (.pair elements draws) := lookup_extend pair eg
  have finish : NaturalRun program 2 (state grown done [] tape 2) []
      (state (grown++[node]) (args.set .r3 root) [] tape 4) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      done,ready,store,args,root,node]
  have out : Output (grown++[node]) root order xs post :=
    ⟨elements,grid,by simp [node,root],pointerList_extend (pointerList_extend ordered eg) [node],table_extend table [node]⟩
  refine ⟨ep++eg++[node],args,root,order,exactOrder,?_,?_⟩
  · simpa only [mid,grown,List.append_assoc] using out
  · let p := EpochPermutationProgram.steps pre
    let c := EpochGridTableProgram.steps xs.length
    have countSteps : p+2+(c+3+2)=p+c+7 := by omega
    change NaturalRun program (p+c+7) _ [] _
    rw [← countSteps]
    simpa only [mid,grown,p,c,List.append_assoc,List.nil_append] using append_run permute (append_run build finish)

end DirectedFlowCutGap.EpochMaterializeProgram
