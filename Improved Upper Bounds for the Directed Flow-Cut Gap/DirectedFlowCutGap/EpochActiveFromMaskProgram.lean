import DirectedFlowCutGap.ActiveDemandListProgram

/-! Produce the exact original-label active demand list from the stored masks. -/

namespace DirectedFlowCutGap.EpochActiveFromMaskProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open GraphWalkExtension (Edge EdgeList edge_extend)
open RetainedGridState

def labelPair {n : ℕ} (p : Pair n) : Bits×Bits := (p.1.val.bits,p.2.val.bits)

def Payloads {n : ℕ} (heap : NaturalHeap) (refs : List ℕ) (pairs : List (Pair n)) : Prop :=
  List.Forall₂ (fun ptr p => Edge heap ptr (labelPair p)) refs pairs

theorem payloads_extend {n : ℕ} {heap : NaturalHeap} {refs : List ℕ} {pairs : List (Pair n)}
    (stored : Payloads heap refs pairs) (ext : NaturalHeap) : Payloads (heap++ext) refs pairs := by
  induction stored with
  | nil => exact .nil
  | cons head _ ih => exact .cons (edge_extend head ext) ih

def flatLabel (pc : Fin 18) : Fin 66 := ⟨16+pc.val,by omega⟩
def filterLabel (pc : Fin 32) : Fin 66 := ⟨34+pc.val,by omega⟩

def program : Program 66 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (flatLabel 0) 1 .r2
    | 1 => .move .r0 .r1 2
    | 2 => .move .r1 .r2 3
    | 3 => .call (filterLabel 0) 4 .r3
    | _ => .halt
  else if h : pc.val<34 then
    if pc.val=24 then .ret .r3
    else ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=35 then .ret .r3
  else ReferenceProgramLabels.instruction filterLabel
    (ActiveDemandListProgram.program ⟨pc.val-34,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 66))
    (tape : Bits) (pc : Fin 66) : NaturalState 66 := ⟨heap,heap.length,r,stack,pc,tape⟩

def flatSteps (n : ℕ) : ℕ := (6*n+8)*n+3
def steps {n : ℕ} (a : PairFlags n) : ℕ :=
  flatSteps n+ActiveDemandListProgram.steps (RetainedEpochFromMasks.flags a)+6

def instructionBound (n : ℕ) : ℕ := flatSteps n+9*(n*n)+10

theorem steps_le {n : ℕ} (a : PairFlags n) : steps a ≤ instructionBound n := by
  have h := ActiveDemandListProgram.steps_le (RetainedEpochFromMasks.flags a)
  have len : (RetainedEpochFromMasks.flags a).length=n*n := by
    simp only [RetainedEpochFromMasks.flags,List.length_map,RetainedMassTableProgram.pairOrder_length]
  rw [len] at h
  unfold steps instructionBound
  omega

private theorem flat_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc≠.halt) :
    program (flatLabel pc)=ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases hp : pc.val=8
  · have eq : pc=8 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,flatLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<34 by omega,show 16+pc.val≠24 by omega]

private theorem filter_slots (pc : Fin 32) (h : ActiveDemandListProgram.program pc≠.halt) :
    program (filterLabel pc)=ReferenceProgramLabels.instruction filterLabel (ActiveDemandListProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,filterLabel,show ¬34+pc.val<16 by omega,show ¬34+pc.val<34 by omega,show 34+pc.val≠35 by omega]

private theorem flat_call {n : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (rows : RetainedDemandEraseProgram.RowsAt heap r.a a) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (RetainedEpochFromMasks.flags a) ∧
      NaturalRun program (flatSteps n+2) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 root) [] tape 1) := by
  obtain ⟨ext,root,_,rep,body⟩ := FlattenDemandMaskProgram.natural_trace rows tape
  let frame : Frame ℕ 66 := ⟨1,.r2,r⟩
  let stop := state (heap++ext) (r.set .r3 root) [frame] tape (flatLabel 8)
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (flatLabel 0),[],0⟩ := rfl
  have lifted := ReferenceProgramLabels.run flatLabel FlattenDemandMaskProgram.program program flat_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (flatSteps n) (state heap r [frame] tape (flatLabel 0)) [] stop := by
    simpa [state,stop,flatSteps,FlattenDemandMaskProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,flatLabel,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem filter_call {heap : NaturalHeap} {r : Registers ℕ} {refs : List ℕ} {flags : Bits}
    (keys : PointerList heap r.b refs) (mask : BoolList heap r.c flags) (len : flags.length=refs.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      PointerList (heap++ext) root (ActiveDemandListProgram.kept flags refs) ∧
      NaturalRun program (ActiveDemandListProgram.steps flags+4) (state heap r [] tape 1) []
        (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  let args := (r.set .r0 r.b).set .r1 r.c
  let frame : Frame ℕ 66 := ⟨4,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 1) [] (state heap args [frame] tape (filterLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,root,rep,body⟩ := ActiveDemandListProgram.natural_filter (r:=args) keys mask len tape
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (filterLabel 1)
  have lifted := ReferenceProgramLabels.run filterLabel ActiveDemandListProgram.program program filter_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  let work := ActiveDemandListProgram.steps flags
  have run : NaturalRun program work (state heap args [frame] tape (filterLabel 0)) [] stop := by
    simpa [state,stop,work,ActiveDemandListProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (args.set .r3 root) [] tape 4,[],0⟩ := by
    simp [state,stop,program,filterLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,args,root,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

theorem natural_active {n : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (rows : RetainedDemandEraseProgram.RowsAt heap r.a a)
    (pairs : EdgeList heap r.b ((RetainedMassTableProgram.pairOrder n).map labelPair)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ) (active : List ℕ),
      PointerList (heap++ext) root active ∧ Payloads (heap++ext) active (RetainedTapeInput.activeList a) ∧
      NaturalRun program (steps a) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  obtain ⟨refs,keys,payloads⟩ := ActiveDemandListProgram.edge_pointers pairs
  have rep : Payloads heap refs (RetainedMassTableProgram.pairOrder n) :=
    List.forall₂_map_right_iff.mp payloads
  let flags := RetainedEpochFromMasks.flags a
  have len : flags.length=refs.length := by simpa only [flags,RetainedEpochFromMasks.flags,List.length_map] using rep.length_eq.symm
  obtain ⟨ef,mask,activeBits,flatten⟩ := flat_call rows tape
  let mid := heap++ef
  let ready := r.set .r2 mask
  obtain ⟨er,args,root,kept,filter⟩ := filter_call (r:=ready) (pointerList_extend keys ef) activeBits len tape
  have agreement := ActiveDemandListProgram.kept_relation (payloads_extend (payloads_extend rep ef) er) (flag a)
  rw [ActiveDemandListProgram.all_pairs n] at agreement
  refine ⟨ef++er,args,root,ActiveDemandListProgram.kept flags refs,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using kept
  · simpa only [mid,flags,Payloads,RetainedEpochFromMasks.flags,ActiveDemandListProgram.all_pairs,RetainedTapeInput.activeList,
      List.append_assoc] using agreement
  · let f := flatSteps n
    let w := ActiveDemandListProgram.steps flags
    have count : f+2+(w+4)=f+w+6 := by omega
    change NaturalRun program (f+w+6) _ [] _
    rw [← count]
    simpa only [mid,f,w,flags,List.append_assoc,List.nil_append] using append_run flatten filter

end DirectedFlowCutGap.EpochActiveFromMaskProgram
