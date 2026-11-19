import DirectedFlowCutGap.CandidateBlockDifferenceProgram

/-!
# Decode one core vertex from its two consecutive threshold blocks

The two scans return the remainder of the same mask and the selected
counts. The removed case reads the retained grid word. The other case
passes the returned counts to binary difference computation.
-/

namespace DirectedFlowCutGap.CandidateNumeratorCellProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def blockLabel (pc : Fin 32) : Fin 112 := ⟨32+pc.val,by omega⟩
def diffLabel (pc : Fin 48) : Fin 112 := ⟨64+pc.val,by omega⟩

def program : Program 112 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call (blockLabel 0) 1 .r3
    | 1 => .make .r2 (.pair .r2 .r3) 2
    | 2 => .field .r0 .r3 false 3
    | 3 => .call (blockLabel 0) 4 .r3
    | 4 => .field .r0 .r2 false 5
    | 5 => .field .r1 .r0 false 6
    | 6 => .branch .r1 31 8 16 31
    | 8 => .field .r1 .r2 true 9
    | 9 => .field .r1 .r1 true 10
    | 10 => .field .r0 .r3 true 11
    | 11 => .call (diffLabel 0) 12 .r1
    | 12 => .field .r0 .r3 false 13
    | 13 => .make .r3 (.pair .r0 .r1) 14
    | 16 => .field .r1 .r0 true 12
    | _ => .halt
  else if h : pc.val<64 then
    if pc.val=34 then .ret .r3
    else ReferenceProgramLabels.instruction blockLabel (CandidateCutBlockCountProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=66 then .ret .r3
  else ReferenceProgramLabels.instruction diffLabel (CandidateBlockDifferenceProgram.program ⟨pc.val-64,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 112))
    (tape : Bits) (pc : Fin 112) : NaturalState 112 := ⟨heap,heap.length,r,stack,pc,tape⟩

def Mode (heap : NaturalHeap) (root : ℕ) (removed : Bool) (grid : Bits) : Prop :=
  ∃ f w,heap[root]?=some (.pair f w) ∧ heap[f]?=some (.flag removed) ∧ BoolList heap w grid

def Stored (heap : NaturalHeap) (root : ℕ) (tail word : Bits) : Prop :=
  ∃ next value,heap[root]?=some (.pair next value) ∧ BoolList heap next tail ∧ BoolList heap value word

def firstCount (k : ℕ) (flags : Bits) : ℕ := (flags.take k).count true
def secondCount (k : ℕ) (flags : Bits) : ℕ := ((flags.drop k).take k).count true

def word (k : ℕ) (flags grid : Bits) (removed : Bool) : Bits :=
  if removed then grid else (secondCount k flags-firstCount k flags).bits

def steps (k : ℕ) (flags : Bits) (removed : Bool) : ℕ :=
  CandidateCutBlockCountProgram.steps k flags+CandidateCutBlockCountProgram.steps k (flags.drop k)+
    if removed then 12 else CandidateBlockDifferenceProgram.steps (secondCount k flags) (firstCount k flags)+16

def instructionBound (k : ℕ) : ℕ := k*(8*k+15)+26*k+35

theorem steps_le (k : ℕ) (flags : Bits) (removed : Bool) : steps k flags removed ≤ instructionBound k := by
  have count (xs : Bits) : (xs.take k).count true≤k :=
    List.count_le_length.trans (by simp [List.length_take])
  have a : firstCount k flags≤k := count flags
  have b : secondCount k flags≤k := count (flags.drop k)
  let difference := secondCount k flags-firstCount k flags
  have diff : difference≤k := (Nat.sub_le _ _).trans b
  have unary := CandidateBlockDifferenceProgram.cancellation_le (secondCount k flags) (firstCount k flags)
  have binary := CandidateRemainingCountProgram.steps_bound (List.replicate difference false) k (by simpa using diff)
  have mulBound := Nat.mul_le_mul_right (8*k+15) diff
  have fst := CandidateCutBlockCountProgram.steps_le k flags
  have snd := CandidateCutBlockCountProgram.steps_le k (flags.drop k)
  rw [List.length_replicate] at binary
  cases removed <;> simp only [steps,ite_true,ite_false,Bool.false_eq_true,instructionBound,
      CandidateBlockDifferenceProgram.steps,← show difference=secondCount k flags-firstCount k flags from rfl] <;> omega

private theorem slots_block (pc : Fin 32) (h : CandidateCutBlockCountProgram.program pc≠.halt) :
    program (blockLabel pc)=ReferenceProgramLabels.instruction blockLabel (CandidateCutBlockCountProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,blockLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<64 by omega,show 32+pc.val≠34 by omega]

private theorem slots_diff (pc : Fin 48) (h : CandidateBlockDifferenceProgram.program pc≠.halt) :
    program (diffLabel pc)=ReferenceProgramLabels.instruction diffLabel (CandidateBlockDifferenceProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,diffLabel,show ¬64+pc.val<32 by omega,show ¬64+pc.val<64 by omega,show 64+pc.val≠66 by omega]

private theorem block_call {heap : NaturalHeap} {r : Registers ℕ} {flags : Bits} {k : ℕ}
    (mask : BoolList heap r.a flags) (limit : IndexSpine heap r.b k) (fits : k≤flags.length)
    (pc next : Fin 112) (opcode : program pc=.call (blockLabel 0) next .r3) (tape : Bits) :
    ∃ ext root,CandidateCutBlockCountProgram.Stored (heap++ext) root (flags.drop k) ((flags.take k).count true) ∧
      NaturalRun program (CandidateCutBlockCountProgram.steps k flags+2) (state heap r [] tape pc) []
        (state (heap++ext) (r.set .r3 root) [] tape next) := by
  obtain ⟨ext,args,root,rep,body⟩ := CandidateCutBlockCountProgram.natural_block mask limit fits tape
  let frame : Frame ℕ 112 := ⟨next,.r3,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (blockLabel 2)
  have enter : tickNatural program (state heap r [] tape pc)=some ⟨state heap r [frame] tape (blockLabel 0),[],0⟩ := by
    simp [state,tickNatural,opcode,frame]
  have lift := ReferenceProgramLabels.run blockLabel CandidateCutBlockCountProgram.program program slots_block body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateCutBlockCountProgram.steps k flags)
      (state heap r [frame] tape (blockLabel 0)) [] stop := by
    simpa [state,stop,CandidateCutBlockCountProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape next,[],0⟩ := by
    simp [state,stop,blockLabel,program,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem diff_call {heap : NaturalHeap} {r : Registers ℕ} {a b : ℕ}
    (left : BoolList heap r.a (List.replicate a false)) (right : BoolList heap r.b (List.replicate b false)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (a-b).bits ∧
      NaturalRun program (CandidateBlockDifferenceProgram.steps a b+2) (state heap r [] tape 11) []
        (state (heap++ext) (r.set .r1 root) [] tape 12) := by
  obtain ⟨ext,args,root,rep,body⟩ := CandidateBlockDifferenceProgram.natural_difference left right tape
  let frame : Frame ℕ 112 := ⟨12,.r1,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (diffLabel 2)
  have enter : tickNatural program (state heap r [] tape 11)=
      some ⟨state heap r [frame] tape (diffLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run diffLabel CandidateBlockDifferenceProgram.program program slots_diff body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateBlockDifferenceProgram.steps a b)
      (state heap r [frame] tape (diffLabel 0)) [] stop := by
    simpa [state,stop,CandidateBlockDifferenceProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 12,[],0⟩ := by
    simp [state,stop,diffLabel,program,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem pack {heap : NaturalHeap} {r : Registers ℕ} {tail height : Bits} {a : ℕ}
    (remaining : CandidateCutBlockCountProgram.Stored heap r.d tail a) (heightRep : BoolList heap r.b height)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root tail height ∧
      NaturalRun program 2 (state heap r [] tape 12) [] (state (heap++ext) (args.set .r3 root) [] tape 14) := by
  obtain ⟨next,units,pair,mask,_⟩ := remaining
  let node : Cell ℕ := .pair next r.b
  let args := r.set .r0 next
  refine ⟨[node],args,heap.length,⟨next,r.b,by simp [node],boolList_extend mask _,boolList_extend heightRep _⟩,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
    pair,node,args]

theorem natural_cell {heap : NaturalHeap} {r : Registers ℕ} {flags grid : Bits} {k : ℕ} {removed : Bool}
    (mask : BoolList heap r.a flags) (limit : IndexSpine heap r.b k) (fits : k+k≤flags.length)
    (mode : Mode heap r.c removed grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root (flags.drop (k+k)) (word k flags grid removed) ∧
      NaturalRun program (steps k flags removed) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 14) := by
  obtain ⟨eb,first,⟨midMask,beforeCount,firstPair,midFlags,beforeRep⟩,scanFirst⟩ := block_call mask limit (by omega) 0 1 rfl tape
  let mid := heap++eb
  let firstRet := r.set .r3 first
  let bundle : Cell ℕ := .pair r.c first
  let prep := mid++[bundle]
  let secondArgs := (firstRet.set .r2 mid.length).set .r0 midMask
  have setup : NaturalRun program 2 (state mid firstRet [] tape 1) [] (state prep secondArgs [] tape 3) := by
    have pair : prep[first]?=some (.pair midMask beforeCount) := lookup_extend firstPair [bundle]
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      firstRet,bundle,prep,secondArgs,pair]
  have inside : k≤(flags.drop k).length := by simp only [List.length_drop]; omega
  obtain ⟨ea,second,afterRep,scanSecond⟩ := block_call (r:=secondArgs) (boolList_extend midFlags [bundle])
    (indexSpine_extend (indexSpine_extend limit eb) [bundle]) inside 3 4 rfl tape
  let grown := prep++ea
  let secondRet := secondArgs.set .r3 second
  obtain ⟨modeFlag,gridRoot,modePair,flagRep,gridRep⟩ := mode
  have modeIn : grown[r.c]?=some (.pair modeFlag gridRoot) :=
    lookup_extend (lookup_extend (lookup_extend modePair eb) [bundle]) ea
  have flagIn : grown[modeFlag]?=some (.flag removed) :=
    lookup_extend (lookup_extend (lookup_extend flagRep eb) [bundle]) ea
  have bundleIn : grown[mid.length]?=some (.pair r.c first) := lookup_extend (by simp [prep,bundle]) ea
  let routed := (secondRet.set .r0 r.c).set .r1 modeFlag
  have route : NaturalRun program 3 (state grown secondRet [] tape 4) []
      (state grown routed [] tape (if removed then 16 else 8)) := by
    apply ReferenceProgramSteps.sound
    cases removed <;> simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
      tagBranch,routed,secondRet,secondArgs,bundleIn,modeIn,flagIn]
  have prefixRun := append_run scanFirst (append_run setup (append_run scanSecond route))
  cases removed with
  | true =>
    let args := routed.set .r1 gridRoot
    have enter : tickNatural program (state grown routed [] tape 16)=some ⟨state grown args [] tape 12,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,Registers.set,args,routed,modeIn]
    have gridIn : BoolList grown args.b grid := boolList_extend (boolList_extend (boolList_extend gridRep eb) [bundle]) ea
    obtain ⟨ef,out,root,rep,finish⟩ := pack (r:=args) afterRep gridIn tape
    refine ⟨eb++[bundle]++ea++ef,out,root,?_,?_⟩
    · simpa only [word,ite_true,grown,prep,mid,List.drop_drop,List.append_assoc] using rep
    · have run := append_run prefixRun (.step enter finish)
      simp only [steps,ite_true]
      convert run using 1 <;> first | rfl | omega | simp only [List.append_assoc]
  | false =>
    obtain ⟨tail,afterCount,afterPair,tailRep,countRep⟩ := afterRep
    let args := (routed.set .r1 beforeCount).set .r0 afterCount
    have firstIn : grown[first]?=some (.pair midMask beforeCount) := lookup_extend (lookup_extend firstPair [bundle]) ea
    have secondIn : grown[second]?=some (.pair tail afterCount) := afterPair
    have prepare : NaturalRun program 3 (state grown routed [] tape 8) [] (state grown args [] tape 11) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,routed,secondRet,
        secondArgs,bundleIn,firstIn,secondIn]
    have beforeIn : BoolList grown args.b (List.replicate (firstCount k flags) false) :=
      boolList_extend (boolList_extend beforeRep [bundle]) ea
    obtain ⟨ed,result,weight,subtract⟩ := diff_call (r:=args) countRep beforeIn tape
    let ready := args.set .r1 result
    have retained : CandidateCutBlockCountProgram.Stored (grown++ed) ready.d ((flags.drop k).drop k) (secondCount k flags) :=
      CandidateCutBlockCountProgram.stored_extend ⟨tail,afterCount,afterPair,tailRep,countRep⟩ ed
    obtain ⟨ef,out,root,rep,finish⟩ := pack (r:=ready) retained weight tape
    refine ⟨eb++[bundle]++ea++ed++ef,out,root,?_,?_⟩
    · simpa only [word,secondCount,Bool.false_eq_true,ite_false,grown,prep,mid,List.drop_drop,List.append_assoc] using rep
    · have run := append_run prefixRun (append_run prepare (append_run subtract finish))
      simp only [steps,secondCount,Bool.false_eq_true,ite_false]
      convert run using 1 <;> first | rfl | omega | simp only [grown,prep,mid,List.append_assoc]

end DirectedFlowCutGap.CandidateNumeratorCellProgram
