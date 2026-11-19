import DirectedFlowCutGap.InitialGraphContexts

/-! Prepare the live masks, uniform weights and controller parameters from the stored graph. -/

namespace DirectedFlowCutGap.InitialSeedProgram

open BooleanTableRead (IndexSpine BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open RetainedGridState (PairFlags)
open InitialGraphContexts (Input Dictionary input_extend dictionary_extend enumeration)
open InitialGraphDictionary (label labels word_spine edge_spine)
open InitialUniformTables (words unitWord)
open PathCostMaterialization (WordList list_extend)

def dictLabel (pc : Fin 129) : Fin 3589 := ⟨128+pc.val,by omega⟩
def tableLabel (pc : Fin 80) : Fin 3589 := ⟨257+pc.val,by omega⟩
def contextLabel (pc : Fin 112) : Fin 3589 := ⟨337+pc.val,by omega⟩
def maskLabel (pc : Fin 3124) : Fin 3589 := ⟨449+pc.val,by omega⟩
def repeatLabel (pc : Fin 16) : Fin 3589 := ⟨3573+pc.val,by omega⟩

def program : Program 3589 := fun pc =>
  if pc.val < 128 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .call 32 2 .r2
    | 2 => .call 64 3 .r1
    | 3 => .call 96 4 .r0
    | 4 => .call 112 5 .r3
    | 5 => .field .r1 .r1 false 6
    | 6 => .field .r2 .r2 true 7
    | 7 => .make .r0 (.pair .r0 .r2) 8
    | 8 => .make .r1 (.pair .r3 .r1) 9
    | 9 => .make .r3 (.pair .r0 .r1) 10
    | 16 => .field .r0 .r0 true 17
    | 17 => .field .r0 .r0 false 18
    | 18 => .call (dictLabel 0) 19 .r3
    | 19 => .ret .r3
    | 32 => .field .r2 .r0 true 33
    | 33 => .field .r2 .r2 true 34
    | 34 => .field .r2 .r2 true 35
    | 35 => .field .r0 .r3 false 36
    | 36 => .field .r1 .r3 true 37
    | 37 => .call (tableLabel 0) 38 .r3
    | 38 => .ret .r3
    | 64 => .make .r0 (.pair .r0 .r1) 65
    | 65 => .field .r1 .r0 false 66
    | 66 => .make .r2 (.pair .r2 .r3) 67
    | 67 => .field .r3 .r2 false 68
    | 68 => .field .r2 .r2 true 69
    | 69 => .make .r0 (.pair .r0 .r2) 70
    | 70 => .field .r2 .r0 false 71
    | 71 => .field .r0 .r0 true 72
    | 72 => .field .r2 .r2 true 73
    | 73 => .call (contextLabel 0) 74 .r3
    | 74 => .ret .r3
    | 96 => .field .r0 .r3 false 97
    | 97 => .field .r2 .r1 true 98
    | 98 => .move .r1 .r0 99
    | 99 => .call (maskLabel 0) 100 .r3
    | 100 => .ret .r3
    | 112 => .field .r0 .r3 false 113
    | 113 => .make .r1 (.flag false) 114
    | 114 => .call (repeatLabel 0) 115 .r3
    | 115 => .ret .r3
    | _ => .halt
  else if h : pc.val < 257 then
    if pc.val=132 then .ret .r3
    else ReferenceProgramLabels.instruction dictLabel (InitialGraphDictionary.program ⟨pc.val-128,by omega⟩)
  else if h : pc.val < 337 then
    if pc.val=260 then .ret .r3
    else ReferenceProgramLabels.instruction tableLabel (InitialUniformTables.program ⟨pc.val-257,by omega⟩)
  else if h : pc.val < 449 then
    if pc.val=340 then .ret .r3
    else ReferenceProgramLabels.instruction contextLabel (InitialGraphContexts.program ⟨pc.val-337,by omega⟩)
  else if h : pc.val < 3573 then
    if pc.val=450 then .ret .r3
    else ReferenceProgramLabels.instruction maskLabel (InitialDemandMaskProgram.program ⟨pc.val-449,by omega⟩)
  else if pc.val=3574 then .ret .r3
  else ReferenceProgramLabels.instruction repeatLabel (RepeatPointerProgram.program ⟨pc.val-3573,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3589

def instructionBound (n W : ℕ) : ℕ :=
  InitialGraphDictionary.steps n n.bits+InitialUniformTables.steps n+InitialDemandMaskProgram.instructionBound n W+
    RepeatPointerProgram.steps n+88

def Tables {n : ℕ} (heap : NaturalHeap) (root : ℕ) : Prop :=
  ∃ fractions weights,heap[root]?=some (.pair fractions weights) ∧
    WordPairTableRead.Table heap fractions (List.replicate n (unitWord,unitWord)) ∧
    RetainedMassTableProgram.TableAt heap weights (words n)

theorem tables_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} (h : Tables (n:=n) heap root) (ext : NaturalHeap) :
    Tables (n:=n) (heap++ext) root := by
  obtain ⟨fractions,weights,read,f,w⟩ := h
  exact ⟨fractions,weights,lookup_extend read ext,BinaryIndexedPairRead.table_extend f ext,RoundInputPackProgram.weights_extend w ext⟩

def Contexts {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n) (R M : Bits) : Prop :=
  ∃ params query,heap[root]?=some (.pair params query) ∧
    AdaptiveControllerStorage.Parameters (L:=L) heap params adj R M ∧
    InitialDemandMaskProgram.Context heap query adj (enumeration n) label L.bits

theorem contexts_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {R M : Bits}
    (h : Contexts (L:=L) heap root adj R M) (ext : NaturalHeap) : Contexts (L:=L) (heap++ext) root adj R M := by
  obtain ⟨p,q,read,params,query⟩ := h
  exact ⟨p,q,lookup_extend read ext,AdaptiveControllerStorage.parameters_extend params ext,InitialDemandMaskProgram.context_extend query ext⟩

private theorem dict_slots (pc : Fin 129) (h : InitialGraphDictionary.program pc≠.halt) :
    program (dictLabel pc)=ReferenceProgramLabels.instruction dictLabel (InitialGraphDictionary.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,dictLabel,show ¬128+pc.val<128 by omega,show 128+pc.val<257 by omega,show 128+pc.val≠132 by omega]

private theorem table_slots (pc : Fin 80) (h : InitialUniformTables.program pc≠.halt) :
    program (tableLabel pc)=ReferenceProgramLabels.instruction tableLabel (InitialUniformTables.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,tableLabel,show ¬257+pc.val<128 by omega,show ¬257+pc.val<257 by omega,show 257+pc.val<337 by omega,show 257+pc.val≠260 by omega]

private theorem context_slots (pc : Fin 112) (h : InitialGraphContexts.program pc≠.halt) :
    program (contextLabel pc)=ReferenceProgramLabels.instruction contextLabel (InitialGraphContexts.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,contextLabel,show ¬337+pc.val<128 by omega,show ¬337+pc.val<257 by omega,show ¬337+pc.val<337 by omega,show 337+pc.val<449 by omega,show 337+pc.val≠340 by omega]

private theorem mask_slots (pc : Fin 3124) (h : InitialDemandMaskProgram.program pc≠.halt) :
    program (maskLabel pc)=ReferenceProgramLabels.instruction maskLabel (InitialDemandMaskProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,maskLabel,show ¬449+pc.val<128 by omega,show ¬449+pc.val<257 by omega,show ¬449+pc.val<337 by omega,show ¬449+pc.val<449 by omega,show 449+pc.val<3573 by omega,show 449+pc.val≠450 by omega]

private theorem repeat_slots (pc : Fin 16) (h : RepeatPointerProgram.program pc≠.halt) :
    program (repeatLabel pc)=ReferenceProgramLabels.instruction repeatLabel (RepeatPointerProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,repeatLabel,show ¬3573+pc.val<128 by omega,show ¬3573+pc.val<257 by omega,show ¬3573+pc.val<337 by omega,show ¬3573+pc.val<449 by omega,show ¬3573+pc.val<3573 by omega,show 3573+pc.val≠3574 by omega]

set_option maxHeartbeats 2200000 in
private theorem dictionary_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap r.a adj) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),Dictionary (n:=n) (heap++ext) root ∧
      NaturalRun program (InitialGraphDictionary.steps n n.bits+6) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  let frame : Frame ℕ 3589 := ⟨1,.r3,r⟩
  let args := r.set .r0 count
  have load : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [frame] tape 18) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atInput,atDims,args,frame]
  obtain ⟨ext,root,vertices,pairs,atDict,list,keys,body⟩ := InitialGraphDictionary.natural_dictionary (r:=args) nRep (value_bits n) tape
  have invoke := ReferenceProgramInvocation.call dictLabel dict_slots (caller:=18) (continuation:=19)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 19
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,⟨vertices,pairs,atDict,list,keys⟩,?_⟩
  let k := InitialGraphDictionary.steps n n.bits
  have count : 3+(k+2+1)=k+6 := by omega
  change NaturalRun program (k+6) _ _ _
  rw [← count]
  simpa only [k,stop,Registers.get,Registers.set,List.nil_append] using
    append_run load (append_run invoke (.step ret (.done _)))

set_option maxHeartbeats 2200000 in
private theorem tables_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap r.a adj) (dict : Dictionary (n:=n) heap r.d) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),Tables (n:=n) (heap++ext) root ∧
      NaturalRun program (InitialUniformTables.steps n+9) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  obtain ⟨vertices,pairs,atDict,list,keys⟩ := dict
  let frame : Frame ℕ 3589 := ⟨2,.r2,r⟩
  let loaded := r.set .r2 one
  let args : Registers ℕ := ⟨vertices,pairs,one,r.d⟩
  have load : NaturalRun program 4 (state heap r [] tape 1) [] (state heap loaded [frame] tape 35) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atInput,atDims,atFields,loaded,frame]
  have spans : NaturalRun program 2 (state heap loaded [frame] tape 35) [] (state heap args [frame] tape 37) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atDict,loaded,args]
  have vertexSpine : IndexSpine heap args.a n := by simpa only [args,labels,List.length_map,List.length_finRange] using word_spine list
  have pairSpine : IndexSpine heap args.b (n*n) := by
    simpa only [args,List.length_map,RetainedMassTableProgram.pairOrder_length] using edge_spine keys
  obtain ⟨ext,root,weights,⟨fractions,atRoot,frac⟩,table,body⟩ := InitialUniformTables.natural_tables vertexSpine pairSpine tRep tape
  have invoke := ReferenceProgramInvocation.call tableLabel table_slots (caller:=37) (continuation:=38)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 38
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 2,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,⟨fractions,weights,atRoot,frac,table⟩,?_⟩
  let k := InitialUniformTables.steps n
  have countEq : 4+(2+(k+2+1))=k+9 := by omega
  change NaturalRun program (k+9) _ _ _
  rw [← countEq]
  simpa only [k,stop,Registers.get,Registers.set,List.nil_append] using
    append_run load (append_run spans (append_run invoke (.step ret (.done _))))

set_option maxHeartbeats 2700000 in
private theorem contexts_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {R M : Bits} (input : Input (L:=L) heap r.a adj) (dict : Dictionary (n:=n) heap r.d)
    (tables : Tables (n:=n) heap r.c) (gate : AdaptiveGatesProgram.Parameters heap r.b R M) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),Contexts (L:=L) (heap++ext) root adj R M ∧
      NaturalRun program 55 (state heap r [] tape 2) [] (state (heap++ext) (r.set .r1 root) [] tape 3) := by
  let frame : Frame ℕ 3589 := ⟨3,.r1,r⟩
  let base := heap.length
  let first : Cell ℕ := .pair r.a r.b
  let second : Cell ℕ := .pair r.c r.d
  let third : Cell ℕ := .pair base r.d
  let medium := heap++[first]
  let hold := r.set .r0 base
  have save : NaturalRun program 2 (state heap r [] tape 2) [] (state medium hold [frame] tape 65) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,medium,hold,base,first,allocateNatural,Recipe.cell]
  let more := heap++[first,second]
  let moved : Registers ℕ := ⟨base,r.a,r.d,r.c⟩
  have collect : NaturalRun program 4 (state medium hold [frame] tape 65) [] (state more moved [frame] tape 69) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      more,medium,hold,moved,base,first,second,allocateNatural,Recipe.cell]
  let before : NaturalHeap := [first,second,third]
  let grown := heap++before
  let args : Registers ℕ := ⟨r.d,r.a,r.b,r.c⟩
  have assemble : NaturalRun program 4 (state more moved [frame] tape 69) [] (state grown args [frame] tape 73) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      more,moved,grown,before,base,args,first,second,third,allocateNatural,Recipe.cell]
  obtain ⟨f,w,atTables,table,_⟩ := tables_extend tables before
  obtain ⟨ext,root,params,query,atRoot,paramRep,queryRep,body⟩ :=
    InitialGraphContexts.natural_contexts (r:=args) (input_extend input before) (dictionary_extend dict before)
      ⟨f,w,atTables,table⟩ (AdaptiveGatesProgram.parameters_extend gate before) tape
  have invoke := ReferenceProgramInvocation.call contextLabel context_slots (caller:=73) (continuation:=74)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (grown++ext) (args.set .r3 root) [frame] tape 74
  have ret : tickNatural program stop=some ⟨state (grown++ext) (r.set .r1 root) [] tape 3,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨before++ext,root,?_,?_⟩
  · have represented : Contexts (L:=L) (grown++ext) root adj R M := ⟨params,query,atRoot,paramRep,queryRep⟩
    simpa only [grown,List.append_assoc] using represented
  · simpa only [stop,grown,Registers.get,Registers.set,List.append_assoc,List.nil_append] using
      append_run save (append_run collect (append_run assemble (append_run invoke (.step ret (.done _)))))

set_option maxHeartbeats 2200000 in
private theorem mask_call {n L W : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {R M : Bits} (context : Contexts (L:=L) heap r.b adj R M)
    (dict : Dictionary (n:=n) heap r.d) (positive : 1≤W) (vertexWidth : n.size≤W) (gridWidth : L.bits.length≤W)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      RetainedDemandEraseProgram.RowsAt (heap++ext) root
        (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) (enumeration n) L) ∧
      NaturalRun program k (state heap r [] tape 3) [] (state (heap++ext) (r.set .r0 root) [] tape 4) ∧
      k≤ InitialDemandMaskProgram.instructionBound n W+7 := by
  obtain ⟨params,query,atContext,paramsHp,queryHp⟩ := context
  obtain ⟨vertices,pairs,atDictionary,vs,ps⟩ := dict
  let frame : Frame ℕ 3589 := ⟨4,.r0,r⟩
  let args : Registers ℕ := ⟨vertices,vertices,query,r.d⟩
  have load : NaturalRun program 4 (state heap r [] tape 3) [] (state heap args [frame] tape 99) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atContext,atDictionary,args,frame]
  have labelsW (i : Fin n) : (label i).length≤W :=
    (Nat.size_eq_bits_len i.val).trans_le ((Nat.size_le_size i.isLt.le).trans vertexWidth)
  obtain ⟨ext,root,k,rep,body,time⟩ := InitialDemandMaskProgram.natural_mask (r:=args) (enumeration n)
    label (fun i => value_bits i.val) (value_bits L) vs vs queryHp positive labelsW gridWidth tape
  have invoke := ReferenceProgramInvocation.call maskLabel mask_slots (caller:=99) (continuation:=100)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 100
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 4,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,k+7,rep,?_,by omega⟩
  have countEq : 4+(k+2+1)=k+7 := by omega
  rw [← countEq]
  simpa only [stop,Registers.get,Registers.set,List.nil_append] using
    append_run load (append_run invoke (.step ret (.done _)))

set_option maxHeartbeats 2300000 in
private theorem cut_call {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (dict : Dictionary (n:=n) heap r.d) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),BoolList (heap++ext) root (List.replicate n false) ∧
      NaturalRun program (RepeatPointerProgram.steps n+6) (state heap r [] tape 4) []
        (state (heap++ext) (r.set .r3 root) [] tape 5) := by
  obtain ⟨vs,ps,atDict,vertices,pairs⟩ := dict
  let frame : Frame ℕ 3589 := ⟨5,.r3,r⟩
  let cell : Cell ℕ := .flag false
  let mid := heap++[cell]
  let args : Registers ℕ := ⟨vs,heap.length,r.c,r.d⟩
  have load : NaturalRun program 3 (state heap r [] tape 4) [] (state mid args [frame] tape 114) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atDict,frame,mid,args,cell,allocateNatural,Recipe.cell]
  have spine : IndexSpine mid args.a n := by
    simpa only [args,labels,List.length_map,List.length_finRange] using indexSpine_extend (word_spine vertices) [cell]
  obtain ⟨ext,root,len,flags,body⟩ := RepeatPointerProgram.natural_repeat spine tape
  have invoke := ReferenceProgramInvocation.call repeatLabel repeat_slots (caller:=114) (continuation:=115)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++ext) (args.set .r3 root) [frame] tape 115
  have ret : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) [] tape 5,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  have atFlag : mid[args.b]?=some cell := by simp [mid,args]
  refine ⟨[cell]++ext,root,?_,?_⟩
  · simpa only [cell,mid,List.append_assoc] using InitialUniformTables.flags_of_repeat flags (lookup_extend atFlag ext)
  · let k := RepeatPointerProgram.steps n
    have countEq : 3+(k+2+1)=k+6 := by omega
    change NaturalRun program (k+6) _ _ _
    rw [← countEq]
    simpa only [k,stop,mid,Registers.get,Registers.set,List.append_assoc,List.nil_append] using
      append_run load (append_run invoke (.step ret (.done _)))

private theorem rows_extend_seed {n : ℕ} {heap : NaturalHeap} {root : ℕ} {mask : PairFlags n}
    (h : RetainedDemandEraseProgram.RowsAt heap root mask) (ext : NaturalHeap) :
    RetainedDemandEraseProgram.RowsAt (heap++ext) root mask := by
  obtain ⟨refs,spine,rows⟩ := h
  exact ⟨refs,BinaryPointerListRead.pointerList_extend spine ext,rows.imp (fun _ _ rep => boolList_extend rep ext)⟩

def Output {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n) (R M : Bits) : Prop :=
  ∃ masks controls mask params table cut,
    heap[root]?=some (.pair masks controls) ∧ heap[masks]?=some (.pair mask table) ∧
    heap[controls]?=some (.pair cut params) ∧
    RetainedDemandEraseProgram.RowsAt heap mask (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) (enumeration n) L) ∧
    AdaptiveControllerStorage.Parameters (L:=L) heap params adj R M ∧
    RetainedMassTableProgram.TableAt heap table (words n) ∧ BoolList heap cut (List.replicate n false)

theorem output_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {R M : Bits}
    (h : Output (L:=L) heap root adj R M) (ext : NaturalHeap) : Output (L:=L) (heap++ext) root adj R M := by
  obtain ⟨m,c,mask,params,table,cut,rootAt,mAt,cAt,mp,pp,tp,cp⟩ := h
  exact ⟨m,c,mask,params,table,cut,lookup_extend rootAt ext,lookup_extend mAt ext,lookup_extend cAt ext,
    rows_extend_seed mp ext,AdaptiveControllerStorage.parameters_extend pp ext,
    RoundInputPackProgram.weights_extend tp ext,boolList_extend cp ext⟩

set_option maxHeartbeats 3000000 in
theorem natural_seed {n L W : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {R M : Bits} (input : Input (L:=L) heap r.a adj)
    (gates : AdaptiveGatesProgram.Parameters heap r.b R M)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : L.bits.length≤W) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root a b table k : ℕ),
      Output (L:=L) (heap++ext) root adj R M ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) ⟨a,b,table,root⟩ [] tape 10) ∧
      k≤ instructionBound n W := by
  obtain ⟨ed,dict,dictionary,prepareDict⟩ := dictionary_call input tape
  let dh := heap++ed
  let dr := r.set .r3 dict
  have originalD : Input (L:=L) dh dr.a adj := input_extend input ed
  obtain ⟨et,tables,storedTables,prepareTables⟩ := tables_call (r:=dr) originalD dictionary tape
  let th := dh++et
  let tr := dr.set .r2 tables
  have dictT : Dictionary (n:=n) th tr.d := dictionary_extend dictionary et
  have originalT : Input (L:=L) th tr.a adj := input_extend originalD et
  have gatesT : AdaptiveGatesProgram.Parameters th tr.b R M :=
    AdaptiveGatesProgram.parameters_extend (AdaptiveGatesProgram.parameters_extend gates ed) et
  obtain ⟨ec,contexts,storedCtx,prepareContexts⟩ := contexts_call (r:=tr) originalT dictT storedTables gatesT tape
  let ch := th++ec
  let cr := tr.set .r1 contexts
  have dictC : Dictionary (n:=n) ch cr.d := dictionary_extend dictT ec
  obtain ⟨em,mask,km,storedMask,prepareMask,maskTime⟩ := mask_call (r:=cr)
    storedCtx dictC hW vertexWidth gridWidth tape
  let mh := ch++em
  let mr := cr.set .r0 mask
  have dictM : Dictionary (n:=n) mh mr.d := dictionary_extend dictC em
  obtain ⟨ex,cut,storedCut,prepareCut⟩ := cut_call (r:=mr) dictM tape
  let final := mh++ex
  let args := mr.set .r3 cut
  obtain ⟨params,query,atCtx,paramsRep,_⟩ := contexts_extend (contexts_extend storedCtx em) ex
  obtain ⟨fractions,weights,atTables,_,tableRep⟩ := tables_extend (tables_extend (tables_extend storedTables ec) em) ex
  have readCtx : final[contexts]?=some (.pair params query) := atCtx
  have readTable : final[tables]?=some (.pair fractions weights) := atTables
  have finish : NaturalRun program 2 (state final args [] tape 5) []
      (state final ⟨mask,params,weights,cut⟩ [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      readCtx,readTable,args,mr,cr,tr,dr]
  let base := final.length
  let first : Cell ℕ := .pair mask weights
  let second : Cell ℕ := .pair cut params
  let third : Cell ℕ := .pair base (base+1)
  let leaves : NaturalHeap := [first,second,third]
  have pack : NaturalRun program 3 (state final ⟨mask,params,weights,cut⟩ [] tape 7) []
      (state (final++leaves) ⟨base,base+1,weights,base+2⟩ [] tape 10) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      base,first,second,third,leaves,allocateNatural,Recipe.cell,Nat.add_assoc]
  let ext := ed++et++ec++em++ex++leaves
  let k := (InitialGraphDictionary.steps n n.bits+6)+(InitialUniformTables.steps n+9+
    (55+(km+(RepeatPointerProgram.steps n+6+(2+3)))))
  have rep : Output (L:=L) (final++leaves) (base+2) adj R M :=
    ⟨base,base+1,mask,params,weights,cut,by simp [base,leaves,third],by simp [base,leaves,first],
      by simp [base,leaves,second],rows_extend_seed (rows_extend_seed storedMask ex) leaves,
      AdaptiveControllerStorage.parameters_extend paramsRep leaves,RoundInputPackProgram.weights_extend tableRep leaves,
      boolList_extend storedCut leaves⟩
  refine ⟨ext,base+2,base,base+1,weights,k,?_,?_,?_⟩
  · simpa only [ext,final,mh,ch,th,dh,List.append_assoc] using rep
  · simpa only [ext,k,final,mh,ch,th,dh,List.append_assoc,List.nil_append] using
      append_run prepareDict (append_run prepareTables (append_run prepareContexts
        (append_run prepareMask (append_run prepareCut (append_run finish pack)))))
  · dsimp only [k,instructionBound]
    omega

end DirectedFlowCutGap.InitialSeedProgram
