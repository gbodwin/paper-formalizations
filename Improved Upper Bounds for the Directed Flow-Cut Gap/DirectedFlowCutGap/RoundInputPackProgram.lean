import DirectedFlowCutGap.PhysicalSampledRoundProgram
import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.RoundWordTablesProgram
import DirectedFlowCutGap.EpochGridLookupProgram

/-! Construct both physical round records from the actual selected input pointers. -/

namespace DirectedFlowCutGap.RoundInputPackProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (pointerList_extend)
open RoundMaskUpdateProgram (MaskPairAt)
open RetainedMassTableProgram (TableAt)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge)
open PathCostMaterialization (WordList)
open IntegerShortestPaths (Enumeration)
open IntegerDistanceFromPhysical (encodedRow)

def counterLabel (pc : Fin 17) : Fin 81 := ⟨64+pc.val,by omega⟩

def program : Program 81 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 8 1 .r1
    | 1 => .call 24 2 .r0
    | 2 => .field .r3 .r3 false 3
    | 3 => .field .r3 .r3 false 4
    | 4 => .field .r2 .r2 false 5
    | 5 => .make .r3 (.pair .r3 .r2) 6
    | 6 => .make .r0 (.pair .r1 .r0) 7
    | 7 => .make .r3 (.pair .r3 .r0) 63
    | 8 => .field .r0 .r0 false 9
    | 9 => .make .r1 (.pair .r0 .r1) 10
    | 10 => .field .r2 .r2 true 11
    | 11 => .make .r2 (.pair .r2 .r0) 12
    | 12 => .field .r3 .r3 false 13
    | 13 => .field .r0 .r3 true 14
    | 14 => .make .r2 (.pair .r0 .r2) 15
    | 15 => .field .r3 .r3 false 16
    | 16 => .make .r3 (.pair .r3 .r2) 17
    | 17 => .make .r3 (.pair .r3 .r1) 18
    | 18 => .ret .r3
    | 24 => .call 48 25 .r1
    | 25 => .call 49 26 .r2
    | 26 => .make .r1 (.pair .r1 .r2) 27
    | 27 => .field .r3 .r3 true 28
    | 28 => .field .r2 .r3 true 29
    | 29 => .make .r1 (.pair .r1 .r2) 30
    | 30 => .field .r3 .r3 false 31
    | 31 => .make .r3 (.pair .r3 .r1) 32
    | 32 => .ret .r3
    | 48 => .field .r0 .r0 false 50
    | 49 => .field .r0 .r0 true 50
    | 50 => .call (counterLabel 0) (counterLabel 16) .r3
    | _ => .halt
  else if pc.val=80 then .ret .r3
  else ReferenceProgramLabels.instruction counterLabel
    (BinaryCounterProgram.program ⟨pc.val-64,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 81

def GraphAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (E : Enumeration (Fin n)) (adj : PairFlags n) : Prop :=
  ∃ vertices matrix,heap[root]?=some (.pair vertices matrix) ∧
    GraphDiscoveryProgram.Vertices heap vertices (E.vertices.map fun i => i.val.bits) ∧
    GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adj)

def StateAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (d : Data n) (words : List (List Bits)) : Prop :=
  ∃ masks weightsContext weights free,heap[root]?=some (.pair masks weightsContext) ∧
    heap[weightsContext]?=some (.pair weights free) ∧ MaskPairAt heap masks d.remaining d.cut ∧
    TableAt heap weights words ∧ heap[free]?=some (.flag false)

def Environment {n : ℕ} (heap : NaturalHeap) (root : ℕ) (E : Enumeration (Fin n)) (adj : PairFlags n)
    (d : Data n) (words : List (List Bits)) : Prop :=
  ∃ graph saved,heap[root]?=some (.pair graph saved) ∧ GraphAt heap graph E adj ∧ StateAt heap saved d words

def Output {n : ℕ} (heap : NaturalHeap) (root : ℕ) (E : Enumeration (Fin n)) (adj : PairFlags n)
    (d : Data n) (p : Pair n) (level : Bits) (words : List (List Bits)) : Prop :=
  ∃ arguments contexts enum targets cutContext updateContext,
    heap[root]?=some (.pair arguments contexts) ∧ heap[arguments]?=some (.pair enum targets) ∧
    heap[contexts]?=some (.pair cutContext updateContext) ∧
    GraphDiscoveryProgram.Vertices heap enum (E.vertices.map fun i => i.val.bits) ∧
    WordPairTableRead.Table heap targets (IntegerLevelCutProgram.fields (row d.weights p) (fun i => i.val.bits) (List.finRange n)) ∧
    IntegerLevelCutProgram.InputContext heap cutContext (E.vertices.map fun i => i.val.bits)
      (GraphRelaxationRefinement.matrix adj) (encodedRow (row d.weights p)).toList p.1.val.bits p.1.val.bits level ∧
    PhysicalSampledRoundProgram.UpdateContext heap updateContext d p words

def steps {n : ℕ} (p : Pair n) : ℕ :=
  BinaryCounterProgram.steps p.1.val.bits+BinaryCounterProgram.steps p.2.val.bits+34

def instructionBound (n : ℕ) : ℕ := 6*n+20*n.size+40

theorem steps_le {n : ℕ} (p : Pair n) : steps p ≤ instructionBound n := by
  have count (i : Fin n) : BinaryCounterProgram.steps i.val.bits ≤ 3*n+10*n.size+3 := by
    have width := Nat.size_le_size i.isLt.le
    have cost := BinaryCounterProgram.steps_bound i.val.bits
    rw [value_bits,Nat.size_eq_bits_len] at cost
    have := i.isLt
    omega
  have left := count p.1
  have right := count p.2
  unfold steps instructionBound
  omega

theorem masks_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {remaining : PairFlags n} {cut : Flags n}
    (h : MaskPairAt heap root remaining cut) (ext : NaturalHeap) : MaskPairAt (heap++ext) root remaining cut := by
  obtain ⟨r,c,read,⟨refs,spine,rows⟩,cut⟩ := h
  exact ⟨r,c,lookup_extend read ext,⟨refs,pointerList_extend spine ext,rows.imp (fun _ _ w => boolList_extend w ext)⟩,
    boolList_extend cut ext⟩

theorem weights_extend {heap : NaturalHeap} {root : ℕ} {words : List (List Bits)}
    (h : TableAt heap root words) (ext : NaturalHeap) : TableAt (heap++ext) root words := by
  induction h with
  | nil read => exact .nil (lookup_extend read ext)
  | cons read words _ ih => exact .cons (lookup_extend read ext) (PathCostMaterialization.list_extend words ext) ih

theorem environment_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {E : Enumeration (Fin n)}
    {adj : PairFlags n} {d : Data n} {words : List (List Bits)}
    (h : Environment heap root E adj d words) (ext : NaturalHeap) : Environment (heap++ext) root E adj d words := by
  obtain ⟨g,s,read,⟨e,m,graph,vertices,matrix⟩,⟨masks,weightContext,weights,free,saved,context,maskRep,wordsRep,flag⟩⟩ := h
  exact ⟨g,s,lookup_extend read ext,⟨e,m,lookup_extend graph ext,GraphDiscoveryProgram.vertices_extend vertices ext,
    GraphAdjacencyProgram.matrix_extend matrix ext⟩,⟨masks,weightContext,weights,free,lookup_extend saved ext,
    lookup_extend context ext,masks_extend maskRep ext,weights_extend wordsRep ext,lookup_extend flag ext⟩⟩

private theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases stop : pc.val=16
  · have eq : pc=16 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,counterLabel,show ¬64+pc.val<64 by omega,show 64+pc.val≠80 by omega]

private theorem index_return {heap : NaturalHeap} {r : Registers ℕ} {word : Bits}
    (stored : BoolList heap r.a word) (caller : Frame ℕ 81) (stack : List (Frame ℕ 81)) (tape : Bits) :
    ∃ ext root,IndexSpine (heap++ext) root (value word) ∧
      NaturalRun program (BinaryCounterProgram.steps word+2) (state heap r (caller::stack) tape 50) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let frame : Frame ℕ 81 := ⟨counterLabel 16,.r3,r⟩
  have enter : tickNatural program (state heap r saved tape 50)=
      some ⟨state heap r (frame::saved) tape (counterLabel 0),[],0⟩ := rfl
  obtain ⟨ext,root,len,body,rep⟩ := BinaryCounterProgram.convert_return stored heap.length r.b r.c r.d rfl r 16 [] tape
  let stop := state (heap++ext) (r.set .r3 root) saved tape (counterLabel 16)
  have lift := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots body
  have lift := ReferenceProgramStack.run program saved lift
  have core : NaturalRun program (BinaryCounterProgram.steps word)
      (state heap r (frame::saved) tape (counterLabel 0)) [] stop := by
    cases r
    simpa [state,ReferenceProgramInvocation.state,stop,frame,BinaryCounterProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program stop=some
      ⟨state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [state,ReferenceProgramInvocation.state,stop,saved,program,counterLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run core (.step ret (.done _)))⟩

private theorem allocated (heap ext : NaturalHeap) (i : ℕ) : (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega)]
  have offset : heap.length+i-heap.length=i := by omega
  rw [offset]

set_option maxHeartbeats 2300000 in
private theorem cut_pack {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ} {level : Bits}
    {E : Enumeration (Fin n)} {adj : PairFlags n} {d : Data n} {words : List (List Bits)}
    {targets costs : ℕ} (key : Edge heap r.a (labelPair p)) (grid : BoolList heap r.b level)
    (tables : heap[r.c]?=some (.pair targets costs))
    (costsRep : WordPairTableRead.Table heap costs (IndexedRationalRead.fields (encodedRow (row d.weights p)).toList))
    (env : Environment heap r.d E adj d words) (tape : Bits) :
    ∃ ext root,IntegerLevelCutProgram.InputContext (heap++ext) root (E.vertices.map fun i => i.val.bits)
        (GraphRelaxationRefinement.matrix adj) (encodedRow (row d.weights p)).toList p.1.val.bits p.1.val.bits level ∧
      NaturalRun program 12 (state heap r [] tape 0) [] (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  obtain ⟨s,t,atKey,source,_⟩ := key
  obtain ⟨g,saved,atEnv,⟨labels,matrix,atGraph,vertices,adjacency⟩,_⟩ := env
  let i := heap.length
  let share : Cell ℕ := .pair s r.b
  let cost : Cell ℕ := .pair costs s
  let mix : Cell ℕ := .pair matrix (i+1)
  let bundle : Cell ℕ := .pair labels (i+2)
  let context : Cell ℕ := .pair (i+3) i
  let ext : NaturalHeap := [share,cost,mix,bundle,context]
  let frame : Frame ℕ 81 := ⟨1,.r1,r⟩
  let first : Registers ℕ := ⟨s,i,r.c,r.d⟩
  let second : Registers ℕ := ⟨matrix,i,i+1,g⟩
  let third : Registers ℕ := ⟨matrix,i,i+2,labels⟩
  let savedGraph := heap++[share,cost]
  have tablesAt : (heap++[share])[r.c]?=some (.pair targets costs) := lookup_extend tables _
  have envAt : savedGraph[r.d]?=some (.pair g saved) := lookup_extend atEnv _
  have graphAt : savedGraph[g]?=some (.pair labels matrix) := lookup_extend atGraph _
  have enumAt : (heap++[share,cost,mix])[g]?=some (.pair labels matrix) := lookup_extend atGraph _
  have begin : NaturalRun program 3 (state heap r [] tape 0) [] (state (heap++[share]) first [frame] tape 10) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atKey,frame,allocateNatural,Recipe.cell,first,share,i]
  have middle : NaturalRun program 4 (state (heap++[share]) first [frame] tape 10) []
      (state savedGraph second [frame] tape 14) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      tablesAt,envAt,graphAt,allocateNatural,Recipe.cell,first,second,share,cost,savedGraph,i]
  have assemble : NaturalRun program 2 (state savedGraph second [frame] tape 14) []
      (state (heap++[share,cost,mix]) third [frame] tape 16) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      enumAt,allocateNatural,Recipe.cell,second,third,mix,savedGraph,i,Nat.add_assoc]
  have finish : NaturalRun program 3 (state (heap++[share,cost,mix]) third [frame] tape 16) []
      (state (heap++ext) (r.set .r1 (i+4)) [] tape 1) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,third,frame,ext,bundle,context,i,Nat.add_assoc]
  have value (offset : ℕ) : (heap++ext)[i+offset]?=ext[offset]? := allocated heap ext offset
  have out : IntegerLevelCutProgram.InputContext (heap++ext) (i+4) (E.vertices.map fun i => i.val.bits)
      (GraphRelaxationRefinement.matrix adj) (encodedRow (row d.weights p)).toList p.1.val.bits p.1.val.bits level := by
    refine ⟨i+3,i,labels,i+2,matrix,i+1,s,r.b,?_,?_,?_,?_,GraphDiscoveryProgram.vertices_extend vertices ext,
      GraphAdjacencyProgram.matrix_extend adjacency ext,?_,boolList_extend source ext,boolList_extend grid ext⟩
    · simpa [ext,context] using value 4
    · simpa [ext,share] using value 0
    · simpa [ext,bundle] using value 3
    · simpa [ext,mix] using value 2
    · exact ⟨costs,s,by simpa [ext,cost] using value 1,RoundWordTablesProgram.extend_table costsRep ext,
        boolList_extend source ext⟩
  exact ⟨ext,i+4,out,append_run begin (append_run middle (append_run assemble finish))⟩

set_option maxHeartbeats 2200000 in
private theorem update_pack {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {E : Enumeration (Fin n)} {adj : PairFlags n} {d : Data n} {words : List (List Bits)}
    (key : Edge heap r.a (labelPair p)) (env : Environment heap r.d E adj d words) (tape : Bits) :
    ∃ ext root,PhysicalSampledRoundProgram.UpdateContext (heap++ext) root d p words ∧
      NaturalRun program (BinaryCounterProgram.steps p.1.val.bits+BinaryCounterProgram.steps p.2.val.bits+16)
        (state heap r [] tape 1) [] (state (heap++ext) (r.set .r0 root) [] tape 2) := by
  obtain ⟨u,v,atKey,source,target⟩ := key
  obtain ⟨g,s,atEnv,_,⟨masks,weightContext,weights,free,atState,atWeight,masksRep,weightRep,freeRep⟩⟩ := env
  let outer : Frame ℕ 81 := ⟨2,.r0,r⟩
  let frame : Frame ℕ 81 := ⟨25,.r1,r⟩
  let srcArgs := r.set .r0 u
  have enter : NaturalRun program 3 (state heap r [] tape 1) [] (state heap srcArgs [frame,outer] tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atKey,outer,frame,srcArgs]
  obtain ⟨es,si,sourceIndex,sourceRun⟩ := index_return (r:=srcArgs) source frame [outer] tape
  let mid := heap++es
  let afterSource := r.set .r1 si
  let next : Frame ℕ 81 := ⟨26,.r2,afterSource⟩
  let targetArgs := afterSource.set .r0 v
  have keyAt : mid[r.a]?=some (.pair u v) := lookup_extend atKey es
  have nextRun : NaturalRun program 2 (state mid afterSource [outer] tape 25) []
      (state mid targetArgs [next,outer] tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      keyAt,afterSource,next,targetArgs]
  obtain ⟨et,ti,targetIndex,targetRun⟩ := index_return (r:=targetArgs) (boolList_extend target es) next [outer] tape
  let grown := mid++et
  let afterTarget := afterSource.set .r2 ti
  let fresh := grown.length
  let indices : Cell ℕ := .pair si ti
  let rest : Cell ℕ := .pair fresh weightContext
  let record : Cell ℕ := .pair masks (fresh+1)
  let extra : NaturalHeap := [indices,rest,record]
  let finishArgs : Registers ℕ := ⟨r.a,fresh,weightContext,s⟩
  have envAt : (grown++[indices])[r.d]?=some (.pair g s) := lookup_extend (lookup_extend (lookup_extend atEnv es) et) _
  have stateAt : (grown++[indices])[s]?=some (.pair masks weightContext) := lookup_extend (lookup_extend (lookup_extend atState es) et) _
  have stateAt₂ : (grown++[indices,rest])[s]?=some (.pair masks weightContext) := lookup_extend (lookup_extend (lookup_extend atState es) et) _
  have gather : NaturalRun program 3 (state grown afterTarget [outer] tape 26) []
      (state (grown++[indices]) finishArgs [outer] tape 29) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,afterTarget,afterSource,indices,envAt,stateAt,finishArgs,fresh]
  have close : NaturalRun program 4 (state (grown++[indices]) finishArgs [outer] tape 29) []
      (state (grown++extra) (r.set .r0 (fresh+2)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,outer,finishArgs,stateAt₂,extra,rest,record,fresh,Nat.add_assoc]
  have read (offset : ℕ) : (grown++extra)[fresh+offset]?=extra[offset]? := allocated grown extra offset
  have out : PhysicalSampledRoundProgram.UpdateContext (grown++extra) (fresh+2) d p words := by
    refine ⟨masks,fresh+1,fresh,weightContext,si,ti,weights,free,?_,?_,
      masks_extend (masks_extend (masks_extend masksRep es) et) extra,?_,?_,?_,
      lookup_extend (lookup_extend (lookup_extend atWeight es) et) extra,
      weights_extend (weights_extend (weights_extend weightRep es) et) extra,
      lookup_extend (lookup_extend (lookup_extend freeRep es) et) extra⟩
    · simpa [extra,record] using read 2
    · simpa [extra,rest] using read 1
    · simpa [extra,indices] using read 0
    · simpa only [labelPair,value_bits] using indexSpine_extend (indexSpine_extend sourceIndex et) extra
    · simpa only [labelPair,value_bits] using indexSpine_extend targetIndex extra
  refine ⟨es++et++extra,fresh+2,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using out
  · have full := append_run enter (append_run sourceRun (append_run nextRun (append_run targetRun (append_run gather close))))
    let a := BinaryCounterProgram.steps p.1.val.bits
    let b := BinaryCounterProgram.steps p.2.val.bits
    have count : 3+(a+2+(2+(b+2+(3+4))))=a+b+16 := by omega
    change NaturalRun program (a+b+16) _ [] _
    rw [← count]
    simpa only [a,b,labelPair,mid,grown,List.append_assoc,List.nil_append] using full

set_option maxHeartbeats 1800000 in
theorem natural_pack {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ} {level : Bits}
    {adj : PairFlags n} {d : Data n} {words : List (List Bits)} {chosen : List Bits}
    (key : Edge heap r.a (labelPair p)) (grid : BoolList heap r.b level)
    (tables : RoundWordTablesProgram.Output heap r.c ((List.finRange n).map fun i => i.val.bits) chosen)
    (values : chosen.map value=(row d.weights p).toList)
    (env : Environment heap r.d (IntegralNetworkFlow.ResidualSearch.Enumeration.fin n) adj d words) (tape : Bits) :
    ∃ (ext : NaturalHeap) (regs : Registers ℕ) (root : ℕ),
      Output (heap++ext) root (IntegralNetworkFlow.ResidualSearch.Enumeration.fin n) adj d p level words ∧
      NaturalRun program (steps p) (state heap r [] tape 0) []
        (state (heap++ext) (regs.set .r3 root) [] tape 63) := by
  let E := IntegralNetworkFlow.ResidualSearch.Enumeration.fin n
  obtain ⟨targets,costs,atTables,targetsRep,costRep⟩ := tables
  rw [RoundWordTablesProgram.cost_fields _ chosen values] at costRep
  rw [RoundWordTablesProgram.target_fields _ chosen values] at targetsRep
  obtain ⟨ec,cut,cutRep,cutRun⟩ := cut_pack key grid atTables costRep env tape
  let middle := heap++ec
  let cutArgs := r.set .r1 cut
  obtain ⟨eu,update,updateRep,updateRun⟩ := update_pack (r:=cutArgs)
    (GraphWalkExtension.edge_extend key ec) (environment_extend env ec) tape
  let grown := middle++eu
  let args := cutArgs.set .r0 update
  obtain ⟨g,s,atEnv,⟨e,m,atGraph,vertices,matrix⟩,stateRep⟩ := env
  have envAt : grown[r.d]?=some (.pair g s) := lookup_extend (lookup_extend atEnv ec) eu
  have graphAt : grown[g]?=some (.pair e m) := lookup_extend (lookup_extend atGraph ec) eu
  have tablesAt : grown[r.c]?=some (.pair targets costs) := lookup_extend (lookup_extend atTables ec) eu
  let finishArgs : Registers ℕ := ⟨update,cut,targets,e⟩
  have prep : NaturalRun program 3 (state grown args [] tape 2) [] (state grown finishArgs [] tape 5) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      envAt,graphAt,tablesAt,args,cutArgs,finishArgs]
  let fresh := grown.length
  let arguments : Cell ℕ := .pair e targets
  let contexts : Cell ℕ := .pair cut update
  let bundle : Cell ℕ := .pair fresh (fresh+1)
  let extra : NaturalHeap := [arguments,contexts,bundle]
  let outRegs : Registers ℕ := ⟨fresh+1,cut,targets,e⟩
  have finish : NaturalRun program 3 (state grown finishArgs [] tape 5) []
      (state (grown++extra) (outRegs.set .r3 (fresh+2)) [] tape 63) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,finishArgs,arguments,contexts,bundle,extra,outRegs,fresh,Nat.add_assoc]
  have read (i : ℕ) : (grown++extra)[fresh+i]?=extra[i]? := allocated grown extra i
  have updated : PhysicalSampledRoundProgram.UpdateContext (grown++extra) update d p words := by
    obtain ⟨masks,rest,indices,weightContext,u,v,weights,free,hroot,hrest,hm,hi,hu,hv,hw,hr,hf⟩ := updateRep
    exact ⟨masks,rest,indices,weightContext,u,v,weights,free,lookup_extend hroot extra,lookup_extend hrest extra,
      masks_extend hm extra,lookup_extend hi extra,indexSpine_extend hu extra,indexSpine_extend hv extra,
      lookup_extend hw extra,weights_extend hr extra,lookup_extend hf extra⟩
  have represented : Output (grown++extra) (fresh+2) E adj d p level words := by
    refine ⟨fresh,fresh+1,e,targets,cut,update,?_,?_,?_,
      GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend vertices ec) eu) extra,
      RoundWordTablesProgram.extend_table (RoundWordTablesProgram.extend_table (RoundWordTablesProgram.extend_table targetsRep ec) eu) extra,
      IntegerLevelCutProgram.context_extend (IntegerLevelCutProgram.context_extend cutRep eu) extra,updated⟩
    · simpa [extra,bundle] using read 2
    · simpa [extra,arguments] using read 0
    · simpa [extra,contexts] using read 1
  refine ⟨ec++eu++extra,outRegs,fresh+2,?_,?_⟩
  · simpa only [grown,middle,List.append_assoc,E] using represented
  · have full := append_run cutRun (append_run updateRun (append_run prep finish))
    let a := BinaryCounterProgram.steps p.1.val.bits
    let b := BinaryCounterProgram.steps p.2.val.bits
    have count : 12+(a+b+16+(3+3))=steps p := by simp only [steps,a,b]; omega
    rw [← count]
    simpa only [middle,grown,cutArgs,args,List.append_assoc,List.nil_append,a,b] using full

end DirectedFlowCutGap.RoundInputPackProgram
