import DirectedFlowCutGap.InitialGraphDictionary
import DirectedFlowCutGap.InitialDemandMaskProgram

/-! Assemble the query and controller records from the stored original graph. -/

namespace DirectedFlowCutGap.InitialGraphContexts

open BooleanTableRead (BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open RetainedGridState (PairFlags)
open InitialGraphDictionary (label labels as_vertices)
open InitialUniformTables (unitWord)
open PathCostMaterialization (WordList list_extend)
open GraphWalkExtension (EdgeList edgeList_extend)
open EpochActiveFromMaskProgram (labelPair)

abbrev enumeration := ResidualSearch.Enumeration.fin

def Input {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n) : Prop :=
  ∃ matrix dims count fields grid one,heap[root]?=some (.pair matrix dims) ∧
    heap[dims]?=some (.pair count fields) ∧ heap[fields]?=some (.pair grid one) ∧
    GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adj) ∧
    BoolList heap count n.bits ∧ BoolList heap grid L.bits ∧ BoolList heap one unitWord

def Dictionary {n : ℕ} (heap : NaturalHeap) (root : ℕ) : Prop :=
  ∃ vertices pairs,heap[root]?=some (.pair vertices pairs) ∧ WordList heap vertices (labels n) ∧
    EdgeList heap pairs ((RetainedMassTableProgram.pairOrder n).map labelPair)

def program : Program 112 := fun pc => match pc.val with
  | 0 => .call 16 1 .r3
  | 1 => .call 32 2 .r0
  | 2 => .make .r3 (.pair .r0 .r3) 3
  | 16 => .field .r3 .r3 false 17
  | 17 => .field .r2 .r1 false 18
  | 18 => .make .r3 (.pair .r2 .r3) 19
  | 19 => .field .r0 .r0 false 20
  | 20 => .make .r3 (.pair .r0 .r3) 21
  | 21 => .field .r1 .r1 true 22
  | 22 => .field .r1 .r1 true 23
  | 23 => .field .r1 .r1 false 24
  | 24 => .make .r3 (.pair .r3 .r1) 25
  | 25 => .ret .r3
  | 32 => .call 48 33 .r3
  | 33 => .call 80 34 .r1
  | 34 => .make .r0 (.pair .r3 .r1) 35
  | 35 => .make .r3 (.pair .r0 .r2) 36
  | 36 => .ret .r3
  | 48 => .field .r0 .r0 false 49
  | 49 => .field .r3 .r1 false 50
  | 50 => .make .r0 (.pair .r0 .r3) 51
  | 51 => .field .r1 .r1 true 52
  | 52 => .field .r3 .r1 false 53
  | 53 => .field .r1 .r1 true 54
  | 54 => .field .r1 .r1 true 55
  | 55 => .make .r1 (.pair .r3 .r1) 56
  | 56 => .make .r3 (.pair .r0 .r1) 57
  | 57 => .ret .r3
  | 80 => .call 96 81 .r3
  | 81 => .field .r0 .r0 true 82
  | 82 => .make .r3 (.pair .r0 .r3) 83
  | 83 => .ret .r3
  | 96 => .field .r3 .r1 false 97
  | 97 => .field .r1 .r1 true 98
  | 98 => .field .r2 .r1 false 99
  | 99 => .make .r2 (.pair .r3 .r2) 100
  | 100 => .field .r1 .r1 true 101
  | 101 => .field .r1 .r1 false 102
  | 102 => .field .r0 .r0 false 103
  | 103 => .make .r0 (.pair .r0 .r1) 104
  | 104 => .make .r3 (.pair .r2 .r0) 105
  | 105 => .ret .r3
  | _ => .halt

abbrev state := @ReferenceProgramInvocation.state 112

theorem input_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap root adj) (ext : NaturalHeap) : Input (L:=L) (heap++ext) root adj := by
  obtain ⟨matrix,dims,count,fields,grid,one,atRoot,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  exact ⟨matrix,dims,count,fields,grid,one,lookup_extend atRoot ext,lookup_extend atDims ext,lookup_extend atFields ext,
    GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend nRep ext,boolList_extend lRep ext,boolList_extend tRep ext⟩

theorem dictionary_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} (d : Dictionary (n:=n) heap root) (ext : NaturalHeap) :
    Dictionary (n:=n) (heap++ext) root := by
  obtain ⟨vertices,pairs,atRoot,v,p⟩ := d
  exact ⟨vertices,pairs,lookup_extend atRoot ext,list_extend v ext,edgeList_extend p ext⟩

set_option maxHeartbeats 2600000 in
private theorem make_query {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap r.b adj) (dict : Dictionary (n:=n) heap r.a)
    (tables : ∃ fractions weights,heap[r.d]?=some (.pair fractions weights) ∧
      WordPairTableRead.Table heap fractions (List.replicate n (unitWord,unitWord))) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      InitialDemandMaskProgram.Context (heap++ext) root adj (enumeration n) label L.bits ∧
      NaturalRun program 11 (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  obtain ⟨vertices,pairs,atDict,labelsRep,pairsRep⟩ := dict
  obtain ⟨fractions,weights,atTables,table⟩ := tables
  let frame : Frame ℕ 112 := ⟨1,.r3,r⟩
  let args : Registers ℕ := ⟨r.a,r.b,matrix,fractions⟩
  have load : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [frame] tape 18) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atInput,atTables]
  let base := heap.length
  let first : Cell ℕ := .pair matrix fractions
  let second : Cell ℕ := .pair vertices base
  let third : Cell ℕ := .pair (base+1) grid
  let mid := heap++[first,second]
  let next : Registers ℕ := ⟨vertices,r.b,matrix,base+1⟩
  have shared : NaturalRun program 3 (state heap args [frame] tape 18) []
      (state mid next [frame] tape 21) := by
    have atKey : (heap++[first])[r.a]?=some (.pair vertices pairs) := lookup_extend atDict _
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,mid,next,base,first,second,atKey,allocateNatural,Recipe.cell]
  have a : mid[r.b]?=some (.pair matrix dims) := lookup_extend atInput _
  have b : mid[dims]?=some (.pair count fields) := lookup_extend atDims _
  have c : mid[fields]?=some (.pair grid one) := lookup_extend atFields _
  let ext : NaturalHeap := [first,second,third]
  have finish : NaturalRun program 5 (state mid next [frame] tape 21) []
      (state (heap++ext) (r.set .r3 (base+2)) [] tape 1) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      a,b,c,next,mid,base,ext,first,second,third,frame,allocateNatural,Recipe.cell]
  have tableFields := BinaryIndexedPairRead.table_extend table ext
  rw [← InitialUniformTables.fraction_fields] at tableFields
  refine ⟨ext,base+2,⟨base+1,grid,by simp [base,ext,third],boolList_extend lRep ext,
    ⟨vertices,base,matrix,fractions,by simp [base,ext,second],by simp [base,ext,first],
      GraphDiscoveryProgram.vertices_extend (as_vertices labelsRep) ext,GraphAdjacencyProgram.matrix_extend graph ext,tableFields⟩⟩,
    append_run load (append_run shared finish)⟩

set_option maxHeartbeats 2600000 in
private theorem make_round {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap r.b adj) (dict : Dictionary (n:=n) heap r.a)
    (stack : List (Frame ℕ 112)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ), (∃ graph cfg,(heap++ext)[root]?=some (.pair graph cfg) ∧
      RoundInputPackProgram.GraphAt (heap++ext) graph (enumeration n) adj ∧ EpochSelectedRoundProgram.config (heap++ext) cfg n) ∧
      NaturalRun program 11 (state heap r stack tape 32) [] (state (heap++ext) (r.set .r3 root) stack tape 33) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  obtain ⟨vertices,pairs,atDict,labelsRep,pairsRep⟩ := dict
  let frame : Frame ℕ 112 := ⟨33,.r3,r⟩
  let args : Registers ℕ := ⟨vertices,r.b,r.c,matrix⟩
  have load : NaturalRun program 3 (state heap r stack tape 32) []
      (state heap args (frame::stack) tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atInput,atDict]
  let base := heap.length
  let first : Cell ℕ := .pair vertices matrix
  let mid := heap++[first]
  let next : Registers ℕ := ⟨base,one,r.c,count⟩
  have a : mid[r.b]?=some (.pair matrix dims) := lookup_extend atInput _
  have b : mid[dims]?=some (.pair count fields) := lookup_extend atDims _
  have c : mid[fields]?=some (.pair grid one) := lookup_extend atFields _
  have geometry : NaturalRun program 5 (state heap args (frame::stack) tape 50) []
      (state mid next (frame::stack) tape 55) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,mid,base,first,a,b,c,next,allocateNatural,Recipe.cell]
  let second : Cell ℕ := .pair count one
  let third : Cell ℕ := .pair base (base+1)
  let ext : NaturalHeap := [first,second,third]
  have finish : NaturalRun program 3 (state mid next (frame::stack) tape 55) []
      (state (heap++ext) (r.set .r3 (base+2)) stack tape 33) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      next,mid,base,ext,first,second,third,frame,allocateNatural,Recipe.cell,Nat.add_assoc]
  exact ⟨ext,base+2,⟨base,base+1,by simp [base,ext,third],
    ⟨vertices,matrix,by simp [base,ext,first],GraphDiscoveryProgram.vertices_extend (as_vertices labelsRep) ext,
      GraphAdjacencyProgram.matrix_extend graph ext⟩,
    ⟨count,one,by simp [base,ext,second],boolList_extend nRep ext,boolList_extend tRep ext⟩⟩,
    append_run load (append_run geometry finish)⟩

set_option maxHeartbeats 2600000 in
private theorem make_refresh {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (input : Input (L:=L) heap r.b adj) (dict : Dictionary (n:=n) heap r.a)
    (stack : List (Frame ℕ 112)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ), (∃ pairs shared,(heap++ext)[root]?=some (.pair pairs shared) ∧
      EdgeList (heap++ext) pairs ((RetainedMassTableProgram.pairOrder n).map labelPair) ∧
      CandidateFamilyProgram.Shared (heap++ext) shared ⟨adj,Vector.replicate n false⟩ n.bits L.bits) ∧
      NaturalRun program 15 (state heap r stack tape 33) [] (state (heap++ext) (r.set .r1 root) stack tape 34) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,tRep⟩ := input
  obtain ⟨vertices,pairs,atDict,labelsRep,pairsRep⟩ := dict
  let frame : Frame ℕ 112 := ⟨34,.r1,r⟩
  let inner : Frame ℕ 112 := ⟨81,.r3,r⟩
  let saved := inner::frame::stack
  let args : Registers ℕ := ⟨r.a,dims,count,matrix⟩
  have load : NaturalRun program 5 (state heap r stack tape 33) [] (state heap args saved tape 99) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,saved,inner,frame,atInput,atDims]
  let base := heap.length
  let first : Cell ℕ := .pair matrix count
  let second : Cell ℕ := .pair vertices grid
  let third : Cell ℕ := .pair base (base+1)
  let fourth : Cell ℕ := .pair pairs (base+2)
  let mid := heap++[first]
  let next : Registers ℕ := ⟨r.a,dims,base,matrix⟩
  have makeGraph : tickNatural program (state heap args saved tape 99)=some ⟨state mid next saved tape 100,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,next,mid,base,first,allocateNatural,Recipe.cell]
  have b : mid[dims]?=some (.pair count fields) := lookup_extend atDims _
  have c : mid[fields]?=some (.pair grid one) := lookup_extend atFields _
  have a : mid[r.a]?=some (.pair vertices pairs) := lookup_extend atDict _
  let ready : Registers ℕ := ⟨vertices,grid,base,matrix⟩
  have loadGrid : NaturalRun program 3 (state mid next saved tape 100) [] (state mid ready saved tape 103) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,next,ready,a,b,c]
  let grown := heap++[first,second,third]
  let withShared := r.set .r3 (base+2)
  have pack : NaturalRun program 3 (state mid ready saved tape 103) []
      (state grown withShared (frame::stack) tape 81) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      mid,grown,ready,withShared,base,first,second,third,saved,inner,allocateNatural,Recipe.cell]
  let ext : NaturalHeap := [first,second,third,fourth]
  have loc : grown[r.a]?=some (.pair vertices pairs) := lookup_extend atDict _
  have finish : NaturalRun program 3 (state grown withShared (frame::stack) tape 81) []
      (state (heap++ext) (r.set .r1 (base+3)) stack tape 34) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      grown,withShared,base,ext,first,second,third,fourth,frame,loc,allocateNatural,Recipe.cell]
  have graphAt : CandidateDemandRowProgram.GraphSizeAt (heap++ext) base ⟨adj,Vector.replicate n false⟩ n.bits :=
    ⟨matrix,count,by simp [base,ext,first],GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend nRep ext⟩
  exact ⟨ext,base+3,⟨pairs,base+2,by simp [base,ext,fourth],edgeList_extend pairsRep ext,
    ⟨base,base+1,vertices,grid,labels n,by simp [base,ext,third],by simp [base,ext,second],graphAt,
      GraphDiscoveryProgram.vertices_extend (as_vertices labelsRep) ext,by simp [labels],boolList_extend lRep ext⟩⟩,
    append_run load (.step makeGraph (append_run loadGrid (append_run pack finish)))⟩

set_option maxHeartbeats 2500000 in
private theorem make_parameters {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M : Bits}
    (input : Input (L:=L) heap r.b adj) (dict : Dictionary (n:=n) heap r.a)
    (gates : AdaptiveGatesProgram.Parameters heap r.c R M) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),AdaptiveControllerStorage.Parameters (L:=L) (heap++ext) root adj R M ∧
      NaturalRun program 30 (state heap r [] tape 1) [] (state (heap++ext) (r.set .r0 root) [] tape 2) := by
  let frame : Frame ℕ 112 := ⟨2,.r0,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape 32,[],0⟩ := rfl
  obtain ⟨er,round,⟨graph,cfg,atRound,
    ⟨vs,matrix,atGraph,labelRep,adjRep⟩,⟨count,one,atConfig,nRep,tRep⟩⟩,roundRun⟩ := make_round input dict [frame] tape
  let mid := heap++er
  let args := r.set .r3 round
  obtain ⟨ef,refresh,⟨pairs,shared,atRefresh,pairRep,sharedRep⟩,refreshRun⟩ :=
    make_refresh (r:=args) (input_extend input er) (dictionary_extend dict er) [frame] tape
  let grown := mid++ef
  let finalRegs := args.set .r1 refresh
  let static : Cell ℕ := .pair round refresh
  let params : Cell ℕ := .pair grown.length r.c
  let out : NaturalHeap := [static,params]
  let root := grown.length+1
  have save : NaturalRun program 3 (state grown finalRegs [frame] tape 34) []
      (state (grown++out) (r.set .r0 root) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,finalRegs,static,params,out,root,frame,allocateNatural,Recipe.cell]
  have s : (grown++out)[grown.length]?=some static := by simp [out]
  have p : (grown++out)[root]?=some params := by simp [root,out]
  have rep : AdaptiveControllerStorage.Parameters (L:=L) (grown++out) root adj R M :=
    ⟨grown.length,r.c,round,refresh,graph,cfg,pairs,shared,p,s,
      lookup_extend (lookup_extend atRound ef) out,lookup_extend atRefresh out,
      AdaptiveGatesProgram.parameters_extend (AdaptiveGatesProgram.parameters_extend (AdaptiveGatesProgram.parameters_extend gates er) ef) out,
      ⟨vs,matrix,lookup_extend (lookup_extend atGraph ef) out,
        GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend labelRep ef) out,
        GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend adjRep ef) out⟩,
      ⟨count,one,lookup_extend (lookup_extend atConfig ef) out,boolList_extend (boolList_extend nRep ef) out,
        boolList_extend (boolList_extend tRep ef) out⟩,
      edgeList_extend pairRep out,AdaptiveControllerStorage.shared_extend sharedRep out⟩
  refine ⟨er++ef++out,root,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using rep
  · simpa only [grown,mid,List.append_assoc,List.nil_append] using
      NaturalRun.step enter (append_run roundRun (append_run refreshRun save))

set_option maxHeartbeats 2000000 in
theorem natural_contexts {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M : Bits}
    (input : Input (L:=L) heap r.b adj) (dict : Dictionary (n:=n) heap r.a)
    (tables : ∃ fractions weights,heap[r.d]?=some (.pair fractions weights) ∧
      WordPairTableRead.Table heap fractions (List.replicate n (unitWord,unitWord)))
    (gates : AdaptiveGatesProgram.Parameters heap r.c R M) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root params query : ℕ),
      (heap++ext)[root]?=some (.pair params query) ∧
      AdaptiveControllerStorage.Parameters (L:=L) (heap++ext) params adj R M ∧
      InitialDemandMaskProgram.Context (heap++ext) query adj (enumeration n) label L.bits ∧
      NaturalRun program 42 (state heap r [] tape 0) []
        (state (heap++ext) ⟨params,r.b,r.c,root⟩ [] tape 3) := by
  obtain ⟨eq,query,queryRep,queryRun⟩ := make_query input dict tables tape
  let mid := heap++eq
  let args := r.set .r3 query
  obtain ⟨ep,params,paramsRep,paramsRun⟩ := make_parameters (r:=args) (input_extend input eq) (dictionary_extend dict eq)
    (AdaptiveGatesProgram.parameters_extend gates eq) tape
  let grown := mid++ep
  let record : Cell ℕ := .pair params query
  have finish : tickNatural program (state grown (args.set .r0 params) [] tape 2)=
      some ⟨state (grown++[record]) ⟨params,r.b,r.c,grown.length⟩ [] tape 3,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,record,allocateNatural,Recipe.cell]
  have loc : (grown++[record])[grown.length]?=some record := by simp
  refine ⟨eq++ep++[record],grown.length,params,query,?_,?_,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc,record] using loc
  · simpa only [grown,mid,List.append_assoc] using AdaptiveControllerStorage.parameters_extend paramsRep [record]
  · simpa only [grown,mid,List.append_assoc] using InitialDemandMaskProgram.context_extend
      (InitialDemandMaskProgram.context_extend queryRep ep) [record]
  · simpa only [grown,mid,List.append_assoc,List.nil_append] using append_run queryRun (append_run paramsRun (.step finish (.done _)))

end DirectedFlowCutGap.InitialGraphContexts
