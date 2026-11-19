import DirectedFlowCutGap.AdaptiveControllerStorage

/-! Execute one selected round and refresh the cache from the updated masks. -/

namespace DirectedFlowCutGap.AdaptiveRoundRefreshProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (StateAt CacheAt Parameters state_extend cache_extend parameters_extend)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge edge_extend)
open CandidateEnumeration (Node Network)

def roundLabel (pc : Fin 2451) : Fin 6878 := ⟨96+pc.val,by omega⟩
def refreshLabel (pc : Fin 4331) : Fin 6878 := ⟨2547+pc.val,by omega⟩

def program : Program 6878 := fun pc =>
  if pc.val<96 then
    match pc.val with
    | 0 => .call 16 1 .r0
    | 1 => .call 40 2 .r1
    | 2 => .call 64 3 .r3
    | 3 => .make .r3 (.pair .r1 .r3) 4
    | 16 => .call 28 17 .r3
    | 17 => .field .r2 .r2 false 18
    | 18 => .field .r2 .r2 false 19
    | 19 => .field .r2 .r2 true 20
    | 20 => .call (roundLabel 0) 21 .r3
    | 21 => .ret .r3
    | 28 => .field .r3 .r3 false 29
    | 29 => .field .r0 .r3 false 30
    | 30 => .field .r1 .r3 true 31
    | 31 => .field .r0 .r0 false 32
    | 32 => .field .r1 .r1 false 33
    | 33 => .make .r0 (.pair .r0 .r1) 34
    | 34 => .field .r2 .r2 false 35
    | 35 => .field .r2 .r2 false 36
    | 36 => .field .r2 .r2 false 37
    | 37 => .make .r3 (.pair .r2 .r0) 38
    | 38 => .ret .r3
    | 40 => .field .r3 .r3 false 41
    | 41 => .field .r3 .r3 true 42
    | 42 => .make .r3 (.pair .r0 .r3) 43
    | 43 => .ret .r3
    | 64 => .field .r0 .r2 false 65
    | 65 => .field .r0 .r0 true 66
    | 66 => .field .r2 .r0 true 67
    | 67 => .field .r0 .r0 false 68
    | 68 => .field .r3 .r1 true 69
    | 69 => .field .r3 .r3 true 70
    | 70 => .field .r1 .r1 false 71
    | 71 => .field .r1 .r1 false 72
    | 72 => .call 80 73 .r3
    | 73 => .field .r1 .r1 false 74
    | 74 => .call (refreshLabel 0) 75 .r3
    | 75 => .ret .r3
    | 80 => .field .r1 .r1 true 81
    | 81 => .make .r3 (.pair .r1 .r3) 82
    | 82 => .ret .r3
    | _ => .halt
  else if h : pc.val<2547 then
    if pc.val=106 then .ret .r3
    else ReferenceProgramLabels.instruction roundLabel (EpochSelectedRoundProgram.program ⟨pc.val-96,by omega⟩)
  else if pc.val=2556 then .ret .r3
  else ReferenceProgramLabels.instruction refreshLabel (CandidateRefreshProgram.program ⟨pc.val-2547,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 6878

def instructionBound (n L cells wordWidth sourceWidth weightsWidth scaleWidth : ℕ) : ℕ :=
  EpochSelectedRoundProgram.instructionBound n cells wordWidth sourceWidth weightsWidth+
    CandidateRefreshProgram.instructionBound n L n.size L.size scaleWidth+42

private theorem round_slots (pc : Fin 2451) (h : EpochSelectedRoundProgram.program pc≠.halt) :
    program (roundLabel pc)=ReferenceProgramLabels.instruction roundLabel (EpochSelectedRoundProgram.program pc) := by
  by_cases stop : pc.val=10
  · have eq : pc=10 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,roundLabel,show ¬96+pc.val<96 by omega,show 96+pc.val<2547 by omega,show 96+pc.val≠106 by omega]

private theorem refresh_slots (pc : Fin 4331) (h : CandidateRefreshProgram.program pc≠.halt) :
    program (refreshLabel pc)=ReferenceProgramLabels.instruction refreshLabel (CandidateRefreshProgram.program pc) := by
  by_cases stop : pc.val=9
  · have eq : pc=9 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,refreshLabel,show ¬2547+pc.val<96 by omega,show ¬2547+pc.val<2547 by omega,show 2547+pc.val≠2556 by omega]

set_option maxHeartbeats 2200000 in
private theorem environment_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M : Bits}
    {d : Data n} {optimum : ℕ} {candidate : Family n} {currentWords candidateWords : List (List Bits)} {scaleBits : Bits}
    (config : Parameters (L:=L) heap r.c adj R M)
    (cache : CacheAt heap r.d d optimum candidate currentWords candidateWords scaleBits)
    (stack : List (Frame ℕ 6878)) (tape : Bits) :
    ∃ ext env,RoundInputPackProgram.Environment (heap++ext) env (EpochSelectedRoundProgram.enumeration n) adj d currentWords ∧
      NaturalRun program 12 (state heap r stack tape 16) [] (state (heap++ext) (r.set .r3 env) stack tape 17) := by
  obtain ⟨live,best,atCache,stored,_⟩ := cache
  obtain ⟨packed,runtime,context,scale,weights,free,atState,updated,atRuntime,atContext,table,freeRep,scaleRep,_,_⟩ := stored
  obtain ⟨masks,mass,massBits,atPacked,maskRep,massRep,massValue⟩ := updated
  obtain ⟨static,gates,round,refresh,graph,roundConfig,pairs,shared,atConfig,atStatic,atRound,atRefresh,gate,
    ⟨enum,matrix,atGraph,enumRep,matrixRep⟩,someConfig,keys,family⟩ := config
  let frame : Frame ℕ 6878 := ⟨17,.r3,r⟩
  let saved := frame::stack
  let first : Registers ℕ := ⟨packed,r.b,r.c,live⟩
  let second : Registers ℕ := ⟨masks,context,r.c,live⟩
  have enter : NaturalRun program 3 (state heap r stack tape 16) [] (state heap first saved tape 30) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atCache,atState,first,frame,saved]
  have fields : NaturalRun program 3 (state heap first saved tape 30) [] (state heap second saved tape 33) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atState,atPacked,atRuntime,first,second]
  let fresh := heap.length
  let storedState : Cell ℕ := .pair masks context
  let environment : Cell ℕ := .pair graph fresh
  let mid := heap++[storedState]
  let ext : NaturalHeap := [storedState,environment]
  let third : Registers ℕ := ⟨fresh,context,graph,live⟩
  have hasConfig : mid[r.c]?=some (.pair static gates) := lookup_extend atConfig _
  have hasStatic : mid[static]?=some (.pair round refresh) := lookup_extend atStatic _
  have hasRound : mid[round]?=some (.pair graph roundConfig) := lookup_extend atRound _
  have pack : NaturalRun program 4 (state heap second saved tape 33) [] (state mid third saved tape 37) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,hasConfig,hasStatic,hasRound,second,third,storedState,mid,fresh]
  have finish : NaturalRun program 2 (state mid third saved tape 37) []
      (state (heap++ext) (r.set .r3 (fresh+1)) stack tape 17) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,third,frame,saved,ext,mid,environment,fresh]
  have rep : RoundInputPackProgram.Environment (heap++ext) (fresh+1) (EpochSelectedRoundProgram.enumeration n) adj d currentWords :=
    ⟨graph,fresh,by simp [ext,environment,fresh],
      ⟨enum,matrix,lookup_extend atGraph ext,GraphDiscoveryProgram.vertices_extend enumRep ext,
        GraphAdjacencyProgram.matrix_extend matrixRep ext⟩,
      ⟨masks,context,weights,free,by simp [ext,storedState,fresh],lookup_extend atContext ext,
        RoundInputPackProgram.masks_extend maskRep ext,RoundInputPackProgram.weights_extend table ext,lookup_extend freeRep ext⟩⟩
  exact ⟨ext,fresh+1,rep,append_run enter (append_run fields (append_run pack finish))⟩

set_option maxHeartbeats 1500000 in
private theorem round_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {p : Pair n} {R M : Bits}
    {d : Data n} {optimum : ℕ} {candidate : Family n} {currentWords candidateWords : List (List Bits)} {scaleBits : Bits}
    {cells : List (Pair n×Bits)} (key : Edge heap r.a (labelPair p)) (grid : EpochGridLookupProgram.Table heap r.b cells)
    (config : Parameters (L:=L) heap r.c adj R M) (cache : CacheAt heap r.d d optimum candidate currentWords candidateWords scaleBits)
    (tape : Bits) :
    ∃ ext root,RoundStateUpdateProgram.UpdatedAt (heap++ext) root (EncodedRoundingState.roundData d p
        (PhysicalSampledRoundProgram.cut (EpochSelectedRoundProgram.enumeration n) adj d p (EpochGridLookupProgram.word p cells))).1 ∧
      NaturalRun program (EpochSelectedRoundProgram.steps adj d p cells currentWords+19)
        (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  let frame : Frame ℕ 6878 := ⟨1,.r0,r⟩
  have start : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 16,[],0⟩ := rfl
  obtain ⟨ee,env,rep,prepare⟩ := environment_call config cache [frame] tape
  let mid := heap++ee
  let withEnv := r.set .r3 env
  obtain ⟨static,gates,round,refresh,graph,roundConfig,pairs,shared,atConfig,atStatic,atRound,atRefresh,gate,
    graphRep,roundConfigRep,keys,family⟩ := parameters_extend config ee
  let args := withEnv.set .r2 roundConfig
  have fields : NaturalRun program 3 (state mid withEnv [frame] tape 17) [] (state mid args [frame] tape 20) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atConfig,atStatic,atRound,args,withEnv,mid]
  obtain ⟨s,b,rootRep,stateRep,output⟩ := cache_extend cache ee
  obtain ⟨packed,runtime,context,scale,weights,free,atState,hout,atRuntime,atContext,table,freeRep,scaleRep,_,data⟩ := stateRep
  obtain ⟨er,out,root,updated,body⟩ := EpochSelectedRoundProgram.natural_round (r:=args)
    (edge_extend key ee) (EpochGridLookupProgram.table_extend grid ee) roundConfigRep rep data tape
  have invoke := ReferenceProgramInvocation.call roundLabel round_slots (caller:=20) (continuation:=21)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++er) (args.set .r3 root) [frame] tape 21
  have round : NaturalRun program (EpochSelectedRoundProgram.steps adj d p cells currentWords+2)
      (state mid args [frame] tape 20) [] stop := by
    simpa only [mid,stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (mid++er) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ee++er,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using updated
  · let k := EpochSelectedRoundProgram.steps adj d p cells currentWords
    have count : 12+(3+(k+2+1))+1=k+19 := by omega
    change NaturalRun program (k+19) _ [] _
    rw [← count]
    simpa only [k,mid,List.append_assoc,List.nil_append] using
      NaturalRun.step start (append_run prepare (append_run fields (append_run round (.step ret (.done _)))))

private theorem replace_state {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {d next : Data n}
    {optimum : ℕ} {candidate : Family n} {currentWords candidateWords : List (List Bits)} {bits : Bits}
    (cache : CacheAt heap r.d d optimum candidate currentWords candidateWords bits)
    (updated : RoundStateUpdateProgram.UpdatedAt heap r.a next)
    (weightsEq : next.weights=d.weights) (scaleEq : next.scale=d.scale) (tape : Bits) :
    ∃ extra root,StateAt (heap++extra) root next currentWords bits ∧
      NaturalRun program 5 (state heap r [] tape 1) [] (state (heap++extra) (r.set .r1 root) [] tape 2) := by
  obtain ⟨s,b,atCache,stored,candidateRep⟩ := cache
  obtain ⟨packed,runtime,context,scale,weights,free,atState,out,atRuntime,atContext,table,freeRep,scaleRep,scaleValue,data⟩ := stored
  let record : Cell ℕ := .pair r.a runtime
  let extra : NaturalHeap := [record]
  let frame : Frame ℕ 6878 := ⟨2,.r1,r⟩
  let args := r.set .r3 s
  have enter : NaturalRun program 2 (state heap r [] tape 1) [] (state heap args [frame] tape 41) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atCache]
  have finish : NaturalRun program 3 (state heap args [frame] tape 41) []
      (state (heap++extra) (r.set .r1 heap.length) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atState,allocateNatural,Recipe.cell,extra,record]
  have rep : StateAt (heap++extra) heap.length next currentWords bits :=
    ⟨r.a,runtime,context,scale,weights,free,by simp [extra,record],AdaptiveControllerStorage.updated_extend updated extra,
      lookup_extend atRuntime extra,lookup_extend atContext extra,RoundInputPackProgram.weights_extend table extra,
      lookup_extend freeRep extra,boolList_extend scaleRep extra,scaleEq.symm ▸ scaleValue,weightsEq.symm ▸ data⟩
  exact ⟨extra,heap.length,rep,append_run enter finish⟩

set_option maxHeartbeats 2300000 in
private theorem refresh_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M scaleBits : Bits}
    {demands : Finset (Pair n)} (s : Code (EncodedIntegerShortestPaths.graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {words : List (List Bits)} (stored : StateAt heap r.b s.data words scaleBits)
    (config : Parameters (L:=L) heap r.c adj R M) (tape : Bits) :
    let D : EncodedCandidateCapacity.Input n := ⟨adj,s.data.cut⟩
    let next := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) s
    let candidateWords := CandidateFamilyData.familyWords D s.data.remaining (4*s.data.scale) L.bits EN E
    ∃ (ext : NaturalHeap) (root k : ℕ),CandidateRefreshProgram.Output (heap++ext) root next.candidate next.optimal candidateWords ∧
      NaturalRun program k (state heap r [] tape 2) [] (state (heap++ext) (r.set .r3 root) [] tape 3) ∧
      k ≤ CandidateRefreshProgram.instructionBound n L n.size L.size scaleBits.length+17 := by
  let D : EncodedCandidateCapacity.Input n := ⟨adj,s.data.cut⟩
  obtain ⟨packed,runtime,context,scale,weights,free,atState,updated,atRuntime,atContext,table,freeRep,scaleRep,scaleValue,data⟩ := stored
  obtain ⟨masks,mass,massBits,atPacked,⟨active,cut,atMasks,activeRep,cutRep⟩,massRep,massValue⟩ := updated
  obtain ⟨static,gates,round,refreshCtx,graph,roundConfig,pairs,shared,atConfig,atStatic,atRound,atRefresh,gate,
    graphRep,configRep,pairsRep,sharedRep⟩ := config
  let frame : Frame ℕ 6878 := ⟨3,.r3,r⟩
  let first := r.set .r0 refreshCtx
  let second : Registers ℕ := ⟨pairs,r.b,shared,r.d⟩
  let third : Registers ℕ := ⟨pairs,masks,shared,scale⟩
  have staticFields : NaturalRun program 3 (state heap r [] tape 2) [] (state heap first [frame] tape 66) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atConfig,atStatic,first,frame]
  have graphFields : NaturalRun program 2 (state heap first [frame] tape 66) [] (state heap second [frame] tape 68) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atRefresh,first,second]
  have stateFields : NaturalRun program 4 (state heap second [frame] tape 68) [] (state heap third [frame] tape 72) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atState,atPacked,atRuntime,second,third]
  let record : Cell ℕ := .pair cut scale
  let mid := heap++[record]
  let fourth := third.set .r3 heap.length
  let args := fourth.set .r1 active
  have pack : NaturalRun program 4 (state heap third [frame] tape 72) [] (state mid fourth [frame] tape 73) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,atMasks,third,fourth,record,mid]
  have read : mid[masks]?=some (.pair active cut) := lookup_extend atMasks _
  have select : tickNatural program (state mid fourth [frame] tape 73)=some ⟨state mid args [frame] tape 74,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,read,args,fourth,third]
  have stateRep : CandidateFamilyProgram.StateAt mid args.d D scaleBits :=
    ⟨cut,scale,by simp [mid,args,fourth,Registers.set,record],boolList_extend cutRep _,boolList_extend scaleRep _⟩
  have sharedAt : CandidateFamilyProgram.Shared mid args.c D n.bits L.bits :=
    AdaptiveControllerStorage.shared_extend sharedRep [record]
  have activeAt : RetainedDemandEraseProgram.RowsAt mid args.b s.data.remaining := by
    obtain ⟨refs,stored,flags⟩ := activeRep
    exact ⟨refs,BinaryPointerListRead.pointerList_extend stored _,flags.imp (fun _ _ rep => boolList_extend rep _)⟩
  obtain ⟨ext,out,root,k,refreshed,body,within⟩ := CandidateRefreshProgram.natural_refresh (r:=args) (D:=D)
    s rfl positive EN E (GraphWalkExtension.edgeList_extend pairsRep [record]) activeAt sharedAt stateRep
    (value_bits n) (value_bits L) scaleValue tape
  have invoke := ReferenceProgramInvocation.call refreshLabel refresh_slots (caller:=74) (continuation:=75)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++ext) (args.set .r3 root) [frame] tape 75
  have run : NaturalRun program (k+2) (state mid args [frame] tape 74) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) [] tape 3,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨[record]++ext,root,k+17,?_,?_,?_⟩
  · rw [← List.append_assoc]
    exact refreshed
  · have count : 3+(2+(4+(4+((k+2+1)+1))))=k+17 := by omega
    rw [← count]
    simpa only [mid,List.append_assoc,List.nil_append] using append_run staticFields (append_run graphFields
      (append_run stateFields (append_run pack (.step select (append_run run (.step ret (.done _)))))))
  · simpa only [Nat.size_eq_bits_len] using Nat.add_le_add_right within 17

set_option maxHeartbeats 2300000 in
theorem natural_round_refresh {n L W B : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (EncodedIntegerShortestPaths.graph adj) demands L)
    {p : Pair n} (hp : p∈(interpret s).remaining) (positive : 0<L) (j : Fin L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scaleBits : Bits} {oldOptimal : ℕ} {oldCandidate : Family n} {words oldWords : List (List Bits)}
    {cells : List (Pair n×Bits)} (sample : value (EpochGridLookupProgram.word p cells)=j.val)
    (key : Edge heap r.a (labelPair p)) (grid : EpochGridLookupProgram.Table heap r.b cells)
    (params : Parameters (L:=L) heap r.c adj R M)
    (cache : CacheAt heap r.d s.data oldOptimal oldCandidate words oldWords scaleBits)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidth : ∀ v : Fin n,(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidth : (EpochGridLookupProgram.word p cells).length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B) (tape : Bits) :
    let next := sampleRound positive (EncodedRoundingInput.cutOracle (EpochSelectedRoundProgram.enumeration n) adj positive)
      s p hp j
    let result := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) next
    let candidateWords := CandidateFamilyData.familyWords ⟨adj,next.data.cut⟩ next.data.remaining (4*next.data.scale) L.bits EN E
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      CacheAt (heap++ext) root next.data result.optimal result.candidate words candidateWords scaleBits ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound n L cells.length W p.1.val.bits.length B scaleBits.length := by
  let C := EncodedRoundingInput.cutOracle (EpochSelectedRoundProgram.enumeration n) adj positive
  let next := sampleRound positive C s p hp j
  let result := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) next
  let candidateWords := CandidateFamilyData.familyWords ⟨adj,next.data.cut⟩ next.data.remaining (4*next.data.scale) L.bits EN E
  obtain ⟨ec,packed,updated,cutRun⟩ := round_call key grid params cache tape
  have sameCut : PhysicalSampledRoundProgram.cut (EpochSelectedRoundProgram.enumeration n) adj s.data p
        (EpochGridLookupProgram.word p cells)=C.cut (row s.data.weights p) p.1 j := by
    unfold PhysicalSampledRoundProgram.cut C EncodedRoundingInput.cutOracle
    rw [sample]
  rw [sameCut,EncodedRoundingState.roundData_value] at updated
  let mid := heap++ec
  let cutArgs := r.set .r0 packed
  have cutOutput : RoundStateUpdateProgram.UpdatedAt mid cutArgs.a next.data := updated
  have weightsEq : next.data.weights=s.data.weights := rfl
  have scaleEq : next.data.scale=s.data.scale := rfl
  obtain ⟨es,sroot,stateRep,stateRun⟩ := replace_state (r:=cutArgs) (cache_extend cache ec) cutOutput weightsEq scaleEq tape
  let grown := mid++es
  let ready := cutArgs.set .r1 sroot
  obtain ⟨ef,newCandidate,k,candidateRep,refreshRun,within⟩ := refresh_call (r:=ready) next positive EN E stateRep
    (parameters_extend (parameters_extend params ec) es) tape
  let final := grown++ef
  let root := final.length
  let cell : Cell ℕ := .pair sroot newCandidate
  have pack : NaturalRun program 1 (state final (ready.set .r3 newCandidate) [] tape 3) []
      (state (final++[cell]) (ready.set .r3 root) [] tape 4) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,ready,root,cell]
  have stored : CacheAt (final++[cell]) root next.data result.optimal result.candidate words candidateWords scaleBits :=
    ⟨sroot,newCandidate,by simp [root,cell],state_extend (state_extend stateRep ef) [cell],
      AdaptiveControllerStorage.candidate_extend candidateRep [cell]⟩
  have data : RetainedMassTableProgram.DataRows s.data.weights words := by
    obtain ⟨_,_,_,⟨_,_,_,_,_,_,_,_,_,_,_,_,_,data⟩,_⟩ := cache
    exact data.2
  have bound := EpochSelectedRoundProgram.steps_le adj s.data p cells words data hW vertexWidth rowWidth levelWidth weightWidths
  refine ⟨ec++es++ef++[cell],ready,root,(EpochSelectedRoundProgram.steps adj s.data p cells words+19)+(5+(k+1)),?_,?_,?_⟩
  · simpa only [next,C,result,candidateWords,final,grown,mid,List.append_assoc] using stored
  · simpa only [final,grown,mid,cutArgs,ready,List.append_assoc,List.nil_append] using
      append_run cutRun (append_run stateRun (append_run refreshRun pack))
  · unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 6878) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

theorem physical_round_refresh {n L W B H A : ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (EncodedIntegerShortestPaths.graph adj) demands L)
    {p : Pair n} (hp : p∈(interpret s).remaining) (positive : 0<L) (j : Fin L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scaleBits : Bits} {oldOptimal : ℕ} {oldCandidate : Family n} {words oldWords : List (List Bits)}
    {cells : List (Pair n×Bits)} (sample : value (EpochGridLookupProgram.word p cells)=j.val)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidth : ∀ v : Fin n,(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidth : (EpochGridLookupProgram.word p cells).length≤W) (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (initial : BitState 6878) (bounded : initial.Bounded H A) (entry : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (key : Edge (eraseState initial).heap (eraseState initial).registers.a (labelPair p))
    (grid : EpochGridLookupProgram.Table (eraseState initial).heap (eraseState initial).registers.b cells)
    (params : Parameters (L:=L) (eraseState initial).heap (eraseState initial).registers.c adj R M)
    (cache : CacheAt (eraseState initial).heap (eraseState initial).registers.d s.data oldOptimal oldCandidate words oldWords scaleBits) :
    let next := sampleRound positive (EncodedRoundingInput.cutOracle (EpochSelectedRoundProgram.enumeration n) adj positive) s p hp j
    let result := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) next
    let candidateWords := CandidateFamilyData.familyWords ⟨adj,next.data.cut⟩ next.data.remaining (4*next.data.scale) L.bits EN E
    ∃ (paid k : ℕ) (out : BitState 6878),Run program k paid initial [] out ∧
      CacheAt (eraseState out).heap (eraseState out).registers.d next.data result.optimal result.candidate words candidateWords scaleBits ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ out.pc=4 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧ (attempt program out).result=none ∧
      paid+(attempt program out).operations ≤ completeBound 6878 H A (instructionBound n L cells.length W p.1.val.bits.length B scaleBits.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,within⟩ := natural_round_refresh s hp positive j EN E sample key grid params cache
    hW vertexWidth rowWidth levelWidth weightWidths old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 4
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old entry empty hn]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,actual,finalState,stopped,cost,tape⟩ := terminating_simulation bounded run halt
  refine ⟨paid,k,out,actual,?_,tape,?_,?_,⟨ext,?_⟩,stopped,cost.trans ?_⟩
  · rw [finalState]; exact rep
  · rw [finalState]; rfl
  · exact congrArg (fun s : NaturalState 6878 => s.pc) finalState
  · rw [finalState]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ within

end DirectedFlowCutGap.AdaptiveRoundRefreshProgram
