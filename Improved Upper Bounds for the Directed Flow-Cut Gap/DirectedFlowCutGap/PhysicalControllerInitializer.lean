import DirectedFlowCutGap.InitialSeedProgram
import DirectedFlowCutGap.AdaptiveControllerExecution

/-! Start the actual adaptive controller from the original stored graph. -/

namespace DirectedFlowCutGap.PhysicalControllerInitializer

open BooleanTableRead (IndexSpine BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open RetainedGridState (PairFlags)
open InitialGraphContexts (Input input_extend enumeration)
open InitialUniformTables (words unitWord)
open AdaptiveControllerProgram (Settings settings_extend)
open EpochScanData (Graph Stored stored_extend)
open CandidateEnumeration (Node Network)

def seedLabel (pc : Fin 3589) : Fin 10935 := ⟨128+pc.val,by omega⟩
def stateLabel (pc : Fin 340) : Fin 10935 := ⟨3717+pc.val,by omega⟩
def refreshLabel (pc : Fin 6878) : Fin 10935 := ⟨4057+pc.val,by omega⟩

def program : Program 10935 := fun pc =>
  if pc.val < 128 then
    match pc.val with
    | 0 => .call 16 1 .r2
    | 1 => .call 64 2 .r3
    | 2 => .call 96 3 .r0
    | 3 => .call 112 4 .r3
    | 4 => .move .r2 .r0 5
    | 5 => .field .r0 .r1 true 6
    | 6 => .field .r0 .r0 false 7
    | 16 => .field .r1 .r1 false 17
    | 17 => .call (seedLabel 0) 18 .r3
    | 18 => .ret .r3
    | 64 => .field .r0 .r0 true 65
    | 65 => .field .r0 .r0 true 66
    | 66 => .field .r0 .r0 true 67
    | 67 => .make .r3 (.flag false) 68
    | 68 => .make .r3 (.pair .r0 .r3) 69
    | 69 => .field .r0 .r2 false 70
    | 70 => .field .r1 .r0 true 71
    | 71 => .field .r0 .r0 false 72
    | 72 => .field .r2 .r2 true 73
    | 73 => .field .r2 .r2 false 74
    | 74 => .call (stateLabel 0) 75 .r3
    | 75 => .ret .r3
    | 96 => .field .r0 .r2 true 97
    | 97 => .field .r0 .r0 true 98
    | 98 => .field .r1 .r1 true 99
    | 99 => .field .r1 .r1 true 100
    | 100 => .make .r0 (.pair .r0 .r1) 101
    | 101 => .ret .r0
    | 112 => .field .r2 .r0 false 113
    | 113 => .move .r1 .r3 114
    | 114 => .call (refreshLabel 2) 115 .r3
    | 115 => .ret .r3
    | _ => .halt
  else if h : pc.val < 3717 then
    if pc.val=138 then .ret .r3
    else ReferenceProgramLabels.instruction seedLabel (InitialSeedProgram.program ⟨pc.val-128,by omega⟩)
  else if h : pc.val < 4057 then
    if pc.val=3723 then .ret .r3
    else ReferenceProgramLabels.instruction stateLabel (InitialRetainedStateProgram.program ⟨pc.val-3717,by omega⟩)
  else if pc.val=4061 then .ret .r3
  else ReferenceProgramLabels.instruction refreshLabel (AdaptiveRoundRefreshProgram.program ⟨pc.val-4057,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 10935

def Control (heap : NaturalHeap) (root : ℕ) (R M : Bits) (trials restarts epochs : ℕ) : Prop :=
  ∃ gates bounds count fuel trial restart,heap[root]?=some (.pair gates bounds) ∧ heap[bounds]?=some (.pair count fuel) ∧
    heap[fuel]?=some (.pair trial restart) ∧ AdaptiveGatesProgram.Parameters heap gates R M ∧
    IndexSpine heap count epochs ∧ IndexSpine heap trial trials ∧ IndexSpine heap restart restarts

theorem control_extend {heap : NaturalHeap} {root : ℕ} {R M : Bits} {trials restarts epochs : ℕ}
    (h : Control heap root R M trials restarts epochs) (ext : NaturalHeap) :
    Control (heap++ext) root R M trials restarts epochs := by
  obtain ⟨g,b,c,f,t,r,read,bc,fr,p,e,tr,rr⟩ := h
  exact ⟨g,b,c,f,t,r,lookup_extend read ext,lookup_extend bc ext,lookup_extend fr ext,
    AdaptiveGatesProgram.parameters_extend p ext,indexSpine_extend e ext,indexSpine_extend tr ext,indexSpine_extend rr ext⟩

def instructionBound (n L W : ℕ) : ℕ :=
  InitialSeedProgram.instructionBound n W+InitialRetainedStateProgram.instructionBound n+
    CandidateRefreshProgram.instructionBound n L n.size L.size 1+56

noncomputable abbrev initialCode {n L : ℕ} (adj : PairFlags n) (positive : 0<L) :=
  RetainedDemandMask.initial (Graph adj) (enumeration n) L positive

private theorem seed_slots (pc : Fin 3589) (h : InitialSeedProgram.program pc≠.halt) :
    program (seedLabel pc)=ReferenceProgramLabels.instruction seedLabel (InitialSeedProgram.program pc) := by
  by_cases stop : pc.val=10
  · have eq : pc=10 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,seedLabel,show ¬128+pc.val<128 by omega,show 128+pc.val<3717 by omega,show 128+pc.val≠138 by omega]

private theorem state_slots (pc : Fin 340) (h : InitialRetainedStateProgram.program pc≠.halt) :
    program (stateLabel pc)=ReferenceProgramLabels.instruction stateLabel (InitialRetainedStateProgram.program pc) := by
  by_cases stop : pc.val=6
  · have eq : pc=6 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,stateLabel,show ¬3717+pc.val<128 by omega,show ¬3717+pc.val<3717 by omega,show 3717+pc.val<4057 by omega,show 3717+pc.val≠3723 by omega]

private theorem refresh_slots (pc : Fin 6878) (h : AdaptiveRoundRefreshProgram.program pc≠.halt) :
    program (refreshLabel pc)=ReferenceProgramLabels.instruction refreshLabel (AdaptiveRoundRefreshProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,refreshLabel,show ¬4057+pc.val<128 by omega,show ¬4057+pc.val<3717 by omega,show ¬4057+pc.val<4057 by omega,show 4057+pc.val≠4061 by omega]

set_option maxHeartbeats 2000000 in
private theorem seed_call {n L W trials restarts epochs : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {R M : Bits} (input : Input (L:=L) heap r.a adj) (controls : Control heap r.b R M trials restarts epochs)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : L.bits.length≤W) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),InitialSeedProgram.Output (L:=L) (heap++ext) root adj R M ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r2 root) [] tape 1) ∧
      k≤ InitialSeedProgram.instructionBound n W+5 := by
  obtain ⟨g,b,e,f,t,z,atControl,atBounds,atFuel,gate,ep,tp,rp⟩ := controls
  let frame : Frame ℕ 10935 := ⟨1,.r2,r⟩
  let args := r.set .r1 g
  have load : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape 17) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atControl,args,frame]
  obtain ⟨ext,root,a,b,w,k,rep,body,time⟩ :=
    InitialSeedProgram.natural_seed (r:=args) input gate hW vertexWidth gridWidth tape
  have invoke := ReferenceProgramInvocation.call seedLabel seed_slots (caller:=17) (continuation:=18)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 18
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,k+5,rep,?_,by omega⟩
  have count : 2+(k+2+1)=k+5 := by omega
  rw [← count]
  simpa only [stop,Registers.get,Registers.set,List.nil_append] using append_run load (append_run invoke (.step ret (.done _)))

set_option maxHeartbeats 2600000 in
private theorem state_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M : Bits}
    (positive : 0<L) (input : Input (L:=L) heap r.a adj) (seed : InitialSeedProgram.Output (L:=L) heap r.c adj R M)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      AdaptiveControllerStorage.StateAt (heap++ext) root (initialCode adj positive).data (words n) unitWord ∧
      NaturalRun program k (state heap r [] tape 1) [] (state (heap++ext) (r.set .r3 root) [] tape 2) ∧
      k≤ InitialRetainedStateProgram.instructionBound n+14 := by
  obtain ⟨matrix,dims,count,fields,grid,one,atInput,atDims,atFields,graph,nRep,lRep,oneRep⟩ := input
  obtain ⟨masks,controls,mask,params,table,cut,atSeed,atM,atC,maskRep,paramRep,rows,cutRep⟩ := seed
  let frame : Frame ℕ 10935 := ⟨2,.r3,r⟩
  let before := r.set .r0 one
  have getScale : NaturalRun program 4 (state heap r [] tape 1) [] (state heap before [frame] tape 67) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      before,frame,atInput,atDims,atFields]
  let freeCell : Cell ℕ := .flag false
  let scalars : Cell ℕ := .pair one heap.length
  let extra : NaturalHeap := [freeCell,scalars]
  let mid := heap++extra
  let constants := before.set .r3 (heap.length+1)
  have put : NaturalRun program 2 (state heap before [frame] tape 67) [] (state mid constants [frame] tape 69) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      before,extra,mid,constants,freeCell,scalars,allocateNatural,Recipe.cell]
  let args : Registers ℕ := ⟨mask,table,cut,heap.length+1⟩
  have a : mid[r.c]?=some (.pair masks controls) := lookup_extend atSeed extra
  have b : mid[masks]?=some (.pair mask table) := lookup_extend atM extra
  have c : mid[controls]?=some (.pair cut params) := lookup_extend atC extra
  have select : NaturalRun program 5 (state mid constants [frame] tape 69) [] (state mid args [frame] tape 74) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      constants,before,args,a,b,c]
  have anchors : InitialRetainedStateProgram.Constants mid args.d :=
    ⟨one,heap.length,by simp [mid,args,extra,scalars],boolList_extend oneRep extra,by simp [mid,extra,freeCell]⟩
  have active : RetainedDemandEraseProgram.RowsAt mid args.a
      (RetainedDemandMask.compute (Graph adj) (enumeration n) L) := by
    obtain ⟨refs,spine,reps⟩ := maskRep
    exact ⟨refs,BinaryPointerListRead.pointerList_extend spine extra,reps.imp (fun _ _ rep => boolList_extend rep extra)⟩
  obtain ⟨ext,root,packed,runtime,free,k,rep,body,time⟩ := InitialRetainedStateProgram.natural_state (r:=args) (adj:=adj)
    (enumeration n) positive active (RoundInputPackProgram.weights_extend rows extra) (boolList_extend cutRep extra)
    anchors tape
  have invoke := ReferenceProgramInvocation.call stateLabel state_slots (caller:=74) (continuation:=75)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++ext) (args.set .r3 root) [frame] tape 75
  have ret : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) [] tape 2,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨extra++ext,root,k+14,?_,?_,by omega⟩
  · simpa only [mid,List.append_assoc] using rep
  · have countEq : 4+(2+(5+(k+2+1)))=k+14 := by omega
    rw [← countEq]
    simpa only [mid,stop,Registers.get,Registers.set,List.append_assoc,List.nil_append] using
      append_run getScale (append_run put (append_run select (append_run invoke (.step ret (.done _)))))

set_option maxHeartbeats 2100000 in
private theorem settings_call {n L trials restarts epochs : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {R M : Bits} (seed : InitialSeedProgram.Output (L:=L) heap r.c adj R M) (control : Control heap r.b R M trials restarts epochs)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),Settings (L:=L) (heap++ext) root adj R M trials restarts ∧
      NaturalRun program 7 (state heap r [] tape 2) [] (state (heap++ext) (r.set .r0 root) [] tape 3) := by
  obtain ⟨m,c,mask,params,table,cut,atSeed,atM,atC,mp,pp,tp,cp⟩ := seed
  obtain ⟨g,b,ep,fuel,trial,restart,atCtl,atBounds,atFuel,gp,es,ts,rs⟩ := control
  let frame : Frame ℕ 10935 := ⟨3,.r0,r⟩
  let args : Registers ℕ := ⟨params,fuel,r.c,r.d⟩
  have load : NaturalRun program 5 (state heap r [] tape 2) [] (state heap args [frame] tape 100) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atSeed,atC,atCtl,atBounds]
  let record : Cell ℕ := .pair params fuel
  let ext : NaturalHeap := [record]
  have save : NaturalRun program 2 (state heap args [frame] tape 100) []
      (state (heap++ext) (r.set .r0 heap.length) [] tape 3) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,ext,record,allocateNatural,Recipe.cell]
  exact ⟨ext,heap.length,⟨params,fuel,trial,restart,by simp [ext,record],lookup_extend atFuel ext,
    AdaptiveControllerStorage.parameters_extend pp ext,indexSpine_extend ts ext,indexSpine_extend rs ext⟩,append_run load save⟩

set_option maxHeartbeats 2300000 in
private theorem start_cache {n L trials restarts : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {R M : Bits} (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (settings : Settings (L:=L) heap r.a adj R M trials restarts)
    (live : AdaptiveControllerStorage.StateAt heap r.d (initialCode adj positive).data (words n) unitWord)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Stored (heap++ext) root (initialCode adj positive) positive EN E (words n) unitWord ∧
      NaturalRun program k (state heap r [] tape 3) [] (state (heap++ext) (r.set .r3 root) [] tape 4) ∧
      k≤ CandidateRefreshProgram.instructionBound n L n.size L.size 1+24 := by
  obtain ⟨fixed,fuel,sample,stab,atSettings,atFuel,params,spine,cap⟩ := settings
  let frame : Frame ℕ 10935 := ⟨4,.r3,r⟩
  let args : Registers ℕ := ⟨r.a,r.d,fixed,r.d⟩
  have load : NaturalRun program 3 (state heap r [] tape 3) [] (state heap args [frame] tape 114) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atSettings]
  obtain ⟨ext,root,k,cache,body,time⟩ := AdaptiveRoundRefreshProgram.natural_cache_from_state (r:=args)
    (initialCode adj positive) positive EN E live params tape
  have run := ReferenceProgramInvocation.call refreshLabel refresh_slots (caller:=114) (continuation:=115)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 115
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 4,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,k+6,cache,?_,?_⟩
  · have countEq : 3+(k+2+1)=k+6 := by omega
    rw [← countEq]
    simpa only [stop,Registers.get,Registers.set,List.nil_append] using append_run load (append_run run (.step ret (.done _)))
  · change k≤ CandidateRefreshProgram.instructionBound n L n.size L.size 1+18 at time
    omega

set_option maxHeartbeats 3300000 in
theorem natural_initialize {n L W trials restarts epochs : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {R M : Bits} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (input : Input (L:=L) heap r.a adj) (controls : Control heap r.b R M trials restarts epochs)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : L.bits.length≤W) (tape : Bits) :
    ∃ (ext : NaturalHeap) (epochRoot settings root k : ℕ),
      Settings (L:=L) (heap++ext) settings adj R M trials restarts ∧ IndexSpine (heap++ext) epochRoot epochs ∧
      Stored (heap++ext) root (initialCode adj positive) positive EN E (words n) unitWord ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) ⟨epochRoot,r.b,settings,root⟩ [] tape 7) ∧
      k≤ instructionBound n L W := by
  obtain ⟨es,seed,x,rep,makeSeed,seedTime⟩ := seed_call input controls hW vertexWidth gridWidth tape
  let mid := heap++es
  let a := r.set .r2 seed
  obtain ⟨et,live,y,stateRep,makeState,stateTime⟩ := state_call (r:=a) positive (input_extend input es) rep tape
  let grown := mid++et
  let b := a.set .r3 live
  have seedAt : InitialSeedProgram.Output (L:=L) grown b.c adj R M := InitialSeedProgram.output_extend rep et
  have controlAt := control_extend (control_extend controls es) et
  obtain ⟨ep,settings,params,makeSettings⟩ := settings_call (r:=b) seedAt controlAt tape
  let ready := grown++ep
  let c := b.set .r0 settings
  obtain ⟨ec,root,z,cacheRep,makeCache,cacheTime⟩ := start_cache (r:=c) positive EN E params
    (AdaptiveControllerStorage.state_extend stateRep ep) tape
  let final := ready++ec
  let d := c.set .r3 root
  have extended := control_extend (control_extend controlAt ep) ec
  obtain ⟨g,bounds,epochRoot,fuel,trial,restart,atControl,atBounds,atFuel,gate,index,spine,cap⟩ := extended
  have hold : final[r.b]?=some (.pair g bounds) := atControl
  have load : final[bounds]?=some (.pair epochRoot fuel) := atBounds
  have finish : NaturalRun program 3 (state final d [] tape 4) []
      (state final ⟨epochRoot,r.b,settings,root⟩ [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      hold,load,d,c,b,a]
  let ext := es++et++ep++ec
  let k := x+(y+(7+(z+3)))
  refine ⟨ext,epochRoot,settings,root,k,?_,?_,?_,?_,?_⟩
  · simpa only [ext,final,ready,grown,mid,List.append_assoc] using settings_extend params ec
  · simpa only [ext,final,ready,grown,mid,List.append_assoc] using index
  · simpa only [ext,final,ready,grown,mid,List.append_assoc] using cacheRep
  · simpa only [ext,k,final,ready,grown,mid,List.append_assoc,List.nil_append] using
      append_run makeSeed (append_run makeState (append_run makeSettings (append_run makeCache finish)))
  · dsimp only [k,instructionBound]
    omega

end DirectedFlowCutGap.PhysicalControllerInitializer
