import DirectedFlowCutGap.CacheStabilizeProgram
import DirectedFlowCutGap.ControllerEpochParameters

/-! Stabilize, draw and scan each active epoch from one represented controller input. -/

namespace DirectedFlowCutGap.AdaptiveControllerProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochScanData (Graph Stored stored_extend cacheOf)
open CandidateEnumeration (Node Network)

def stabilizeLabel (pc : Fin 7320) : Fin 15323 := ⟨96+pc.val,by omega⟩
def parametersLabel (pc : Fin 118) : Fin 15323 := ⟨7416+pc.val,by omega⟩
def epochLabel (pc : Fin 7789) : Fin 15323 := ⟨7534+pc.val,by omega⟩

def program : Program 15323 := fun pc =>
  if pc.val < 96 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .call 16 9 .r3
    | 9 => .branch .r0 15 60 60 10
    | 10 => .call 24 11 .r1
    | 11 => .branch .r1 15 60 60 12
    | 12 => .move .r3 .r1 13
    | 13 => .field .r0 .r0 true 8
    | 15 => .ret .r3
    | 16 => .field .r0 .r2 true 17
    | 17 => .field .r2 .r2 false 18
    | 18 => .field .r0 .r0 true 19
    | 19 => .call (stabilizeLabel 0) 20 .r3
    | 20 => .ret .r3
    | 24 => .field .r0 .r2 true 25
    | 25 => .field .r0 .r0 false 26
    | 26 => .field .r2 .r2 false 27
    | 27 => .call (parametersLabel 0) 28 .r1
    | 28 => .field .r2 .r1 false 29
    | 29 => .field .r1 .r1 true 30
    | 30 => .branch .r1 60 31 34 60
    | 31 => .call (epochLabel 0) 32 .r3
    | 32 => .ret .r3
    | 34 => .make .r3 .nil 35
    | 35 => .ret .r3
    | _ => .halt
  else if h : pc.val < 7416 then
    if pc.val=97 then .ret .r3
    else ReferenceProgramLabels.instruction stabilizeLabel (CacheStabilizeProgram.program ⟨pc.val-96,by omega⟩)
  else if h : pc.val < 7534 then
    if pc.val=7420 then .ret .r3
    else ReferenceProgramLabels.instruction parametersLabel (ControllerEpochParameters.program ⟨pc.val-7416,by omega⟩)
  else if pc.val=7538 then .ret .r3
  else ReferenceProgramLabels.instruction epochLabel (PhysicalEpochScanProgram.program ⟨pc.val-7534,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 15323

def Settings {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n) (R M : Bits) (trials restarts : ℕ) : Prop :=
  ∃ fixed fuel sample stabilize,heap[root]?=some (.pair fixed fuel) ∧ heap[fuel]?=some (.pair sample stabilize) ∧
    Parameters (L:=L) heap fixed adj R M ∧ IndexSpine heap sample trials ∧ IndexSpine heap stabilize restarts

theorem settings_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {R M : Bits} {trials restarts : ℕ}
    (h : Settings (L:=L) heap root adj R M trials restarts) (ext : NaturalHeap) :
    Settings (L:=L) (heap++ext) root adj R M trials restarts := by
  obtain ⟨fixed,fuel,sample,stabilize,loc,read,params,count,cap⟩ := h
  exact ⟨fixed,fuel,sample,stabilize,lookup_extend loc ext,lookup_extend read ext,parameters_extend params ext,
    indexSpine_extend count ext,indexSpine_extend cap ext⟩

private theorem stabilize_slots (pc : Fin 7320) (h : CacheStabilizeProgram.program pc≠.halt) :
    program (stabilizeLabel pc)=ReferenceProgramLabels.instruction stabilizeLabel (CacheStabilizeProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,stabilizeLabel,show ¬96+pc.val<96 by omega,show 96+pc.val<7416 by omega,show 96+pc.val≠97 by omega]

private theorem parameters_slots (pc : Fin 118) (h : ControllerEpochParameters.program pc≠.halt) :
    program (parametersLabel pc)=ReferenceProgramLabels.instruction parametersLabel (ControllerEpochParameters.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,parametersLabel,show ¬7416+pc.val<96 by omega,show ¬7416+pc.val<7416 by omega,
      show 7416+pc.val<7534 by omega,show 7416+pc.val≠7420 by omega]

private theorem epoch_slots (pc : Fin 7789) (h : PhysicalEpochScanProgram.program pc≠.halt) :
    program (epochLabel pc)=ReferenceProgramLabels.instruction epochLabel (PhysicalEpochScanProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,epochLabel,show ¬7534+pc.val<96 by omega,show ¬7534+pc.val<7416 by omega,
      show ¬7534+pc.val<7534 by omega,show 7534+pc.val≠7538 by omega]

set_option maxHeartbeats 1700000 in
theorem stabilize_call {n L B S trials restarts : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (settings : Settings (L:=L) heap r.c adj R M trials restarts)
    (cache : Stored heap r.d s positive EN E words scale)
    (grid : max L.size (L+1).size≤B) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B) (scaleBound : scale.length+2*restarts≤S)
    (stack : List (Frame ℕ 15323)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
      Stored (heap++ext) root (CacheStabilizeProgram.stableCode positive E R restarts s) positive EN E nextWords nextScale ∧
      (∀ ws∈nextWords,∀ w∈ws,w.length≤B) ∧ nextScale.length≤ scale.length+2*restarts ∧
      NaturalRun program k (state heap r stack tape 8) [] (state (heap++ext) (r.set .r3 root) stack tape 9) ∧
      k ≤ CacheStabilizeProgram.instructionBound n L restarts heap.length B S R.length M.length+7 ∧
      ext.length ≤ CacheStabilizeProgram.allocationBound n L restarts B S R.length M.length := by
  obtain ⟨fixed,fuel,sample,restart,atSettings,atFuel,parameters,trialsRep,restartsRep⟩ := settings
  let frame : Frame ℕ 15323 := ⟨9,.r3,r⟩
  let args : Registers ℕ := ⟨restart,r.b,fixed,r.d⟩
  have load : NaturalRun program 4 (state heap r stack tape 8) []
      (state heap args (frame::stack) tape 19) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atSettings,atFuel]
  obtain ⟨ext,root,k,nextWords,nextScale,rep,width,scaleGrowth,body,time,allocation⟩ :=
    CacheStabilizeProgram.natural_stabilize s positive EN E (r:=args) parameters cache restartsRep grid widths scaleBound tape
  have invoke := ReferenceProgramInvocation.call stabilizeLabel stabilize_slots (caller:=19) (continuation:=20)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) (frame::stack) body
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape 20
  have stabilize : NaturalRun program (k+2) (state heap args (frame::stack) tape 19) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 9,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,k+7,nextWords,nextScale,rep,width,scaleGrowth,?_,by omega,allocation⟩
  have count : 4+(k+2+1)=k+7 := by omega
  rw [← count]
  exact append_run load (append_run stabilize (.step ret (.done _)))

structure EpochReady {n L : ℕ} (heap : NaturalHeap) (args : Registers ℕ) (adj : PairFlags n) (d : Data n) (optimum trials : ℕ)
    (R threshold : Bits) : Prop where
  parameters : Parameters (L:=L) heap args.c adj R threshold
  trialCap : IndexSpine heap args.a trials
  stop : heap[args.b]?=some (.flag (optimum==0))
  value_eq : value threshold=d.current
  width_eq : threshold.length=d.current.size

set_option maxHeartbeats 2500000 in
theorem prepare_call {n L trials restarts : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {d : Data n} {optimum : ℕ} {candidate : Family n} {words candidateWords : List (List Bits)} {R M scale : Bits}
    (settings : Settings (L:=L) heap r.c adj R M trials restarts)
    (cache : AdaptiveControllerStorage.CacheAt heap r.d d optimum candidate words candidateWords scale)
    (stack : List (Frame ℕ 15323)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (trialRoot zeroFlag params k : ℕ) (threshold : Bits),
      EpochReady (L:=L) (heap++ext) ⟨trialRoot,zeroFlag,params,r.d⟩ adj d optimum trials R threshold ∧
      NaturalRun program k (state heap r stack tape 10) []
        (state (heap++ext) ⟨trialRoot,zeroFlag,params,r.d⟩ (⟨11,.r1,r⟩::stack) tape 30) ∧
      k ≤ ControllerEpochParameters.instructionBound heap.length+8 ∧ ext.length=d.current.size+4 := by
  obtain ⟨fixed,fuel,sample,restart,atSettings,atFuel,parameters,trialsRep,restartsRep⟩ := settings
  let frame : Frame ℕ 15323 := ⟨11,.r1,r⟩
  let args : Registers ℕ := ⟨sample,r.b,fixed,r.d⟩
  have load : NaturalRun program 4 (state heap r stack tape 10) []
      (state heap args (frame::stack) tape 27) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atSettings,atFuel]
  obtain ⟨ext,root,params,flag,thresholdRoot,k,threshold,atResult,rep,test,val,width,body,time,allocation⟩ :=
    ControllerEpochParameters.natural_prepare (r:=args) parameters cache tape
  let mid := heap++ext
  let packed := args.set .r1 root
  let final : Registers ℕ := ⟨sample,flag,params,r.d⟩
  have invoke := ReferenceProgramInvocation.call parametersLabel parameters_slots (caller:=27) (continuation:=28)
    (result:=.r3) (dst:=.r1) (by rfl) (by rfl) (frame::stack) body
  have prepared : NaturalRun program (k+2) (state heap args (frame::stack) tape 27) []
      (state mid packed (frame::stack) tape 28) := by
    simpa only [mid,packed,Registers.get] using invoke
  have both : mid[root]?=some (.pair params flag) := atResult
  have extract : NaturalRun program 2 (state mid packed (frame::stack) tape 28) []
      (state mid final (frame::stack) tape 30) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,packed,final,both]
  refine ⟨ext,sample,flag,params,k+8,threshold,⟨rep,indexSpine_extend trialsRep ext,test,val,width⟩,
    ?_,by omega,allocation⟩
  have count : 4+(k+2+2)=k+8 := by omega
  rw [← count]
  exact append_run load (append_run prepared extract)

theorem stop_epoch {n L trials : ℕ} {heap : NaturalHeap} {r caller : Registers ℕ} {adj : PairFlags n}
    {d : Data n} {R threshold : Bits} (ready : EpochReady (L:=L) heap r adj d 0 trials R threshold)
    (stack : List (Frame ℕ 15323)) (tape : Bits) :
    (heap++[.nil])[heap.length]?=some .nil ∧
      NaturalRun program 3 (state heap r (⟨11,.r1,caller⟩::stack) tape 30) []
        (state (heap++[.nil]) (caller.set .r1 heap.length) stack tape 11) := by
  have tag : heap[r.b]?=some (.flag true) := ready.stop
  refine ⟨by simp,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
    tag,tagBranch,allocateNatural,Recipe.cell]

set_option maxHeartbeats 1700000 in
theorem sample_epoch {n L W B trials : ℕ} {heap : NaturalHeap} {r caller : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R threshold scale : Bits} {words : List (List Bits)}
    (ready : EpochReady (L:=L) heap r adj s.data (cacheOf positive E s).optimal trials R threshold)
    (cache : Stored heap r.d s positive EN E words scale) (active : (cacheOf positive E s).optimal≠0)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : RetainedEpochFromMasks.width n L≤W)
    (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (stack : List (Frame ℕ 15323)) (tape rest : Bits) (reads : ℕ) (t : RetainedTapeInput.Tape L s.data.remaining)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower trials
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) tape=some (t,(rest,reads))) :
    let input := RetainedTapeInput.materialize positive s.data.remaining t
    let observed := PhysicalDrawSequenceProgram.batch trials (RetainedEpochFromMasks.bounds s.data.remaining positive) tape
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Stored (heap++ext) root (EpochScanData.scan positive E R threshold input.cell input.order s) positive EN E words scale ∧
      NaturalRun program k (state heap r (⟨11,.r1,caller⟩::stack) tape 30) (observed.requests.map Event.request)
        (state (heap++ext) (caller.set .r1 root) stack rest 11) ∧
      k≤ PhysicalEpochScanProgram.instructionBound n L trials heap.length W B scale.length R.length threshold.length+4 ∧
      ext.length≤ PhysicalEpochScanProgram.allocationBound n L trials W B scale.length R.length threshold.length ∧
      observed.requests.length=reads := by
  let frame : Frame ℕ 15323 := ⟨11,.r1,caller⟩
  let saved := frame::stack
  have zeroTest : ((cacheOf positive E s).optimal==0)=false := beq_eq_false_iff_ne.mpr active
  have flag : heap[r.b]?=some (.flag false) := by simpa only [zeroTest] using ready.stop
  have choose : tickNatural program (state heap r saved tape 30)=some ⟨state heap r saved tape 31,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,flag,tagBranch]
  obtain ⟨ext,root,orderRoot,cellRoot,k,rep,body,time,alloc,count⟩ :=
    PhysicalEpochScanProgram.natural_epoch_scan s positive EN E ready.trialCap ready.parameters cache (le_refl heap.length)
      hW vertexWidth gridWidth rowWidths weightWidths tape rest reads t sample
  have invoke := ReferenceProgramInvocation.call epochLabel epoch_slots (caller:=31) (continuation:=32)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) saved body
  let stop := state (heap++ext) (r.set .r3 root) saved rest 32
  have ret : tickNatural program stop=some ⟨state (heap++ext) (caller.set .r1 root) stack rest 11,[],0⟩ := by
    simp [stop,saved,frame,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,k+4,rep,?_,by omega,alloc,count⟩
  have launch := append_run invoke (NaturalRun.step ret (.done _))
  simpa only [Registers.get,List.nil_append,List.append_nil,Nat.add_assoc] using NaturalRun.step choose launch

theorem reject_epoch {n L trials : ℕ} {heap : NaturalHeap} {r caller : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R threshold scale : Bits} {words : List (List Bits)}
    (ready : EpochReady (L:=L) heap r adj s.data (cacheOf positive E s).optimal trials R threshold)
    (cache : Stored heap r.d s positive EN E words scale) (active : (cacheOf positive E s).optimal≠0)
    (stack : List (Frame ℕ 15323)) (tape : Bits)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower trials
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) tape=none) :
    ∃ (k : ℕ) (events : List Event) (out : NaturalState 15323),
      NaturalRun program k (state heap r (⟨11,.r1,caller⟩::stack) tape 30) events out ∧
      tape.length < GuardedReferenceExecution.requestCount events := by
  let callerFrame : Frame ℕ 15323 := ⟨11,.r1,caller⟩
  let drawFrame : Frame ℕ 15323 := ⟨32,.r3,r⟩
  let saved := callerFrame::stack
  have zeroTest : ((cacheOf positive E s).optimal==0)=false := beq_eq_false_iff_ne.mpr active
  have flag : heap[r.b]?=some (.flag false) := by simpa only [zeroTest] using ready.stop
  have choose : tickNatural program (state heap r saved tape 30)=some ⟨state heap r saved tape 31,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,flag,tagBranch]
  have enter : tickNatural program (state heap r saved tape 31)=
      some ⟨state heap r (drawFrame::saved) tape (epochLabel 0),[],0⟩ := rfl
  obtain ⟨ext,root,body,short⟩ := PhysicalEpochScanProgram.natural_epoch_rejected s positive EN E
    ready.trialCap ready.parameters cache tape sample
  have relabel := ReferenceProgramLabels.run epochLabel PhysicalEpochScanProgram.program program epoch_slots body
  have moved := ReferenceProgramStack.run program (drawFrame::saved) relabel
  exact ⟨_,_,_,.step choose (.step enter moved),short⟩

end DirectedFlowCutGap.AdaptiveControllerProgram
