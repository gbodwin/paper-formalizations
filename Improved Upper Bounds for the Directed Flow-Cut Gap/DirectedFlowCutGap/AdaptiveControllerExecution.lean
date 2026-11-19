import DirectedFlowCutGap.AdaptiveControllerBounds
import DirectedFlowCutGap.ControllerTapeModel

/-! Complete control flow from a represented cache, with exact literal tape semantics. -/

namespace DirectedFlowCutGap.AdaptiveControllerExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead (IndexSpine)
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerProgram (program state Settings settings_extend)
open AdaptiveControllerBounds
open EpochScanData (Graph Stored stored_extend cacheOf)
open CacheStabilizeProgram (stableCode)
open CandidateEnumeration (Node Network)
open GuardedReferenceExecution (requestCount count_append count_reads)

private theorem nil_counter {heap : NaturalHeap} {r : Registers ℕ} {tape : Bits}
    {frame : Frame ℕ 15323} {stack : List (Frame ℕ 15323)} (h : heap[r.a]?=some .nil) :
    NaturalRun program 2 (state heap r (frame::stack) tape 9) []
      (state heap (frame.saved.set frame.destination r.d) stack tape frame.continuation) := by
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,h]

private theorem nil_epoch {heap : NaturalHeap} {r : Registers ℕ} {tape : Bits}
    {frame : Frame ℕ 15323} {stack : List (Frame ℕ 15323)} (h : heap[r.b]?=some .nil) :
    NaturalRun program 2 (state heap r (frame::stack) tape 11) []
      (state heap (frame.saved.set frame.destination r.d) stack tape frame.continuation) := by
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,h]

private theorem next_epoch {heap : NaturalHeap} {r : Registers ℕ} {tape : Bits}
    {stack : List (Frame ℕ 15323)} {x y payload tail : ℕ}
    (result : heap[r.b]?=some (.pair x y)) (counter : heap[r.a]?=some (.pair payload tail)) :
    NaturalRun program 3 (state heap r stack tape 11) []
      (state heap ⟨tail,r.b,r.c,r.b⟩ stack tape 8) := by
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
    tagBranch,result,counter]

def Witness {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (heap : NaturalHeap) (entry : NaturalState 15323) (tape : Bits) (W S k A : ℕ)
    (frame : Frame ℕ 15323) (stack : List (Frame ℕ 15323)) :
    Option (Code (Graph adj) demands L × EncodedSolverBits.Tape) → Prop
  | none => ∃ (steps : ℕ) (events : List Event) (out : NaturalState 15323),
      NaturalRun program steps entry events out ∧ tape.length < requestCount events
  | some (s,(rest,reads)) =>
    ∃ (ext : NaturalHeap) (root steps : ℕ) (events : List Event) (words : List (List Bits)) (scale : Bits),
      Stored (heap++ext) root s positive EN E words scale ∧
      (∀ ws∈words,∀ w∈ws,w.length≤W) ∧ scale.length≤S ∧
      NaturalRun program steps entry events
        (state (heap++ext) (frame.saved.set frame.destination root) stack rest frame.continuation) ∧
      steps≤k ∧ ext.length≤A ∧ requestCount events=reads ∧ reads≤tape.length

set_option maxHeartbeats 4200000 in
theorem natural_loop {n L W B S trials restarts epochs : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (settings : Settings (L:=L) heap r.c adj R M trials restarts)
    (cache : Stored heap r.d s positive EN E words scale) (epochsAt : IndexSpine heap r.a epochs)
    (hW : 1≤W) (labelWidth : n.size≤W) (gridWidth : RetainedEpochFromMasks.width n L≤W) (hB : B≤W)
    (grid : max L.size (L+1).size≤B) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (scaleBound : scale.length+2*restarts*(epochs+1)≤S)
    (frame : Frame ℕ 15323) (stack : List (Frame ℕ 15323)) (tape : Bits) :
    let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
    Witness positive EN E heap (state heap r (frame::stack) tape 8) tape B S
      (loopLimit b (epochs+1) heap.length) ((epochs+1)*b.stepCells) frame stack
      (ControllerTapeModel.run positive E R trials restarts epochs s tape) := by
  let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
  induction epochs generalizing heap r s words scale tape with
  | zero =>
    cases epochsAt with
    | nil atEpochs =>
      have fit : scale.length+2*restarts≤S := by simpa only [Nat.zero_add,Nat.mul_one] using scaleBound
      obtain ⟨ext,root,k,ws,bs,stored,wordBound,scaleGrowth,body,time,space⟩ :=
        AdaptiveControllerProgram.stabilize_call s positive EN E settings cache grid widths fit (frame::stack) tape
      let mid := heap++ext
      have last : mid[(r.set .r3 root).a]?=some .nil := lookup_extend atEpochs ext
      have tail := nil_counter (frame:=frame) (stack:=stack) (tape:=tape) last
      have endTime : k+2≤ b.stepInstructions heap.length := by
        change k≤ b.stabilizeInstructions heap.length+7 at time
        unfold Limits.stepInstructions
        omega
      have endSpace : ext.length≤ (0+1)*b.stepCells := by
        change ext.length≤ b.stabilizeCells at space
        unfold Limits.stepCells
        omega
      change Witness positive EN E heap _ tape B S _ _ frame stack
        (some (stableCode positive E R restarts s,(tape,0)))
      exact ⟨ext,root,k+2,[],ws,bs,stored,wordBound,by omega,append_run body tail,
        loop_stop b 0 heap.length (k+2) endTime,endSpace,rfl,Nat.zero_le _⟩
  | succ epochs ih =>
    cases epochsAt with
    | cons atEpochs later =>
      rename_i payload tailRoot
      let saved := frame::stack
      let c := stableCode positive E R restarts s
      have fit : scale.length+2*restarts≤S := by
        have h := Nat.le_mul_of_pos_right (2*restarts) (show 0<epochs+1+1 by omega)
        exact (Nat.add_le_add_left h scale.length).trans scaleBound
      obtain ⟨ec,rootC,k,ws,bs,stable,wordBound,scaleGrowth,stabilize,stabilizeTime,stabilizeSpace⟩ :=
        AdaptiveControllerProgram.stabilize_call s positive EN E settings cache grid widths fit saved tape
      let mid := heap++ec
      let current := r.set .r3 rootC
      have currentCache : Stored mid current.d c positive EN E ws bs := stable
      have testEpochs : mid[current.a]?=some (.pair payload tailRoot) := lookup_extend atEpochs ec
      have select : tickNatural program (state mid current saved tape 9)=some ⟨state mid current saved tape 10,[],0⟩ := by
        simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,testEpochs,tagBranch]
      obtain ⟨ep,trialRoot,zeroFlag,params,kp,threshold,ready,prep,prepTime,prepSpace⟩ :=
        AdaptiveControllerProgram.prepare_call (r:=current) (settings_extend settings ec) currentCache saved tape
      let grown := mid++ep
      let drawnArgs : Registers ℕ := ⟨trialRoot,zeroFlag,params,rootC⟩
      let frontCount := k+(kp+1)
      have start : NaturalRun program frontCount (state heap r saved tape 8) []
          (state grown drawnArgs (⟨11,.r1,current⟩::saved) tape 30) :=
        append_run stabilize (.step select prep)
      have grownCache : Stored grown drawnArgs.d c positive EN E ws bs := stored_extend currentCache ep
      have curWidth : c.data.current.size≤ b.threshold := (EpochScanBounds.mass_widths currentCache wordBound).1
      have midSize : mid.length≤heap.length+b.stabilizeCells := by
        change ec.length≤ b.stabilizeCells at stabilizeSpace
        simpa only [mid,List.length_append] using Nat.add_le_add_left stabilizeSpace heap.length
      have padSize : ep.length≤ b.threshold+4 := by omega
      have grownSize : grown.length≤heap.length+b.stabilizeCells+b.threshold+4 := by
        simp only [grown,List.length_append]
        omega
      have st : k≤ b.stabilizeInstructions heap.length+7 := stabilizeTime
      have pt : kp≤ControllerEpochParameters.instructionBound (heap.length+b.stabilizeCells)+8 :=
        prepTime.trans (Nat.add_le_add_right (prep_instructions_mono midSize) 8)
      have nextScale : bs.length+2*restarts*(epochs+1)≤S := by
        change scale.length+2*restarts*((epochs+1)+1)≤S at scaleBound
        rw [Nat.mul_succ] at scaleBound
        omega
      have sBound : bs.length≤S := by omega
      rw [ControllerTapeModel.run_step]
      by_cases zero : (cacheOf positive E c).optimal=0
      · have readyZero : AdaptiveControllerProgram.EpochReady (L:=L) grown drawnArgs adj c.data 0 trials R threshold := zero ▸ ready
        obtain ⟨nilAt,exit⟩ := AdaptiveControllerProgram.stop_epoch (caller:=current) readyZero saved tape
        let last := grown++[Cell.nil]
        let out := current.set .r1 grown.length
        have terminal := nil_epoch (r:=out) (frame:=frame) (stack:=stack) (tape:=tape) nilAt
        have finalCache : Stored last rootC c positive EN E ws bs := stored_extend grownCache [Cell.nil]
        have finish : NaturalRun program (frontCount+(3+2)) (state heap r saved tape 8) []
            (state last (frame.saved.set frame.destination rootC) stack tape frame.continuation) :=
          append_run start (append_run exit terminal)
        have time : frontCount+5≤ b.stepInstructions heap.length := by
          dsimp only [frontCount,Limits.stepInstructions]
          omega
        have space : (ec++ep++[Cell.nil]).length≤(epochs+1+1)*b.stepCells := by
          have one : (ec++ep++[Cell.nil]).length≤ b.stepCells := by
            change ec.length≤ b.stabilizeCells at stabilizeSpace
            simp only [List.length_append,List.length_cons,List.length_nil,Limits.stepCells]
            omega
          exact one.trans (Nat.le_mul_of_pos_left _ (by omega))
        have test : ((cacheOf positive E (stableCode positive E R restarts s)).optimal==0)=true :=
          beq_iff_eq.mpr zero
        simp only [test,ite_true]
        exact ⟨ec++ep++[Cell.nil],rootC,frontCount+5,[],ws,bs,
          by simpa only [last,grown,mid,List.append_assoc] using finalCache,wordBound,sBound,
          by simpa only [last,grown,mid,List.append_assoc] using finish,
          loop_stop b (epochs+1) heap.length _ time,space,rfl,Nat.zero_le _⟩
      · have test : ((cacheOf positive E (stableCode positive E R restarts s)).optimal==0)=false :=
          beq_eq_false_iff_ne.mpr zero
        simp only [test,Bool.false_eq_true,ite_false]
        let sample := EncodedSolverBits.run (LazyFairBitTrees.lower trials (RetainedDrawTrees.sampleTape positive c.data.remaining)) tape
        cases sampled : sample with
        | none =>
          have eq : EncodedSolverBits.run (LazyFairBitTrees.lower trials (RetainedDrawTrees.sampleTape positive c.data.remaining)) tape=none := sampled
          rw [eq]
          obtain ⟨ks,events,out,reject,short⟩ := AdaptiveControllerProgram.reject_epoch c positive EN E (caller:=current)
            ready grownCache zero saved tape sampled
          exact ⟨frontCount+ks,events,out,append_run start reject,short⟩
        | some result =>
          rcases result with ⟨t,rest,reads⟩
          have eq : EncodedSolverBits.run (LazyFairBitTrees.lower trials (RetainedDrawTrees.sampleTape positive c.data.remaining)) tape=
              some (t,(rest,reads)) := sampled
          rw [eq]
          simp only [Option.bind_some]
          let input := RetainedTapeInput.materialize positive c.data.remaining t
          let next := EpochScanData.scan positive E R c.data.current.bits input.cell input.order c
          have modelRows : RetainedMassTableProgram.DataRows c.data.weights ws := by
            obtain ⟨live,best,pair,⟨packed,runtime,ctx,scale,weights,free,loc,update,rt,rc,table,rf,rs,rv,d⟩,candidate⟩ :=
              currentCache
            exact d
          have rowWidths : ∀ p (v : Fin n),(row c.data.weights p)[v.val].bits.length≤W :=
            fun p v => (ControllerTapeModel.row_widths c.data ws modelRows wordBound p v).trans hB
          obtain ⟨ee,root,kd,scanned,run,drawTime,drawSpace,drawCount⟩ :=
            AdaptiveControllerProgram.sample_epoch c positive EN E (caller:=current) ready grownCache zero hW labelWidth gridWidth
              rowWidths wordBound saved tape rest reads t sampled
          have same : EpochScanData.scan positive E R threshold input.cell input.order c=next :=
            ControllerTapeModel.scan_threshold positive E R threshold c.data.current.bits
              (ready.value_eq.trans (value_bits _).symm) input.cell input.order c
          rw [same] at scanned
          let finished := grown++ee
          let draft := current.set .r1 root
          let args : Registers ℕ := ⟨tailRoot,root,r.c,root⟩
          have nextCache : Stored finished args.d next positive EN E ws bs := scanned
          obtain ⟨storedState,storedOpt,rootAt,_,_⟩ := scanned
          have steps := next_epoch (r:=draft) (stack:=saved) (tape:=rest) rootAt
            (lookup_extend (lookup_extend testEpochs ep) ee)
          let allExt := ec++ep++ee
          have nextSettings : Settings (L:=L) finished args.c adj R M trials restarts :=
            settings_extend (settings_extend (settings_extend settings ec) ep) ee
          have nextEpochs : IndexSpine finished args.a epochs := indexSpine_extend (indexSpine_extend (indexSpine_extend later ec) ep) ee
          have recurse := ih next nextSettings nextCache nextEpochs wordBound nextScale rest
          let measured := PhysicalDrawSequenceProgram.batch trials (RetainedEpochFromMasks.bounds c.data.remaining positive) tape
          let ev := measured.requests.map Event.request
          let doneCount := frontCount+(kd+3)
          have head : NaturalRun program doneCount (state heap r saved tape 8) ev (state finished args saved rest 8) := by
            simpa only [doneCount,ev,measured,finished,draft,args,current,Registers.set,List.nil_append,List.append_nil] using
              append_run start (append_run run steps)
          have count : requestCount ev=reads := (count_reads measured.requests).trans drawCount
          have fits : reads≤tape.length := by
            rw [← drawCount]
            exact PhysicalEpochInputData.successful_tape_fits c.data.remaining positive trials tape t rest reads sampled
          obtain ⟨_,_,_,tailEq,_⟩ := PhysicalEpochInputData.split_draws c.data.remaining positive trials tape t rest reads sampled
          have suffixLen : rest.length=tape.length-reads := by
            have eq : measured.suffix=rest := tailEq
            have drop : measured.suffix=tape.drop measured.requests.length :=
              PhysicalDrawSequenceProgram.batch_suffix trials (RetainedEpochFromMasks.bounds c.data.remaining positive) tape
            rw [← eq,drop,List.length_drop,show measured.requests.length=reads from drawCount]
          obtain ⟨drawLimit,heapLimit⟩ := epoch_bounds b grownSize sBound (ready.width_eq.trans_le curWidth)
          have headTime : doneCount≤ b.stepInstructions heap.length := by
            have d := drawTime.trans (Nat.add_le_add_right drawLimit 4)
            dsimp only [doneCount,frontCount,Limits.stepInstructions]
            omega
          have prefixSpace : allExt.length≤ b.stepCells := by
            have ds := drawSpace.trans heapLimit
            change ec.length≤ b.stabilizeCells at stabilizeSpace
            simp only [allExt,List.length_append,Limits.stepCells]
            omega
          have heapGrow : finished.length≤heap.length+b.stepCells := by
            simpa only [finished,grown,mid,allExt,List.length_append,Nat.add_assoc] using
              Nat.add_le_add_left prefixSpace heap.length
          cases laterRun : ControllerTapeModel.run positive E R trials restarts epochs next rest with
          | none =>
            simp only [Option.map_none]
            try rw [laterRun] at recurse
            obtain ⟨steps,events,out,rejected,short⟩ := recurse
            have missing : tape.length < requestCount (ev++events) := by
              rw [count_append,count]
              omega
            exact ⟨doneCount+steps,ev++events,out,append_run head rejected,missing⟩
          | some result =>
            rcases result with ⟨final,suffix,moreReads⟩
            simp only [Option.map_some]
            try rw [laterRun] at recurse
            obtain ⟨ext,root',v,events,finalWords,finalScale,stored,wordLimit,scaleLimit,body,vtime,vspace,eventCount,enough⟩ := recurse
            have time := loop_advance b (epochs+1) heap.length finished.length doneCount v heapGrow headTime vtime
            have remaining : ext.length≤(epochs+1)*b.stepCells := vspace
            have space : (allExt++ext).length≤(epochs+1+1)*b.stepCells := by
              rw [List.length_append,Nat.succ_mul]
              simpa only [Nat.add_comm ((epochs+1)*b.stepCells) b.stepCells] using Nat.add_le_add prefixSpace remaining
            refine ⟨allExt++ext,root',doneCount+v,ev++events,finalWords,finalScale,?_,wordLimit,scaleLimit,?_,time,space,?_,?_⟩
            · simpa only [finished,grown,mid,allExt,List.append_assoc] using stored
            · simpa only [finished,grown,mid,allExt,List.append_assoc] using append_run head body
            · rw [count_append,count,eventCount]
            · omega

private theorem at_entry (s : NaturalState 15323) (entry : s.pc=0) (quiet : s.stack=[])
    (dense : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

set_option maxHeartbeats 1900000 in
theorem physical_controller {n L W B S H A trials restarts epochs : ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} (initial : BitState 15323)
    (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (settings : Settings (L:=L) (eraseState initial).heap (eraseState initial).registers.c adj R M trials restarts)
    (cache : Stored (eraseState initial).heap (eraseState initial).registers.d s positive EN E words scale)
    (epochsAt : IndexSpine (eraseState initial).heap (eraseState initial).registers.a epochs)
    (hW : 1≤W) (labelWidth : n.size≤W) (gridWidth : RetainedEpochFromMasks.width n L≤W) (hB : B≤W)
    (grid : max L.size (L+1).size≤B) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (scaleBound : scale.length+2*restarts*(epochs+1)≤S) :
    let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
    let budget := instructionBound b epochs H
    match ControllerTapeModel.run positive E R trials restarts epochs s initial.source with
    | none => ∀ limit paid,GuardedReferenceExecution.execute program limit initial paid=none
    | some (result,(rest,reads)) =>
      ∃ (out : BitState 15323) (paid : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
        GuardedReferenceExecution.execute program (budget+1) initial 0=some (out,paid) ∧
        Stored (eraseState out).heap (eraseState out).registers.d result positive EN E nextWords nextScale ∧
        (∀ ws∈nextWords,∀ w∈ws,w.length≤B) ∧ nextScale.length≤S ∧
        out.source=rest ∧ out.stack=[] ∧ out.pc=1 ∧ reads≤ initial.source.length ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length≤(epochs+1)*b.stepCells) ∧
        paid≤ completeBound 15323 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 15323 := by
  let old := eraseState initial
  let frame : Frame ℕ 15323 := ⟨1,.r3,old.registers⟩
  let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
  let budget := instructionBound b epochs H
  have empty : old.stack=[] := by simp [old,eraseState,State.map,quiet]
  have initialAt : old=state old.heap old.registers [] initial.source 0 := at_entry old entry empty dense
  have enter : tickNatural program old=some ⟨state old.heap old.registers [frame] initial.source 8,[],0⟩ := by
    conv_lhs => arg 2; rw [initialAt]
    rfl
  have execution := natural_loop s positive EN E settings cache epochsAt hW labelWidth gridWidth hB grid widths scaleBound
    frame [] initial.source
  cases exactRun : ControllerTapeModel.run positive E R trials restarts epochs s initial.source with
  | none =>
    rw [exactRun] at execution
    obtain ⟨k,events,out,body,short⟩ := execution
    obtain ⟨_,_,actual,_,_,_,_⟩ := polynomial_simulation bounded (.step enter body)
    exact fun limit paid => GuardedReferencePrefix.rejects_prefix actual short limit paid
  | some result =>
    rcases result with ⟨final,rest,reads⟩
    rw [exactRun] at execution
    obtain ⟨ext,root,k,events,nextWords,nextScale,stored,wordBound,newScale,body,time,allocation,count,fits⟩ := execution
    let done := state (old.heap++ext) (old.registers.set .r3 root) [] rest 1
    have run : NaturalRun program (k+1) old events done := .step enter body
    have halt : tickNatural program done=none := rfl
    obtain ⟨q,out,actual,matchState,stopped,cost,tape⟩ := terminating_simulation bounded run halt
    have heapCap : old.heap.length≤H := by
      have hh := bounded.1
      simp only [State.records] at hh
      simpa only [old,eraseState,State.map,List.length_map] using (Nat.le_add_right _ _).trans
        ((Nat.le_add_right (initial.heap.length+initial.stack.length) 1).trans hh)
    have enough : k+1≤budget := by
      change k≤loopLimit b (epochs+1) old.heap.length at time
      have mono : loopLimit b (epochs+1) old.heap.length≤loopLimit b (epochs+1) H := by
        unfold loopLimit
        gcongr
      exact Nat.add_le_add_right (time.trans mono) 1
    have guarded := GuardedReferenceExecution.execute_eq actual stopped (budget+1) 0 (by omega)
    rw [count,ite_eq_left fits] at guarded
    refine ⟨out,_,nextWords,nextScale,guarded,?_,wordBound,newScale,tape,?_,?_,fits,⟨ext,?_,allocation⟩,?_⟩
    · rw [matchState]; exact stored
    · have noFrames : (eraseState out).stack=[] := by rw [matchState]; rfl
      simpa [eraseState,State.map] using noFrames
    · exact congrArg (fun st : NaturalState 15323 => st.pc) matchState
    · rw [matchState]; rfl
    · have hard := cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ enough)
      have guard := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 15323) (Nat.add_le_add_right enough 1)
      simpa only [Nat.zero_add] using Nat.add_le_add hard guard

end DirectedFlowCutGap.AdaptiveControllerExecution
