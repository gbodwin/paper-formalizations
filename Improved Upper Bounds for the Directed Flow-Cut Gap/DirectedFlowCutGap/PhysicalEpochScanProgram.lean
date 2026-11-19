import DirectedFlowCutGap.EpochScanProgram
import DirectedFlowCutGap.GuardedReferencePrefix

/-! Draw the actual epoch and execute its physical scan on the same heap. -/

namespace DirectedFlowCutGap.PhysicalEpochScanProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open EpochScanData (Graph Stored stored_extend cacheOf)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (EdgeList edgeList_extend)
open CandidateEnumeration (Node Network)

def inputLabel (pc : Fin 401) : Fin 7789 := ⟨64+pc.val,by omega⟩
def scanLabel (pc : Fin 7324) : Fin 7789 := ⟨465+pc.val,by omega⟩

def program : Program 7789 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 16 1 .r0
    | 1 => .field .r1 .r0 true 2
    | 2 => .field .r0 .r0 false 3
    | 3 => .call (scanLabel 0) 4 .r3
    | 16 => .move .r1 .r0 17
    | 17 => .field .r0 .r2 false 18
    | 18 => .field .r0 .r0 true 19
    | 19 => .field .r2 .r0 true 20
    | 20 => .field .r2 .r2 true 21
    | 21 => .field .r2 .r2 true 22
    | 22 => .field .r3 .r3 false 23
    | 23 => .field .r3 .r3 false 24
    | 24 => .field .r3 .r3 false 25
    | 25 => .field .r3 .r3 false 26
    | 26 => .field .r0 .r0 false 27
    | 27 => .make .r0 (.pair .r0 .r3) 28
    | 28 => .field .r3 .r0 false 29
    | 29 => .field .r0 .r0 true 30
    | 30 => .make .r1 (.pair .r1 .r2) 31
    | 31 => .field .r2 .r1 false 32
    | 32 => .field .r1 .r1 true 33
    | 33 => .call (inputLabel 0) 34 .r3
    | 34 => .ret .r3
    | _ => .halt
  else if h : pc.val<465 then
    if pc.val=67 then .ret .r3
    else ReferenceProgramLabels.instruction inputLabel (PhysicalEpochInputProgram.program ⟨pc.val-64,by omega⟩)
  else if pc.val=466 then .ret .r3
  else ReferenceProgramLabels.instruction scanLabel (EpochScanProgram.program ⟨pc.val-465,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 7789

def instructionBound (n L fuel H W B scale ratio threshold : ℕ) : ℕ :=
  let epoch := PhysicalEpochInputProgram.instructionBound n L fuel
  let alloc := EpochScanBounds.stepCells n L (n*n) W B scale ratio threshold
  let base := EpochScanBounds.baseInstructions n L (n*n) W B scale ratio threshold
  epoch+25+EpochScanBounds.loopBound (n*n) (H+epoch+21) alloc base+1

def allocationBound (n L fuel W B scale ratio threshold : ℕ) : ℕ :=
  PhysicalEpochInputProgram.instructionBound n L fuel+21+
    (n*n)*EpochScanBounds.stepCells n L (n*n) W B scale ratio threshold

private theorem input_slots (pc : Fin 401) (h : PhysicalEpochInputProgram.program pc≠.halt) :
    program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (PhysicalEpochInputProgram.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,inputLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<465 by omega,show 64+pc.val≠67 by omega]

private theorem scan_slots (pc : Fin 7324) (h : EpochScanProgram.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (EpochScanProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,scanLabel,show ¬465+pc.val<64 by omega,show ¬465+pc.val<465 by omega,show 465+pc.val≠466 by omega]

set_option maxHeartbeats 2100000 in
private theorem prepare {n L trials : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} {s : Code (Graph adj) demands L} {positive : 0<L}
    {EN : ResidualSearch.Enumeration (Node n L)} {E : ResidualSearch.Enumeration (Network n L)}
    {R M scale : Bits} {words : List (List Bits)}
    (guard : IndexSpine heap r.a trials) (params : Parameters (L:=L) heap r.c adj R M)
    (cache : Stored heap r.d s positive EN E words scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ),
      RetainedDemandEraseProgram.RowsAt (heap++ext) args.a s.data.remaining ∧ BoolList (heap++ext) args.b L.bits ∧
      IndexSpine (heap++ext) args.c trials ∧
      EdgeList (heap++ext) args.d ((RetainedMassTableProgram.pairOrder n).map labelPair) ∧
      NaturalRun program 18 (state heap r [] tape 0) [] (state (heap++ext) args [⟨1,.r0,r⟩] tape 33) := by
  obtain ⟨static,gates,round,refresh,graph,config,pairs,shared,atConfig,atStatic,atRound,atRefresh,gate,
    graphRep,configRep,original,⟨gs,labelsGrid,labels,grid,vs,atShared,atLabels,_,_,_,gridRep⟩⟩ := params
  obtain ⟨live,best,atCache,⟨packed,runtime,context,scaleRoot,weights,free,atState,updated,rr,rc,rt,rf,rs,rv,rd⟩,_⟩ := cache
  obtain ⟨masks,mass,bits,atPacked,⟨active,cut,atMasks,activeRep,cutRep⟩,massRep,massValue⟩ := updated
  let frame : Frame ℕ 7789 := ⟨1,.r0,r⟩
  let first : Registers ℕ := ⟨refresh,r.a,r.c,r.d⟩
  let second : Registers ℕ := ⟨refresh,r.a,grid,live⟩
  let third : Registers ℕ := ⟨pairs,r.a,grid,active⟩
  have locate : NaturalRun program 4 (state heap r [] tape 0) [] (state heap first [frame] tape 19) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,first,atConfig,atStatic]
  have load : NaturalRun program 4 (state heap first [frame] tape 19) [] (state heap second [frame] tape 23) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      first,second,atRefresh,atShared,atLabels,atCache]
  have fields : NaturalRun program 4 (state heap second [frame] tape 23) [] (state heap third [frame] tape 27) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      second,third,atState,atPacked,atMasks,atRefresh]
  let firstPair : Cell ℕ := .pair pairs active
  let secondPair : Cell ℕ := .pair r.a grid
  let mid := heap++[firstPair]
  let ext : NaturalHeap := [firstPair,secondPair]
  let fourth : Registers ℕ := ⟨active,r.a,grid,pairs⟩
  let args : Registers ℕ := ⟨active,grid,r.a,pairs⟩
  have swap : NaturalRun program 3 (state heap third [frame] tape 27) [] (state mid fourth [frame] tape 30) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,third,fourth,mid,firstPair]
  have swap' : NaturalRun program 3 (state mid fourth [frame] tape 30) [] (state (heap++ext) args [frame] tape 33) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,fourth,args,mid,ext,secondPair]
  have activeAt : RetainedDemandEraseProgram.RowsAt (heap++ext) args.a s.data.remaining := by
    obtain ⟨refs,list,rows⟩ := activeRep
    exact ⟨refs,BinaryPointerListRead.pointerList_extend list ext,rows.imp (fun _ _ h => boolList_extend h ext)⟩
  exact ⟨ext,args,activeAt,boolList_extend gridRep ext,indexSpine_extend guard ext,edgeList_extend original ext,
    append_run locate (append_run load (append_run fields (append_run swap swap')))⟩

private theorem sample_call {heap ext : NaturalHeap} {r args out : Registers ℕ} {ep : NaturalHeap} {root k : ℕ}
    {tape rest : Bits} {events : List Event}
    (load : NaturalRun program 18 (state heap r [] tape 0) [] (state (heap++ext) args [⟨1,.r0,r⟩] tape 33))
    (body : NaturalRun PhysicalEpochInputProgram.program k (PhysicalEpochInputProgram.state (heap++ext) args [] tape 0)
      events (PhysicalEpochInputProgram.state (heap++ext++ep) (out.set .r3 root) [] rest 3)) :
    NaturalRun program (k+21) (state heap r [] tape 0) events (state (heap++(ext++ep)) (r.set .r0 root) [] rest 1) := by
  let frame : Frame ℕ 7789 := ⟨1,.r0,r⟩
  let stop := state (heap++ext++ep) (args.set .r3 root) [frame] rest 34
  have invoke := ReferenceProgramInvocation.call inputLabel input_slots (caller:=33) (continuation:=34)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  have run : NaturalRun program (k+2) (state (heap++ext) args [frame] tape 33) events stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++ext++ep) (r.set .r0 root) [] rest 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  have count : 18+(k+2+1)=k+21 := by omega
  rw [← count]
  simpa only [List.append_assoc,List.nil_append,List.append_nil] using append_run load (append_run run (.step ret (.done _)))

private theorem grid_word_width {n W : ℕ} (cells : List (Pair n×Bits)) (p : Pair n)
    (widths : ∀ cell ∈ cells, cell.2.length≤W) : (EpochGridLookupProgram.word p cells).length≤W := by
  induction cells with
  | nil => simp [EpochGridLookupProgram.word]
  | cons cell cells ih =>
    rcases cell with ⟨q, bits⟩
    simp only [EpochGridLookupProgram.word]
    split
    · exact widths (q,bits) List.mem_cons_self
    · exact ih (fun cell h => widths cell (List.mem_cons_of_mem _ h))

private theorem scan_bound (n L W B scale ratio threshold H h : ℕ) {cells count : ℕ}
    (hc : cells≤n*n) (hm : count≤n*n) (hh : h≤H) :
    EpochScanBounds.loopBound count h (EpochScanBounds.stepCells n L cells W B scale ratio threshold)
      (EpochScanBounds.baseInstructions n L cells W B scale ratio threshold) ≤
    EpochScanBounds.loopBound (n*n) H (EpochScanBounds.stepCells n L (n*n) W B scale ratio threshold)
      (EpochScanBounds.baseInstructions n L (n*n) W B scale ratio threshold) := by
  unfold EpochScanBounds.loopBound EpochScanBounds.stepCells EpochScanBounds.baseInstructions EpochScanBounds.roundBound
    AdaptiveRoundRefreshProgram.instructionBound EpochSelectedRoundProgram.instructionBound EpochGridLookupProgram.instructionBound
  gcongr

private theorem scan_allocation_bound (n L W B scale ratio threshold : ℕ) {cells count : ℕ}
    (hc : cells≤n*n) (hm : count≤n*n) :
    count*EpochScanBounds.stepCells n L cells W B scale ratio threshold ≤
      (n*n)*EpochScanBounds.stepCells n L (n*n) W B scale ratio threshold := by
  unfold EpochScanBounds.stepCells EpochScanBounds.roundBound AdaptiveRoundRefreshProgram.instructionBound
    EpochSelectedRoundProgram.instructionBound EpochGridLookupProgram.instructionBound
  gcongr

private theorem dispatch {heap : NaturalHeap} {r : Registers ℕ} {root order cells : ℕ} {tape : Bits}
    (atRoot : heap[root]?=some (.pair order cells)) :
    NaturalRun program 2 (state heap (r.set .r0 root) [] tape 1) []
      (state heap ⟨order,cells,r.c,r.d⟩ [] tape 3) := by
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,atRoot]

set_option maxHeartbeats 2200000 in
theorem natural_epoch_scan {n L fuel W B H : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (guard : IndexSpine heap r.a fuel) (params : Parameters (L:=L) heap r.c adj R M)
    (cache : Stored heap r.d s positive EN E words scale) (heapSize : heap.length≤H)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : RetainedEpochFromMasks.width n L≤W)
    (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (tape rest : Bits) (reads : ℕ) (t : RetainedTapeInput.Tape L s.data.remaining)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) tape=some (t,(rest,reads))) :
    let input := RetainedTapeInput.materialize positive s.data.remaining t
    let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds s.data.remaining positive) tape
    ∃ (ext : NaturalHeap) (root orderRoot cellRoot k : ℕ),
      Stored (heap++ext) root (EpochScanData.scan positive E R M input.cell input.order s) positive EN E words scale ∧
      NaturalRun program k (state heap r [] tape 0) (observed.requests.map Event.request)
        (state (heap++ext) ⟨orderRoot,cellRoot,r.c,root⟩ [] rest 4) ∧
      k≤ instructionBound n L fuel H W B scale.length R.length M.length ∧
      ext.length≤ allocationBound n L fuel W B scale.length R.length M.length ∧ observed.requests.length=reads := by
  let a := s.data.remaining
  let input := RetainedTapeInput.materialize positive a t
  let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds a positive) tape
  let m := Fintype.card ↥(remainingSet a)
  let drawn := observed.draws.drop m
  let cells := (RetainedTapeInput.activeList a).zip (drawn.map PhysicalBoundedDrawProgram.Outcome.index)
  obtain ⟨ep,args,mask,grid,trials,pairs,load⟩ := prepare guard params cache tape
  obtain ⟨ee,regs,result,output,body,count⟩ := PhysicalEpochInputProgram.natural_epoch_input positive mask grid trials pairs
    tape rest reads t sample
  let start := heap++(ep++ee)
  have rep : PhysicalEpochInputProgram.Output start result a positive t drawn := by
    simpa only [start,List.append_assoc] using output
  obtain ⟨orderRoot,cellRoot,atRoot,orderRep,cellRep,values⟩ := EpochGridLookupProgram.stored_epoch rep
  let scanArgs : Registers ℕ := ⟨orderRoot,cellRoot,r.c,r.d⟩
  have rowCount : (RetainedTapeInput.activeList a).length=m := RetainedTapeInput.activeList_length a
  have card : m≤n*n := RetainedDrawTrees.active_card_le a
  have cellCount : cells.length≤ n*n := by
    simp only [cells,List.length_zip,rowCount]
    exact (Nat.min_le_left _ _).trans card
  have orderCount : input.order.length≤ n*n := by
    rw [show input.order.length=(remainingSet a).card from RetainedTapeInput.materialize_order_length positive a t]
    simpa only [m,Fintype.card_coe] using card
  have widths := PhysicalEpochInputData.batch_widths fuel (RetainedEpochFromMasks.bounds a positive) tape
    (RetainedEpochFromMasks.widths a positive)
  have levels : ∀ p,(EpochGridLookupProgram.word p cells).length≤W := by
    intro p
    apply grid_word_width
    intro entry member
    obtain ⟨d,hd,eq⟩ := List.mem_map.mp (List.of_mem_zip member).2
    rw [← eq]
    exact (widths d (List.drop_subset m observed.draws hd)).trans gridWidth
  obtain ⟨es,root,k,stored,scan,time,scanSpace⟩ := EpochScanProgram.natural_scan s positive EN E input.cell values
    (r:=scanArgs) orderRep cellRep (parameters_extend params (ep++ee)) (stored_extend cache (ep++ee))
    hW vertexWidth rowWidths levels weightWidths rest
  have sampleRun := sample_call load body
  have walk := dispatch (r:=r) (tape:=rest) atRoot
  have invoke := ReferenceProgramInvocation.call scanLabel scan_slots (caller:=3) (continuation:=4)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] scan
  let e := PhysicalEpochInputProgram.steps a positive fuel tape
  have prepareBound : e≤PhysicalEpochInputProgram.instructionBound n L fuel :=
    PhysicalEpochInputProgram.steps_le a positive fuel tape
  have size : start.length≤H+PhysicalEpochInputProgram.instructionBound n L fuel+21 := by
    have grow := ControllerWordWidth.heap_bound sampleRun
    change start.length≤heap.length+(e+21) at grow
    omega
  have finalBound := scan_bound n L W B scale.length R.length M.length
    (H+PhysicalEpochInputProgram.instructionBound n L fuel+21) start.length cellCount orderCount size
  refine ⟨ep++ee++es,root,orderRoot,cellRoot,e+21+(2+(k+2)),?_,?_,?_,?_,count⟩
  · simpa only [start,List.append_assoc] using stored
  · simpa only [e,start,scanArgs,Registers.get,Registers.set,List.append_nil,List.append_assoc] using
      append_run sampleRun (append_run walk invoke)
  · change k ≤ EpochScanBounds.loopBound input.order.length start.length
      (EpochScanBounds.stepCells n L cells.length W B scale.length R.length M.length)
      (EpochScanBounds.baseInstructions n L cells.length W B scale.length R.length M.length)+1 at time
    dsimp only [instructionBound]
    omega
  · have prepSpace : (ep++ee).length≤e+21 := ControllerWordWidth.extension_bound sampleRun rfl
    change es.length ≤ input.order.length*EpochScanBounds.stepCells n L cells.length W B scale.length R.length M.length at scanSpace
    have fullSpace := scanSpace.trans (scan_allocation_bound n L W B scale.length R.length M.length cellCount orderCount)
    dsimp only [allocationBound]
    rw [List.length_append]
    omega

private theorem at_entry (s : NaturalState 7789) (entry : s.pc=0) (quiet : s.stack=[])
    (dense : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

theorem physical_epoch_scan {n L fuel W B H A : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} (initial : BitState 7789)
    (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (guard : IndexSpine (eraseState initial).heap (eraseState initial).registers.a fuel)
    (params : Parameters (L:=L) (eraseState initial).heap (eraseState initial).registers.c adj R M)
    (cache : Stored (eraseState initial).heap (eraseState initial).registers.d s positive EN E words scale)
    (hW : 1≤W) (vertexWidth : n.size≤W) (gridWidth : RetainedEpochFromMasks.width n L≤W)
    (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B)
    (t : RetainedTapeInput.Tape L s.data.remaining) (rest : Bits) (reads : ℕ)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) initial.source=some (t,(rest,reads))) :
    let input := RetainedTapeInput.materialize positive s.data.remaining t
    let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds s.data.remaining positive) initial.source
    let budget := instructionBound n L fuel H W B scale.length R.length M.length
    ∃ out paid,GuardedReferenceExecution.execute program (budget+1) initial 0=some (out,paid) ∧
      Stored (eraseState out).heap (eraseState out).registers.d (EpochScanData.scan positive E R M input.cell input.order s)
        positive EN E words scale ∧
      out.source=rest ∧ out.stack=[] ∧ out.pc=4 ∧ observed.requests.length=reads ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length≤budget) ∧
      paid≤completeBound 7789 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 7789 := by
  let old := eraseState initial
  let budget := instructionBound n L fuel H W B scale.length R.length M.length
  let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds s.data.remaining positive) initial.source
  obtain ⟨ext,root,orderRoot,cellRoot,k,rep,body,within,_,count⟩ := natural_epoch_scan s positive EN E guard params cache
    (by simpa only [eraseState,State.map,List.length_map] using (Nat.le_add_right initial.heap.length (initial.stack.length+1)).trans (by simpa only [State.records,Nat.add_assoc] using bounded.1)) hW vertexWidth gridWidth
    rowWidths weightWidths initial.source rest reads t sample
  let final := state (old.heap++ext) ⟨orderRoot,cellRoot,old.registers.c,root⟩ [] rest 4
  have empty : old.stack=[] := by simp [old,eraseState,State.map,quiet]
  have trace : NaturalRun program k old (observed.requests.map Event.request) final := by
    rw [at_entry old entry empty dense]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,matchState,stopped,cost,tape⟩ := terminating_simulation bounded trace halt
  have advance := GuardedReferenceExecution.execute_eq execution stopped (budget+1) 0 (by omega)
  have fits : observed.requests.length≤ initial.source.length :=
    PhysicalEpochInputData.successful_tape_fits s.data.remaining positive fuel initial.source t rest reads sample
  rw [GuardedReferenceExecution.count_reads,ite_eq_left fits] at advance
  refine ⟨out,_,advance,?_,tape,?_,?_,count,⟨ext,?_,?_⟩,?_⟩
  · rw [matchState]; exact rep
  · have h : (eraseState out).stack=[] := by rw [matchState]; rfl
    simpa [eraseState,State.map] using h
  · exact congrArg (fun s : NaturalState 7789 => s.pc) matchState
  · rw [matchState]; rfl
  · exact (ControllerWordWidth.extension_bound trace rfl).trans within
  · have kernelCost := cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ within)
    have guardCost := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 7789) (Nat.add_le_add_right within 1)
    simpa only [Nat.zero_add] using Nat.add_le_add kernelCost guardCost

theorem natural_epoch_rejected {n L fuel : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (guard : IndexSpine heap r.a fuel) (params : Parameters (L:=L) heap r.c adj R M)
    (cache : Stored heap r.d s positive EN E words scale) (tape : Bits)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) tape=none) :
    let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds s.data.remaining positive) tape
    ∃ (ext : NaturalHeap) (root : ℕ),
      NaturalRun program (PhysicalEpochInputProgram.steps s.data.remaining positive fuel tape+21)
        (state heap r [] tape 0) (observed.requests.map Event.request)
        (state (heap++ext) (r.set .r0 root) [] observed.suffix 1) ∧
      tape.length < GuardedReferenceExecution.requestCount (observed.requests.map Event.request) := by
  let a := s.data.remaining
  let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds a positive) tape
  have exactTape := PhysicalEpochDraws.epoch_run fuel L (Fintype.card ↥(remainingSet a)) positive tape
  rw [sample] at exactTape
  change none =
    (if observed.requests.length≤ tape.length then
      some (EpochPermutationProgram.indices observed.draws,(observed.suffix,0+observed.requests.length)) else none) at exactTape
  have short : tape.length < GuardedReferenceExecution.requestCount (observed.requests.map Event.request) := by
    rw [GuardedReferenceExecution.count_reads]
    by_contra! enough
    rw [ite_eq_left enough] at exactTape
    contradiction
  obtain ⟨ep,args,mask,grid,trials,pairs,load⟩ := prepare guard params cache tape
  obtain ⟨ee,regs,root,_,_,_,_,_,body⟩ := PhysicalEpochInputProgram.natural_observed_input positive mask grid trials pairs tape
  exact ⟨ep++ee,root,sample_call load body,short⟩

theorem physical_epoch_rejected {n L fuel H A : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} (initial : BitState 7789) (limit paid : ℕ)
    (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (guard : IndexSpine (eraseState initial).heap (eraseState initial).registers.a fuel)
    (params : Parameters (L:=L) (eraseState initial).heap (eraseState initial).registers.c adj R M)
    (cache : Stored (eraseState initial).heap (eraseState initial).registers.d s positive EN E words scale)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet s.data.remaining)))) initial.source=none) :
    GuardedReferenceExecution.execute program limit initial paid=none := by
  let old := eraseState initial
  let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds s.data.remaining positive) initial.source
  obtain ⟨ext,root,body,short⟩ := natural_epoch_rejected s positive EN E guard params cache initial.source sample
  have empty : old.stack=[] := by simp [old,eraseState,State.map,quiet]
  have trace : NaturalRun program (PhysicalEpochInputProgram.steps s.data.remaining positive fuel initial.source+21)
      old (observed.requests.map Event.request) (state (old.heap++ext) (old.registers.set .r0 root) [] observed.suffix 1) := by
    rw [at_entry old entry empty dense]
    exact body
  obtain ⟨_,_,run,_,_,_,_⟩ := polynomial_simulation bounded trace
  exact GuardedReferencePrefix.rejects_prefix run short limit paid

end DirectedFlowCutGap.PhysicalEpochScanProgram
