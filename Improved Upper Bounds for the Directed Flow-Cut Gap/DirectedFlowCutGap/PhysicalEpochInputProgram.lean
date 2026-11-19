import DirectedFlowCutGap.PhysicalEpochInputData
import DirectedFlowCutGap.EpochActiveFromMaskProgram
import DirectedFlowCutGap.EpochMaterializeProgram

/-! Read the fair tape and materialize the epoch's order and stored grid table. -/

namespace DirectedFlowCutGap.PhysicalEpochInputProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open GraphWalkExtension (EdgeList)
open EpochActiveFromMaskProgram (labelPair Payloads payloads_extend)
open PhysicalDrawSequenceProgram (StoredBatch batch batch_extend)
open PhysicalBoundedDrawProgram (Outcome)
open EpochPermutationProgram (indices)

def activeLabel (pc : Fin 66) : Fin 401 := ⟨16+pc.val,by omega⟩
def epochLabel (pc : Fin 174) : Fin 401 := ⟨82+pc.val,by omega⟩
def materializeLabel (pc : Fin 145) : Fin 401 := ⟨256+pc.val,by omega⟩

def program : Program 401 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 1 => .call (epochLabel 0) 2 .r2
    | 2 => .call 12 3 .r3
    | 8 => .move .r1 .r3 (activeLabel 0)
    | 12 => .move .r0 .r3 13
    | 13 => .move .r1 .r2 (materializeLabel 0)
    | _ => .halt
  else if h : pc.val<82 then
    if pc.val=20 then .ret .r3
    else ReferenceProgramLabels.instruction activeLabel (EpochActiveFromMaskProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<256 then
    if pc.val=177 then .ret .r3
    else ReferenceProgramLabels.instruction epochLabel (RetainedEpochFromMasks.program ⟨pc.val-82,by omega⟩)
  else if pc.val=260 then .ret .r3
  else ReferenceProgramLabels.instruction materializeLabel
    (EpochMaterializeProgram.program ⟨pc.val-256,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 401))
    (tape : Bits) (pc : Fin 401) : NaturalState 401 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (tape : Bits) : ℕ :=
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (RetainedEpochFromMasks.bounds a positive) tape
  EpochActiveFromMaskProgram.steps a+RetainedEpochFromMasks.steps a positive fuel tape+
    EpochMaterializeProgram.steps (out.draws.take m) m+9

def Output {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (a : PairFlags n)
    (positive : 0<L) (t : RetainedTapeInput.Tape L a) (grid : List Outcome) : Prop :=
  ∃ original order,Payloads heap original (RetainedTapeInput.activeList a) ∧
    Payloads heap order (RetainedTapeInput.materialize positive a t).order ∧
    EpochMaterializeProgram.Output heap root order original grid ∧
    indices grid=PhysicalEpochDraws.cellValues L (Fintype.card ↥(remainingSet a)) t.2

private theorem active_slots (pc : Fin 66) (h : EpochActiveFromMaskProgram.program pc≠.halt) :
    program (activeLabel pc)=ReferenceProgramLabels.instruction activeLabel (EpochActiveFromMaskProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,activeLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<82 by omega,show 16+pc.val≠20 by omega]

private theorem epoch_slots (pc : Fin 174) (h : RetainedEpochFromMasks.program pc≠.halt) :
    program (epochLabel pc)=ReferenceProgramLabels.instruction epochLabel (RetainedEpochFromMasks.program pc) := by
  by_cases hp : pc.val=95
  · have eq : pc=95 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,epochLabel,show ¬82+pc.val<16 by omega,show ¬82+pc.val<82 by omega,
      show 82+pc.val<256 by omega,show 82+pc.val≠177 by omega]

private theorem materialize_slots (pc : Fin 145) (h : EpochMaterializeProgram.program pc≠.halt) :
    program (materializeLabel pc)=ReferenceProgramLabels.instruction materializeLabel (EpochMaterializeProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,materializeLabel,show ¬256+pc.val<16 by omega,show ¬256+pc.val<82 by omega,
      show ¬256+pc.val<256 by omega,show 256+pc.val≠260 by omega]

private theorem active_call {n : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (mask : RetainedDemandEraseProgram.RowsAt heap r.a a)
    (pairs : EdgeList heap r.d ((RetainedMassTableProgram.pairOrder n).map labelPair)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (refs : List ℕ),PointerList (heap++ext) root refs ∧
      Payloads (heap++ext) refs (RetainedTapeInput.activeList a) ∧
      NaturalRun program (EpochActiveFromMaskProgram.steps a+3) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let args := r.set .r1 r.d
  let frame : Frame ℕ 401 := ⟨1,.r3,r⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape (activeLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,regs,root,refs,ordered,payloads,body⟩ := EpochActiveFromMaskProgram.natural_active (r:=args) mask pairs tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (activeLabel 4)
  have lifted := ReferenceProgramLabels.run activeLabel EpochActiveFromMaskProgram.program program active_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  let work := EpochActiveFromMaskProgram.steps a
  have run : NaturalRun program work (state heap args [frame] tape (activeLabel 0)) [] stop := by
    simpa [state,stop,work,EpochActiveFromMaskProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,activeLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,refs,ordered,payloads,?_⟩
  have count : 2+(work+1)=work+3 := by omega
  change NaturalRun program (work+3) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem draw_call {n L fuel : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ} (positive : 0<L)
    (mask : RetainedDemandEraseProgram.RowsAt heap r.a a) (grid : BoolList heap r.b L.bits)
    (trials : IndexSpine heap r.c fuel) (tape : Bits) :
    let out := batch fuel (RetainedEpochFromMasks.bounds a positive) tape
    ∃ ext root,StoredBatch (heap++ext) root out.draws ∧
      NaturalRun program (RetainedEpochFromMasks.steps a positive fuel tape+2) (state heap r [] tape 1)
        (out.requests.map Event.request) (state (heap++ext) (r.set .r2 root) [] out.suffix 2) := by
  let drawn := batch fuel (RetainedEpochFromMasks.bounds a positive) tape
  obtain ⟨ext,args,rep,body⟩ := RetainedEpochFromMasks.natural_epoch positive mask grid trials tape
  let frame : Frame ℕ 401 := ⟨2,.r2,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape (epochLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) args [frame] drawn.suffix (epochLabel 95)
  have lifted := ReferenceProgramLabels.run epochLabel RetainedEpochFromMasks.program program epoch_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (RetainedEpochFromMasks.steps a positive fuel tape)
      (state heap r [frame] tape (epochLabel 0)) (drawn.requests.map Event.request) stop := by
    simpa [state,stop,drawn,RetainedEpochFromMasks.state,RetainedEpochFromMasks.drawLabel,
      ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 args.d) [] drawn.suffix 2,[],0⟩ := by
    simp [state,stop,program,epochLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,args.d,rep,?_⟩
  simpa only [List.nil_append,List.append_nil] using NaturalRun.step enter (append_run run (.step ret (.done _)))

private theorem materialize_call {heap : NaturalHeap} {r : Registers ℕ} {refs : List ℕ} {pre post : List Outcome}
    (original : PointerList heap r.d refs) (draws : StoredBatch heap r.c (pre++post))
    (valid : EpochPermutationData.Valid (indices pre) refs.length) (len : post.length=refs.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (order : List ℕ),EpochPermutationData.reorder (indices pre) refs=some order ∧
      EpochMaterializeProgram.Output (heap++ext) root order refs post ∧
      NaturalRun program (EpochMaterializeProgram.steps pre refs.length+4) (state heap r [] tape 2) []
        (state (heap++ext) (r.set .r3 root) [] tape 3) := by
  let args := (r.set .r0 r.d).set .r1 r.c
  let frame : Frame ℕ 401 := ⟨3,.r3,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 2) []
      (state heap args [frame] tape (materializeLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,regs,root,order,eq,rep,body⟩ := EpochMaterializeProgram.natural_materialize (r:=args) original draws valid len tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (materializeLabel 4)
  have lifted := ReferenceProgramLabels.run materializeLabel EpochMaterializeProgram.program program materialize_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  let work := EpochMaterializeProgram.steps pre refs.length
  have run : NaturalRun program work (state heap args [frame] tape (materializeLabel 0)) [] stop := by
    simpa [state,stop,work,EpochMaterializeProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 3,[],0⟩ := by
    simp [state,stop,program,materializeLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,order,eq,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem payloads_map {m n : ℕ} {heap : NaturalHeap} {xs : List ℕ} {ps : List (Pair n)}
    (data : Payloads heap xs ps) (xlen : xs.length=m) (plen : ps.length=m) (is : List (Fin m)) :
    Payloads heap (is.map (fun i => xs[i.val]'(xlen ▸ i.isLt))) (is.map (fun i => ps[i.val]'(plen ▸ i.isLt))) := by
  induction is with
  | nil => exact .nil
  | cons i is ih => exact .cons (data.get (xlen ▸ i.isLt) (plen ▸ i.isLt)) ih

private theorem rows_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {mask : PairFlags n}
    (stored : RetainedDemandEraseProgram.RowsAt heap root mask) (ext : NaturalHeap) :
    RetainedDemandEraseProgram.RowsAt (heap++ext) root mask := by
  obtain ⟨refs,spine,rows⟩ := stored
  exact ⟨refs,pointerList_extend spine ext,rows.imp (fun _ _ rep => boolList_extend rep ext)⟩

theorem natural_observed_input {n L fuel : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (positive : 0<L) (mask : RetainedDemandEraseProgram.RowsAt heap r.a a) (grid : BoolList heap r.b L.bits)
    (trials : IndexSpine heap r.c fuel) (pairs : EdgeList heap r.d ((RetainedMassTableProgram.pairOrder n).map labelPair))
    (source : Bits) :
    let m := Fintype.card ↥(remainingSet a)
    let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
    ∃ (ext : NaturalHeap) (regs : Registers ℕ) (root : ℕ) (original order : List ℕ),
      Payloads (heap++ext) original (RetainedTapeInput.activeList a) ∧
      EpochPermutationData.reorder (indices (out.draws.take m)) original=some order ∧
      EpochMaterializeProgram.Output (heap++ext) root order original (out.draws.drop m) ∧
      NaturalRun program (steps a positive fuel source) (state heap r [] source 0) (out.requests.map Event.request)
        (state (heap++ext) (regs.set .r3 root) [] out.suffix 3) := by
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
  let pre := out.draws.take m
  let post := out.draws.drop m
  obtain ⟨ea,active,refs,stored,payloads,select⟩ := active_call mask pairs source
  let mid := heap++ea
  let ready := r.set .r3 active
  obtain ⟨ed,draws,batchRep,readTape⟩ := draw_call (r:=ready) positive
    (rows_extend mask ea) (boolList_extend grid ea) (indexSpine_extend trials ea) source
  let grown := mid++ed
  let args := ready.set .r2 draws
  have whole : StoredBatch grown args.c (pre++post) := by
    rw [show pre++post=out.draws from List.take_append_drop m out.draws]
    exact batchRep
  have count : refs.length=m := payloads.length_eq.trans (RetainedTapeInput.activeList_length a)
  have valid : EpochPermutationData.Valid (indices pre) refs.length := by
    rw [count]
    exact PhysicalEpochInputData.permutation_valid a positive fuel source
  have gridLength : post.length=m := PhysicalEpochInputData.grid_length a positive fuel source
  obtain ⟨em,root,order,orderEq,output,materialize⟩ := materialize_call (r:=args)
    (pointerList_extend stored ed) whole valid (gridLength.trans count.symm) out.suffix
  have original := payloads_extend (payloads_extend payloads ed) em
  refine ⟨ea++ed++em,args,root,refs,order,?_,orderEq,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using original
  · simpa only [grown,mid,List.append_assoc] using output
  · let x := EpochActiveFromMaskProgram.steps a
    let y := RetainedEpochFromMasks.steps a positive fuel source
    let z := EpochMaterializeProgram.steps pre m
    have finish : NaturalRun program (z+4) (state grown args [] out.suffix 2) []
        (state (grown++em) (args.set .r3 root) [] out.suffix 3) := by
      simpa only [count] using materialize
    have total : x+3+(y+2+(z+4))=x+y+z+9 := by omega
    change NaturalRun program (x+y+z+9) _ _ _
    rw [← total]
    simpa only [mid,grown,out,args,ready,pre,x,y,z,List.append_assoc,List.nil_append,List.append_nil,
      Registers.set] using append_run select (append_run readTape finish)

theorem natural_epoch_input {n L fuel : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (positive : 0<L) (mask : RetainedDemandEraseProgram.RowsAt heap r.a a) (grid : BoolList heap r.b L.bits)
    (trials : IndexSpine heap r.c fuel) (pairs : EdgeList heap r.d ((RetainedMassTableProgram.pairOrder n).map labelPair))
    (source rest : Bits) (reads : ℕ) (t : RetainedTapeInput.Tape L a)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet a)))) source=some (t,(rest,reads))) :
    let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
    ∃ (ext : NaturalHeap) (regs : Registers ℕ) (root : ℕ),
      Output (heap++ext) root a positive t (out.draws.drop (Fintype.card ↥(remainingSet a))) ∧
      NaturalRun program (steps a positive fuel source) (state heap r [] source 0) (out.requests.map Event.request)
        (state (heap++ext) (regs.set .r3 root) [] rest 3) ∧ out.requests.length=reads := by
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
  obtain ⟨ext,regs,root,refs,order,original,orderEq,materialized,body⟩ :=
    natural_observed_input positive mask grid trials pairs source
  obtain ⟨permutationValues,gridValues,_,tapeEq,readEq⟩ :=
    PhysicalEpochInputData.split_draws a positive fuel source t rest reads sample
  have exactDraws : indices (out.draws.take m)=PhysicalEpochDraws.permutationValues m t.1 := permutationValues
  have count : refs.length=m := original.length_eq.trans (RetainedTapeInput.activeList_length a)
  have same : order=(FinitePermutationSampler.run m t.1).order.map (fun i => refs[i.val]'(by rw [count]; exact i.isLt)) := by
    change EpochPermutationData.reorder (indices (out.draws.take m)) refs=some order at orderEq
    rw [exactDraws,EpochPermutationData.reorder_tape m t.1 refs count] at orderEq
    exact (Option.some.inj orderEq).symm
  have orderData := payloads_map original count (RetainedTapeInput.activeList_length a) (FinitePermutationSampler.run m t.1).order
  rw [← same,← PhysicalEpochInputData.materialized_order a positive t] at orderData
  have unread : (batch fuel (RetainedEpochFromMasks.bounds a positive) source).suffix=rest := tapeEq
  refine ⟨ext,regs,root,⟨refs,order,original,orderData,materialized,gridValues⟩,?_,readEq⟩
  simpa only [unread] using body

def instructionBound (n L fuel : ℕ) : ℕ :=
  EpochActiveFromMaskProgram.instructionBound n+RetainedEpochFromMasks.instructionBound n L fuel+
    EpochPermutationProgram.instructionBound (n*n) (RetainedEpochFromMasks.width n L)+
    EpochGridTableProgram.steps (n*n)+16

theorem steps_le {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (source : Bits) :
    steps a positive fuel source ≤ instructionBound n L fuel := by
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
  let pre := out.draws.take m
  have valid : EpochPermutationData.Valid (indices pre) m :=
    PhysicalEpochInputData.permutation_valid a positive fuel source
  have widths := PhysicalEpochInputData.batch_widths fuel (RetainedEpochFromMasks.bounds a positive) source
    (RetainedEpochFromMasks.widths a positive)
  have boundPerm := EpochPermutationProgram.steps_le pre valid (fun d hd => widths d (List.take_subset m out.draws hd))
  have boundActive := EpochActiveFromMaskProgram.steps_le a
  have boundDraw := RetainedEpochFromMasks.steps_le a positive fuel source
  have card : m ≤ n*n := RetainedDrawTrees.active_card_le a
  have permMono : EpochPermutationProgram.instructionBound m (RetainedEpochFromMasks.width n L) ≤
      EpochPermutationProgram.instructionBound (n*n) (RetainedEpochFromMasks.width n L) := by
    unfold EpochPermutationProgram.instructionBound
    gcongr
  have gridMono : EpochGridTableProgram.steps m ≤ EpochGridTableProgram.steps (n*n) := by
    unfold EpochGridTableProgram.steps
    omega
  change EpochActiveFromMaskProgram.steps a+RetainedEpochFromMasks.steps a positive fuel source+
    EpochMaterializeProgram.steps pre m+9 ≤ _
  unfold instructionBound EpochMaterializeProgram.steps
  omega

private theorem at_entry (s : NaturalState 401) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_epoch_input {n L fuel H A : ℕ} (a : PairFlags n) (positive : 0<L) (initial : BitState 401)
    (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (mask : RetainedDemandEraseProgram.RowsAt (eraseState initial).heap (eraseState initial).registers.a a)
    (grid : BoolList (eraseState initial).heap (eraseState initial).registers.b L.bits)
    (trials : IndexSpine (eraseState initial).heap (eraseState initial).registers.c fuel)
    (pairs : EdgeList (eraseState initial).heap (eraseState initial).registers.d
      ((RetainedMassTableProgram.pairOrder n).map labelPair))
    (t : RetainedTapeInput.Tape L a) (rest : Bits) (reads : ℕ)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet a)))) initial.source=some (t,(rest,reads))) :
    let observed := batch fuel (RetainedEpochFromMasks.bounds a positive) initial.source
    let budget := instructionBound n L fuel
    ∃ out paid,GuardedReferenceExecution.execute program (budget+1) initial 0=some (out,paid) ∧
      Output (eraseState out).heap (eraseState out).registers.d a positive t
        (observed.draws.drop (Fintype.card ↥(remainingSet a))) ∧
      out.source=rest ∧ out.stack=[] ∧ out.pc=3 ∧ observed.requests.length=reads ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      paid ≤ completeBound 401 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 401 := by
  let old := eraseState initial
  let observed := batch fuel (RetainedEpochFromMasks.bounds a positive) initial.source
  let budget := instructionBound n L fuel
  obtain ⟨ext,regs,root,rep,body,count⟩ := natural_epoch_input positive mask grid trials pairs initial.source rest reads t sample
  let final := state (old.heap++ext) (regs.set .r3 root) [] rest 3
  have quiet : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps a positive fuel initial.source) old (observed.requests.map Event.request) final := by
    rw [at_entry old hp quiet hn]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,matchState,stopped,cost,tape⟩ := terminating_simulation bounded trace halt
  have within : steps a positive fuel initial.source ≤ budget := steps_le a positive fuel initial.source
  have advance := GuardedReferenceExecution.execute_eq execution stopped (budget+1) 0 (by omega)
  have fits : observed.requests.length ≤ initial.source.length :=
    PhysicalEpochInputData.successful_tape_fits a positive fuel initial.source t rest reads sample
  rw [GuardedReferenceExecution.count_reads,ite_eq_left fits] at advance
  have costBound := cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ within)
  have guardBound := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 401) (Nat.add_le_add_right within 1)
  refine ⟨out,_,advance,?_,tape,?_,?_,count,⟨ext,?_⟩,?_⟩
  · rw [matchState]; exact rep
  · have h := congrArg (fun s : NaturalState 401 => s.stack) matchState
    simpa [eraseState,State.map,final,state] using h
  · have h := congrArg (fun s : NaturalState 401 => s.pc) matchState
    exact h
  · rw [matchState]; rfl
  · simpa only [Nat.zero_add] using Nat.add_le_add costBound guardBound

theorem physical_epoch_rejected {n L fuel H A : ℕ} (a : PairFlags n) (positive : 0<L) (initial : BitState 401)
    (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (mask : RetainedDemandEraseProgram.RowsAt (eraseState initial).heap (eraseState initial).registers.a a)
    (grid : BoolList (eraseState initial).heap (eraseState initial).registers.b L.bits)
    (trials : IndexSpine (eraseState initial).heap (eraseState initial).registers.c fuel)
    (pairs : EdgeList (eraseState initial).heap (eraseState initial).registers.d
      ((RetainedMassTableProgram.pairOrder n).map labelPair))
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet a)))) initial.source=none) :
    GuardedReferenceExecution.execute program (instructionBound n L fuel+1) initial 0=none := by
  let old := eraseState initial
  let observed := batch fuel (RetainedEpochFromMasks.bounds a positive) initial.source
  let budget := instructionBound n L fuel
  have exactTape := PhysicalEpochDraws.epoch_run fuel L (Fintype.card ↥(remainingSet a)) positive initial.source
  rw [sample] at exactTape
  change none =
    (if observed.requests.length ≤ initial.source.length then
      some (indices observed.draws,(observed.suffix,0+observed.requests.length)) else none) at exactTape
  have short : ¬ observed.requests.length ≤ initial.source.length := by
    intro enough
    rw [ite_eq_left enough] at exactTape
    contradiction
  obtain ⟨ext,regs,root,_,_,_,_,_,body⟩ := natural_observed_input positive mask grid trials pairs initial.source
  let final := state (old.heap++ext) (regs.set .r3 root) [] observed.suffix 3
  have quiet : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps a positive fuel initial.source) old (observed.requests.map Event.request) final := by
    rw [at_entry old hp quiet hn]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨_,out,execution,_,stopped,_,_⟩ := terminating_simulation bounded trace halt
  have within : steps a positive fuel initial.source ≤ budget := steps_le a positive fuel initial.source
  have guard := GuardedReferenceExecution.execute_eq execution stopped (budget+1) 0 (by omega)
  rw [GuardedReferenceExecution.count_reads,ite_eq_right short] at guard
  exact guard

end DirectedFlowCutGap.PhysicalEpochInputProgram
