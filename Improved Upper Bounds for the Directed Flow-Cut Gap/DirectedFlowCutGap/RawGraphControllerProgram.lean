import DirectedFlowCutGap.PhysicalControllerControls
import DirectedFlowCutGap.OriginalGraphControllerLaw
import DirectedFlowCutGap.PhysicalCoverReader

/-! Prepare controls from the graph size, run the controller, and return its cut pointer. -/

namespace DirectedFlowCutGap.RawGraphControllerProgram

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open BooleanTableRead (BoolList)
open ConcreteExpressionProgram (append_run)
open RetainedGridState (PairFlags cutSet)
open InitialGraphContexts (Input enumeration)
open PhysicalControllerInitializer (Control initialCode)
open OriginalGraphControllerLaw (epochs ratio readBound)
open AdaptiveControllerBounds (Limits)
open EpochScanData (Stored Graph)
open CandidateEnumeration (Node Network)
open IntegralNetworkFlow
open GuardedReferenceExecution (requestCount)

def controlsLabel (pc : Fin 413) : Fin 26704 := ⟨32+pc.val,by omega⟩
def originalLabel (pc : Fin 26259) : Fin 26704 := ⟨445+pc.val,by omega⟩

def program : Program 26704 := fun pc =>
  if h : pc.val < 32 then
    match pc.val with
    | 0 => .call 16 1 .r1
    | 1 => .call (originalLabel 0) 2 .r3
    | 2 => .field .r3 .r3 false 3
    | 3 => .field .r3 .r3 false 4
    | 4 => .field .r3 .r3 false 5
    | 5 => .field .r3 .r3 true 6
    | 16 => .field .r0 .r0 true 17
    | 17 => .field .r2 .r0 true 18
    | 18 => .field .r2 .r2 true 19
    | 19 => .field .r0 .r0 false 20
    | 20 => .call (controlsLabel 0) 21 .r3
    | 21 => .ret .r3
    | _ => .halt
  else if h : pc.val < 445 then
    if pc.val=42 then .ret .r3
    else ReferenceProgramLabels.instruction controlsLabel (PhysicalControllerControls.program ⟨pc.val-32,by omega⟩)
  else if pc.val=26703 then .ret .r3
  else ReferenceProgramLabels.instruction originalLabel (OriginalGraphControllerProgram.program ⟨pc.val-445,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 26704

private theorem control_slots (pc : Fin 413) (used : PhysicalControllerControls.program pc≠.halt) :
    program (controlsLabel pc)=ReferenceProgramLabels.instruction controlsLabel (PhysicalControllerControls.program pc) := by
  by_cases stop : pc.val=10
  · have eq : pc=10 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,controlsLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<445 by omega,
      show 32+pc.val≠42 by omega]

private theorem original_slots (pc : Fin 26259) (used : OriginalGraphControllerProgram.program pc≠.halt) :
    program (originalLabel pc)=ReferenceProgramLabels.instruction originalLabel (OriginalGraphControllerProgram.program pc) := by
  by_cases stop : pc.val=26258
  · have eq : pc=26258 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,originalLabel,show ¬445+pc.val<32 by omega,show ¬445+pc.val<445 by omega,
      show 445+pc.val≠26703 by omega]

def preparationBound (n : ℕ) (trials : Bits) : ℕ :=
  PhysicalControllerControls.instructionBound n (value trials) trials.length+8

def weightWidth (L : ℕ) : ℕ := max 1 (max L.size (L+1).size)

def wordWidth (n L : ℕ) : ℕ :=
  max (weightWidth L) (max n.size (RetainedEpochFromMasks.width n L))

def scaleWidth (n : ℕ) : ℕ := 1+2*epochs n*(epochs n+1)

def limits (n L : ℕ) (trials : Bits) : Limits :=
  ⟨n,L,value trials,epochs n,wordWidth n L,weightWidth L,scaleWidth n,(ratio n).length,0⟩

def instructionBound (n L H : ℕ) (trials : Bits) : ℕ :=
  let prep := preparationBound n trials
  prep+OriginalGraphControllerProgram.instructionBound (limits n L trials) (epochs n) (H+prep)+6

set_option maxHeartbeats 1600000 in
private theorem prepare {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {trials : Bits}
    (input : Input (L:=L) heap r.a adj) (trial : BoolList heap r.b trials) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Control (heap++ext) root (ratio n) [] (value trials) (epochs n) (epochs n) ∧
      k≤preparationBound n trials ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  obtain ⟨matrix,dims,count,fields,grid,one,atGraph,atDims,atFields,_,nRep,_,oneRep⟩ := input
  let frame : Frame ℕ 26704 := ⟨1,.r1,r⟩
  let args : Registers ℕ := ⟨count,r.b,one,r.d⟩
  have load : NaturalRun program 5 (state heap r [] tape 0) [] (state heap args [frame] tape 20) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atGraph,atDims,atFields]
  obtain ⟨ext,regs,k,control,time,body⟩ := PhysicalControllerControls.natural_controls (r:=args) nRep trial oneRep tape
  have invoke := ReferenceProgramInvocation.call controlsLabel control_slots (caller:=20) (continuation:=21)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  have ret : tickNatural program (state (heap++ext) (args.set .r3 regs.d) [frame] tape 21) =
    some ⟨state (heap++ext) (r.set .r1 regs.d) [] tape 1,[],0⟩ := rfl
  refine ⟨ext,regs.d,k+8,control,by unfold preparationBound; omega,?_⟩
  have count : k+8=5+((k+2)+1) := by omega
  rw [count]
  simpa only [Registers.get,List.nil_append] using append_run load (append_run invoke (.step ret (.done _)))

private theorem cut_pointer {n L : ℕ} {adj : PairFlags n}
    {s : RetainedGridState.Code (Graph adj) (RetainedGridState.remainingSet
      (RetainedDemandMask.compute (Graph adj) (enumeration n) L)) L}
    {positive : 0<L} {EN : ResidualSearch.Enumeration (Node n L)} {E : ResidualSearch.Enumeration (Network n L)}
    {heap : NaturalHeap} {r : Registers ℕ} {words : List (List Bits)} {scale : Bits}
    (data : Stored heap r.d s positive EN E words scale) (tape : Bits) :
    ∃ root,BoolList heap root s.data.cut.toList ∧
      NaturalRun program 4 (state heap r [] tape 2) [] (state heap (r.set .r3 root) [] tape 6) := by
  obtain ⟨live,best,atCache,stateRep,_⟩ := data
  obtain ⟨packed,runtime,context,scale,weights,free,atState,packedRep,_⟩ := stateRep
  obtain ⟨masks,mass,word,atPacked,maskRep,_⟩ := packedRep
  obtain ⟨active,cut,atMasks,_,cutRep⟩ := maskRep
  refine ⟨cut,cutRep,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
    atCache,atState,atPacked,atMasks]

set_option maxHeartbeats 2200000 in
theorem natural_cut {n L H : ℕ} {adj : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ} {trials : Bits}
    (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (heapCap : heap.length≤H) (input : Input (L:=L) heap r.a adj) (trial : BoolList heap r.b trials)
    (tape : Bits) :
    match ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n) (initialCode adj positive) tape with
    | none => ∃ k events stop, NaturalRun program k (state heap r [] tape 0) events stop ∧
        tape.length<requestCount events
    | some (result,(rest,reads)) =>
      ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ) (events : List Event),
        NaturalRun program k (state heap r [] tape 0) events (state (heap++ext) out [] rest 6) ∧
        BoolList (heap++ext) out.d result.data.cut.toList ∧
        requestCount events=reads ∧ reads≤tape.length ∧ k≤ instructionBound n L H trials := by
  obtain ⟨e1,controls,t,control,time,seed⟩ := prepare input trial tape
  let mid := heap++e1
  let regs := r.set .r1 controls
  let prep := preparationBound n trials
  have footprint : mid.length≤H+prep := by
    have h := ControllerWordWidth.heap_bound seed
    change mid.length≤heap.length+t at h
    omega
  have vwidth : n.size≤wordWidth n L := (le_max_left _ _).trans (le_max_right _ _)
  have ewidth : RetainedEpochFromMasks.width n L≤wordWidth n L :=
    (le_max_right _ _).trans (le_max_right _ _)
  have wwidth : weightWidth L≤wordWidth n L := le_max_left _ _
  have one : 1≤wordWidth n L := (le_max_left _ _).trans wwidth
  have level : L.bits.length≤wordWidth n L := by
    rw [Nat.size_eq_bits_len]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans wwidth)
  have main := OriginalGraphControllerProgram.natural_original (r:=regs) (B:=weightWidth L) (S:=scaleWidth n)
    positive EN E footprint (InitialGraphContexts.input_extend input e1) control
    one vwidth ewidth level le_rfl wwidth le_rfl tape
  dsimp only at main
  cases model : ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n)
      (initialCode adj positive) tape with
  | none =>
    rw [model] at main
    obtain ⟨k,events,stop,prefixRun,short⟩ := main
    let frame : Frame ℕ 26704 := ⟨2,.r3,regs⟩
    have start : tickNatural program (state mid regs [] tape 1)=
        some ⟨state mid regs [frame] tape (originalLabel 0),[],0⟩ := rfl
    have lifted := ReferenceProgramLabels.run originalLabel OriginalGraphControllerProgram.program program original_slots prefixRun
    have stack := ReferenceProgramStack.run program [frame] lifted
    have entry : ReferenceProgramStack.state [frame]
        (ReferenceProgramLabels.state originalLabel (OriginalGraphControllerProgram.state mid regs [] tape 0))=
        state mid regs [frame] tape (originalLabel 0) := rfl
    rw [entry] at stack
    have run := append_run seed (.step start stack)
    simp only [List.nil_append] at run
    exact ⟨_,_,_,run,short⟩
  | some answer =>
    rcases answer with ⟨result,rest,reads⟩
    rw [model] at main
    obtain ⟨e2,out,k,events,nextWords,nextScale,body,cache,_,_,count,fits,spent⟩ := main
    have join := ReferenceProgramInvocation.call originalLabel original_slots (caller:=1) (continuation:=2)
      (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] body
    obtain ⟨root,cut,read⟩ := cut_pointer (r:=regs.set .r3 out.d) cache rest
    let final := regs.set .r3 root
    refine ⟨e1++e2,final,t+(k+2)+4,events,?_,?_,count,fits,?_⟩
    · simpa only [final,mid,regs,Registers.set,Registers.get,List.nil_append,List.append_nil,List.append_assoc,Nat.add_assoc]
        using append_run seed (append_run join read)
    · simpa only [mid,final,Registers.set,List.append_assoc] using cut
    · have b : k≤OriginalGraphControllerProgram.instructionBound (limits n L trials) (epochs n) (H+prep) := spent
      change t+(k+2)+4≤prep+OriginalGraphControllerProgram.instructionBound (limits n L trials) (epochs n) (H+prep)+6
      omega

def chargeBound (n L H A : ℕ) (trials : Bits) : ℕ :=
  let t := instructionBound n L H trials
  completeBound 26704 H A t+(t+1)*GuardedReferenceExecution.guardCost 26704

set_option maxHeartbeats 2200000 in
theorem guarded_cut {n L H A : ℕ} {adj : PairFlags n} {trials : Bits}
    (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (initial : BitState 26704) (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (input : Input (L:=L) (eraseState initial).heap (eraseState initial).registers.a adj)
    (trial : BoolList (eraseState initial).heap (eraseState initial).registers.b trials) :
    match ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n)
      (initialCode adj positive) initial.source with
    | none => ∀ limit paid,GuardedReferenceExecution.execute program limit initial paid=none
    | some (result,(rest,reads)) =>
      ∃ (out : BitState 26704) (paid : ℕ),
        GuardedReferenceExecution.execute program (instructionBound n L H trials+1) initial 0=some (out,paid) ∧
        PhysicalCoverReader.readWord (eraseState out).heap (eraseState out).registers.d=some result.data.cut.toList ∧
        out.source=rest ∧ out.pc=6 ∧ out.stack=[] ∧ reads≤ initial.source.length ∧
        paid≤chargeBound n L H A trials := by
  let old := eraseState initial
  let tape := initial.source
  have start : old=state old.heap old.registers [] tape 0 := by
    cases initial
    simp_all [old,tape,eraseState,State.map,ReferenceProgramInvocation.state]
  have heapCap : old.heap.length≤H := by
    have h := bounded.1
    simp only [State.records] at h
    simpa only [old,eraseState,State.map,List.length_map] using (Nat.le_add_right _ _).trans
      ((Nat.le_add_right (initial.heap.length+initial.stack.length) 1).trans h)
  have run := natural_cut positive EN E heapCap input trial tape
  cases model : ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n)
      (initialCode adj positive) tape with
  | none =>
    rw [model] at run
    obtain ⟨k,events,stop,prefixRun,short⟩ := run
    rw [← start] at prefixRun
    obtain ⟨_,_,actual,_,_,_,_⟩ := polynomial_simulation bounded prefixRun
    exact fun limit paid => GuardedReferencePrefix.rejects_prefix actual short limit paid
  | some answer =>
    rcases answer with ⟨result,rest,reads⟩
    rw [model] at run
    obtain ⟨ext,regs,k,events,body,mem,count,fits,time⟩ := run
    rw [← start] at body
    have halt : tickNatural program (state (old.heap++ext) regs [] rest 6)=none := rfl
    obtain ⟨_,out,actual,same,stopped,cost,suffix⟩ := terminating_simulation bounded body halt
    have done := GuardedReferenceExecution.execute_eq actual stopped (instructionBound n L H trials+1) 0 (by omega)
    rw [count,ite_eq_left fits] at done
    refine ⟨out,_,done,?_,suffix,?_,?_,fits,?_⟩
    · rw [same]
      exact PhysicalCoverReader.readWord_eq mem
    · exact congrArg (fun st : NaturalState 26704 => st.pc) same
    · have h : (eraseState out).stack=[] := by rw [same]; rfl
      simpa [eraseState,State.map] using h
    · have paid := cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ time)
      have guards := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 26704) (Nat.add_le_add_right time 1)
      simpa only [chargeBound,Nat.zero_add] using Nat.add_le_add paid guards

end DirectedFlowCutGap.RawGraphControllerProgram
