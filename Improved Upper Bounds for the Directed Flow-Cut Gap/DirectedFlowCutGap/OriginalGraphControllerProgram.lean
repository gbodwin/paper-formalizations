import DirectedFlowCutGap.PhysicalControllerInitializer

/-! Join original-graph initialization and the complete literal-tape controller. -/

namespace DirectedFlowCutGap.OriginalGraphControllerProgram

open BooleanTableRead (IndexSpine)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open RetainedGridState (PairFlags remainingSet)
open InitialGraphContexts (Input enumeration)
open PhysicalControllerInitializer (Control initialCode)
open EpochScanData (Graph Stored)
open AdaptiveControllerBounds (Limits loopLimit)
open CandidateEnumeration (Node Network)
open GuardedReferenceExecution (requestCount)

def initialLabel (pc : Fin 10935) : Fin 26259 := ⟨pc.val,by have := pc.isLt; omega⟩
def controllerLabel (pc : Fin 15323) : Fin 26259 := ⟨10935+pc.val,by omega⟩

def program : Program 26259 := fun pc =>
  if h : pc.val < 10935 then
    if pc.val=7 then .call (controllerLabel 0) 26258 .r3
    else ReferenceProgramLabels.instruction initialLabel (PhysicalControllerInitializer.program ⟨pc.val,h⟩)
  else if h : pc.val < 26258 then
    if pc.val=10936 then .ret .r3
    else ReferenceProgramLabels.instruction controllerLabel (AdaptiveControllerProgram.program ⟨pc.val-10935,by omega⟩)
  else .halt

abbrev state := @ReferenceProgramInvocation.state 26259

def instructionBound (b : Limits) (epochs H : ℕ) : ℕ :=
  let setup := PhysicalControllerInitializer.instructionBound b.vertices b.grid b.word
  setup+AdaptiveControllerBounds.instructionBound b epochs (H+setup)+2

private theorem init_slots (pc : Fin 10935) (h : PhysicalControllerInitializer.program pc≠.halt) :
    program (initialLabel pc)=ReferenceProgramLabels.instruction initialLabel (PhysicalControllerInitializer.program pc) := by
  by_cases stop : pc.val=7
  · have eq : pc=7 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,initialLabel,pc.isLt,stop]

private theorem controller_slots (pc : Fin 15323) (h : AdaptiveControllerProgram.program pc≠.halt) :
    program (controllerLabel pc)=ReferenceProgramLabels.instruction controllerLabel (AdaptiveControllerProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,controllerLabel,show ¬10935+pc.val<10935 by omega,show 10935+pc.val<26258 by omega,
      show 10935+pc.val≠10936 by omega]

private theorem at_entry (s : NaturalState 26259) (entry : s.pc=0) (quiet : s.stack=[])
    (dense : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

set_option maxHeartbeats 3200000 in
theorem natural_original {n L W B S H trials restarts epochs : ℕ} {adj : PairFlags n}
    (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {heap : NaturalHeap} {r : Registers ℕ} {R M : Bits} (initialHeap : heap.length≤H)
    (input : Input (L:=L) heap r.a adj) (controls : Control heap r.b R M trials restarts epochs)
    (hW : 1≤W) (labelWidth : n.size≤W) (epochWidth : RetainedEpochFromMasks.width n L≤W) (levelWidth : L.bits.length≤W)
    (weightsWidth : max 1 (max L.size (L+1).size)≤B) (hB : B≤W) (scaleBound : 1+2*restarts*(epochs+1)≤S)
    (tape : Bits) :
    let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
    let budget := instructionBound b epochs H
    match ControllerTapeModel.run positive E R trials restarts epochs (initialCode adj positive) tape with
    | none => ∃ k events stop, NaturalRun program k (state heap r [] tape 0) events stop ∧
        tape.length<requestCount events
    | some (result,(rest,reads)) =>
      ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ) (events : List Event)
        (nextWords : List (List Bits)) (nextScale : Bits),
        NaturalRun program k (state heap r [] tape 0) events (state (heap++ext) out [] rest 26258) ∧
        Stored (heap++ext) out.d result positive EN E nextWords nextScale ∧
        (∀ ws∈nextWords,∀ w∈ws,w.length≤B) ∧ nextScale.length≤S ∧
        requestCount events=reads ∧ reads≤tape.length ∧ k≤budget := by
  let old := state heap r [] tape 0
  let s := initialCode adj positive
  let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
  let setup := PhysicalControllerInitializer.instructionBound n L W
  let budget := instructionBound b epochs H
  obtain ⟨es,epochRoot,settings,root,k,params,epochCap,cache,body,time⟩ :=
    PhysicalControllerInitializer.natural_initialize positive EN E input controls hW labelWidth levelWidth tape
  let mid := old.heap++es
  let regs : Registers ℕ := ⟨epochRoot,old.registers.b,settings,root⟩
  have prepare : NaturalRun program k old [] (state mid regs [] tape 7) := by
    have atStart : initialLabel 0=0 := rfl
    have atFinish : initialLabel 7=7 := rfl
    simpa only [mid,regs,old,atStart,atFinish,ReferenceProgramLabels.state,ReferenceProgramInvocation.state,List.map_nil] using
      ReferenceProgramLabels.run initialLabel PhysicalControllerInitializer.program program init_slots body
  let frame : Frame ℕ 15323 := ⟨1,.r3,regs⟩
  have enter : tickNatural AdaptiveControllerProgram.program
      (AdaptiveControllerProgram.state mid regs [] tape 0)=
      some ⟨AdaptiveControllerProgram.state mid regs [frame] tape 8,[],0⟩ := rfl
  have grid : max L.size (L+1).size≤B := (le_max_right _ _).trans weightsWidth
  have width : ∀ ws∈InitialUniformTables.words n,∀ w∈ws,w.length≤B :=
    fun ws hws w hw => (InitialRetainedStateProgram.words_width n ws hws w hw).trans ((le_max_left _ _).trans weightsWidth)
  have execution := AdaptiveControllerExecution.natural_loop s positive EN E (r:=regs) params cache epochCap
    hW labelWidth epochWidth hB grid width scaleBound frame [] tape
  cases model : ControllerTapeModel.run positive E R trials restarts epochs s tape with
  | none =>
    rw [model] at execution
    obtain ⟨v,events,stop,run,short⟩ := execution
    let callFrame : Frame ℕ 26259 := ⟨26258,.r3,regs⟩
    have invoke : tickNatural program (state mid regs [] tape 7)=
        some ⟨state mid regs [callFrame] tape (controllerLabel 0),[],0⟩ := rfl
    have inner := ReferenceProgramLabels.run controllerLabel AdaptiveControllerProgram.program program controller_slots (.step enter run)
    have withCall := ReferenceProgramStack.run program [callFrame] inner
    have prefixRun := append_run prepare (NaturalRun.step invoke withCall)
    simp only [List.nil_append] at prefixRun
    exact ⟨_,events,_,prefixRun,short⟩
  | some answer =>
    rcases answer with ⟨last,rest,reads⟩
    rw [model] at execution
    obtain ⟨ex,result,v,events,nextWords,nextScale,stored,wordBound,newScale,run,controllerTime,_,count,fits⟩ := execution
    have inner : NaturalRun AdaptiveControllerProgram.program (v+1) (AdaptiveControllerProgram.state mid regs [] tape 0)
        events (AdaptiveControllerProgram.state (mid++ex) (regs.set .r3 result) [] rest 1) := .step enter run
    have invoke := ReferenceProgramInvocation.call controllerLabel controller_slots (caller:=7) (continuation:=26258)
      (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] inner
    let final := state (mid++ex) (regs.set .r3 result) [] rest 26258
    have trace : NaturalRun program (k+(v+1+2)) old events final := by
      simpa only [final,Registers.get,Registers.set,List.nil_append] using append_run prepare invoke
    have grew : mid.length≤H+setup := by
      have heapGrow := ControllerWordWidth.heap_bound prepare
      change mid.length≤heap.length+k at heapGrow
      omega
    have advance : v+1≤ AdaptiveControllerBounds.instructionBound b epochs (H+setup) := by
      change v≤loopLimit b (epochs+1) mid.length at controllerTime
      have mono : loopLimit b (epochs+1) mid.length≤loopLimit b (epochs+1) (H+setup) := by
        unfold loopLimit
        gcongr
      exact Nat.add_le_add_right (controllerTime.trans mono) 1
    have within : k+(v+1+2)≤budget := by
      change k+(v+1+2)≤ setup+AdaptiveControllerBounds.instructionBound b epochs (H+setup)+2
      have initTime : k≤ setup := time
      omega
    refine ⟨es++ex,regs.set .r3 result,k+(v+1+2),events,nextWords,nextScale,?_,?_,
      wordBound,newScale,count,fits,within⟩
    · simpa only [final,mid,old,ReferenceProgramInvocation.state,List.append_assoc] using trace
    · simpa only [Registers.set,mid,old,ReferenceProgramInvocation.state,List.append_assoc] using stored

set_option maxHeartbeats 3200000 in
theorem physical_original {n L W B S H A trials restarts epochs : ℕ} {adj : PairFlags n}
    (positive : 0<L) (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M : Bits} (initial : BitState 26259) (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (input : Input (L:=L) (eraseState initial).heap (eraseState initial).registers.a adj)
    (controls : Control (eraseState initial).heap (eraseState initial).registers.b R M trials restarts epochs)
    (hW : 1≤W) (labelWidth : n.size≤W) (epochWidth : RetainedEpochFromMasks.width n L≤W) (levelWidth : L.bits.length≤W)
    (weightsWidth : max 1 (max L.size (L+1).size)≤B) (hB : B≤W)
    (scaleBound : 1+2*restarts*(epochs+1)≤S) :
    let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
    let budget := instructionBound b epochs H
    match ControllerTapeModel.run positive E R trials restarts epochs (initialCode adj positive) initial.source with
    | none => ∀ limit paid,GuardedReferenceExecution.execute program limit initial paid=none
    | some (result,(rest,reads)) =>
      ∃ (out : BitState 26259) (paid : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
        GuardedReferenceExecution.execute program (budget+1) initial 0=some (out,paid) ∧
        Stored (eraseState out).heap (eraseState out).registers.d result positive EN E nextWords nextScale ∧
        (∀ ws∈nextWords,∀ w∈ws,w.length≤B) ∧ nextScale.length≤S ∧
        out.source=rest ∧ out.stack=[] ∧ out.pc=26258 ∧ reads≤ initial.source.length ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
        paid≤ completeBound 26259 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 26259 := by
  let old := eraseState initial
  let tape := initial.source
  let b : Limits := ⟨n,L,trials,restarts,W,B,S,R.length,M.length⟩
  let budget := instructionBound b epochs H
  have empty : old.stack=[] := by simp [old,eraseState,State.map,quiet]
  have initialAt : old=state old.heap old.registers [] tape 0 := at_entry old entry empty dense
  have heapCap : old.heap.length≤H := by
    have hh := bounded.1
    simp only [State.records] at hh
    simpa only [old,eraseState,State.map,List.length_map] using (Nat.le_add_right _ _).trans
      ((Nat.le_add_right (initial.heap.length+initial.stack.length) 1).trans hh)
  have exec := natural_original positive EN E heapCap input controls hW labelWidth epochWidth levelWidth
    weightsWidth hB scaleBound tape
  dsimp only at exec
  cases model : ControllerTapeModel.run positive E R trials restarts epochs (initialCode adj positive) tape with
  | none =>
    rw [model] at exec
    obtain ⟨k,events,stop,run,short⟩ := exec
    rw [← initialAt] at run
    obtain ⟨_,_,actual,_,_,_,_⟩ := polynomial_simulation bounded run
    exact fun limit paid => GuardedReferencePrefix.rejects_prefix actual short limit paid
  | some answer =>
    rcases answer with ⟨result,rest,reads⟩
    rw [model] at exec
    obtain ⟨ext,regs,k,events,nextWords,nextScale,run,stored,wordBound,newScale,count,fits,within⟩ := exec
    rw [← initialAt] at run
    have halt : tickNatural program (state (old.heap++ext) regs [] rest 26258)=none := rfl
    obtain ⟨q,out,actual,matchState,stopped,cost,suffix⟩ := terminating_simulation bounded run halt
    have time : k≤budget := within
    have guarded := GuardedReferenceExecution.execute_eq actual stopped (budget+1) 0 (by omega)
    rw [count,ite_eq_left fits] at guarded
    refine ⟨out,_,nextWords,nextScale,guarded,?_,wordBound,newScale,suffix,?_,?_,fits,⟨ext,?_⟩,?_⟩
    · rw [matchState]; exact stored
    · have noFrames : (eraseState out).stack=[] := by rw [matchState]; rfl
      simpa [eraseState,State.map] using noFrames
    · exact congrArg (fun st : NaturalState 26259 => st.pc) matchState
    · rw [matchState]; rfl
    · have paid := cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ time)
      have guards := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 26259) (Nat.add_le_add_right time 1)
      simpa only [Nat.zero_add] using Nat.add_le_add paid guards

end DirectedFlowCutGap.OriginalGraphControllerProgram
