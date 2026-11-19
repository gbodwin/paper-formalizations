import DirectedFlowCutGap.AdaptiveControllerStorage
import DirectedFlowCutGap.ControllerWordWidth

/-! Read the actual cache masses and normalize them before the ready and active tests. -/

namespace DirectedFlowCutGap.CacheGatesProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters CacheAt cache_extend parameters_extend)

def trimLabel (pc : Fin 13) : Fin 298 := ⟨48+pc.val,by omega⟩
def gatesLabel (pc : Fin 237) : Fin 298 := ⟨61+pc.val,by omega⟩

def program : Program 298 := fun pc =>
  if pc.val<48 then
    match pc.val with
    | 0 => .call 16 1 .r0
    | 1 => .call 24 2 .r1
    | 2 => .field .r2 .r2 true 3
    | 3 => .call (gatesLabel 0) 4 .r3
    | 16 => .field .r0 .r3 false 17
    | 17 => .field .r0 .r0 false 18
    | 18 => .field .r0 .r0 true 19
    | 19 => .call (trimLabel 11) 20 .r3
    | 20 => .ret .r3
    | 24 => .field .r0 .r3 true 25
    | 25 => .field .r0 .r0 true 26
    | 26 => .call (trimLabel 11) 27 .r3
    | 27 => .ret .r3
    | _ => .halt
  else if h : pc.val<61 then
    if pc.val=60 then .ret .r3
    else ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program ⟨pc.val-48,by omega⟩)
  else if pc.val=68 then .ret .r3
  else ReferenceProgramLabels.instruction gatesLabel
    (AdaptiveGatesProgram.program ⟨pc.val-61,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 298

def Output (heap : NaturalHeap) (root current optimum : ℕ) (R M : Bits) : Prop :=
  ∃ ready active,heap[root]?=some (.pair ready active) ∧
    heap[ready]?=some (.flag (FlexibleGridProvider.readyCode (value R) current optimum)) ∧
    heap[active]?=some (.flag (FlexibleGridProvider.readyCode (value R) current optimum &&
      !(optimum == 0) && Nat.ble (value M) (value R*current)))

def allocationBound (current optimum ratio threshold : ℕ) : ℕ :=
  current+optimum+AdaptiveGatesProgram.instructionBound current optimum ratio threshold

def instructionBound (heapSize current optimum ratio threshold : ℕ) : ℕ :=
  16*heapSize+AdaptiveGatesProgram.instructionBound current optimum ratio threshold+24

private theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases stop : pc.val=12
  · have eq : pc=12 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,trimLabel,show ¬48+pc.val<48 by omega,show 48+pc.val<61 by omega,show 48+pc.val≠60 by omega]

private theorem gate_slots (pc : Fin 237) (h : AdaptiveGatesProgram.program pc≠.halt) :
    program (gatesLabel pc)=ReferenceProgramLabels.instruction gatesLabel (AdaptiveGatesProgram.program pc) := by
  by_cases stop : pc.val=7
  · have eq : pc=7 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,gatesLabel,show ¬61+pc.val<48 by omega,show ¬61+pc.val<61 by omega,show 61+pc.val≠68 by omega]

set_option maxHeartbeats 1700000 in
private theorem trim_call {heap : NaturalHeap} {r : Registers ℕ} {live best packed current optimum table : ℕ}
    {runtime masks : ℕ} {word : Bits} (optimal : Bool) (destination : Reg) (dest : destination=(if optimal then .r1 else .r0))
    (cacheRead : heap[r.d]?=some (.pair live best)) (stateRead : heap[live]?=some (.pair packed runtime))
    (currentRead : heap[packed]?=some (.pair masks current)) (candidateRead : heap[best]?=some (.pair table optimum))
    (stored : BoolList heap (if optimal then optimum else current) word) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=(value word).size ∧ BoolList (heap++ext) root (trim word).1 ∧
      NaturalRun program (BinaryTrimProgram.steps word+(if optimal then 7 else 8))
        (state heap r [] tape (if optimal then 1 else 0)) []
        (state (heap++ext) (r.set destination root) [] tape (if optimal then 2 else 1)) := by
  let start : Fin 298 := if optimal then 1 else 0
  let exit : Fin 298 := if optimal then 2 else 1
  let callSite : Fin 298 := if optimal then 26 else 19
  let retSite : Fin 298 := if optimal then 27 else 20
  let args := r.set .r0 (if optimal then optimum else current)
  let frame : Frame ℕ 298 := ⟨exit,destination,r⟩
  have prep : NaturalRun program (if optimal then 3 else 4) (state heap r [] tape start) []
      (state heap args [frame] tape callSite) := by
    cases optimal
    · apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        start,exit,callSite,dest,args,frame,cacheRead,stateRead,currentRead]
    · apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        start,exit,callSite,dest,args,frame,cacheRead,candidateRead]
  let sub : NaturalState 13 := ReferenceProgramInvocation.state heap args [] tape 11
  obtain ⟨ext,root,len,trimBody,rep⟩ := BinaryTrimProgram.trim_high sub rfl rfl stored rfl
  have body : NaturalRun BinaryTrimProgram.program (1+BinaryTrimProgram.steps word)
      (ReferenceProgramInvocation.state heap args [] tape 11) []
      (ReferenceProgramInvocation.state (heap++ext) (args.set .r3 root) [] tape 12) := by
    cases r
    simpa [sub,ReferenceProgramInvocation.state,BinaryTrimProgram.state,args,Registers.set] using trimBody
  have link : program callSite=.call (trimLabel 11) retSite .r3 := by cases optimal <;> rfl
  have invoke := ReferenceProgramInvocation.call trimLabel trim_slots (result:=.r3) (dst:=.r3) link (by rfl) [frame] body
  let done := state (heap++ext) (args.set .r3 root) [frame] tape retSite
  have work : NaturalRun program (1+BinaryTrimProgram.steps word+2) (state heap args [frame] tape callSite) [] done := by
    simpa only [done,Registers.get,Registers.set] using invoke
  have ret : tickNatural program done=some ⟨state (heap++ext) (r.set destination root) [] tape exit,[],0⟩ := by
    cases optimal <;> simp [done,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,retSite,frame]
  refine ⟨ext,root,len.trans (trim_length word),rep,?_⟩
  have count : (if optimal then 3 else 4)+(1+BinaryTrimProgram.steps word+2+1)=
      BinaryTrimProgram.steps word+(if optimal then 7 else 8) := by cases optimal <;> simp <;> omega
  rw [← count]
  exact append_run prep (append_run work (.step ret (.done _)))

set_option maxHeartbeats 2100000 in
theorem natural_cache_gates {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n} {R M scale : Bits}
    {d : Data n} {optimum : ℕ} {candidate : Family n} {currentWords candidateWords : List (List Bits)}
    (params : Parameters (L:=L) heap r.c adj R M)
    (cache : CacheAt heap r.d d optimum candidate currentWords candidateWords scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),Output (heap++ext) root d.current optimum R M ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound heap.length d.current.size optimum.size R.length M.length ∧
      ext.length ≤ allocationBound d.current.size optimum.size R.length M.length := by
  obtain ⟨live,best,cacheRead,⟨packed,runtime,context,si,weights,free,stateRead,updated,rr,rc,rt,rf,rs,rv,rd⟩,
    ⟨table,opt,optBits,bestRead,tableRep,od,optRep,optValue⟩⟩ := cache
  obtain ⟨masks,current,curBits,currentRead,maskRep,curRep,curValue⟩ := updated
  obtain ⟨ec,cr,clen,curStored,curRun⟩ := trim_call (r:=r) false .r0 rfl cacheRead stateRead currentRead bestRead curRep tape
  let mid := heap++ec
  let withCur := r.set .r0 cr
  obtain ⟨eo,op,olen,optStored,optRun⟩ := trim_call (r:=withCur) true .r1 rfl
    (lookup_extend cacheRead ec) (lookup_extend stateRead ec) (lookup_extend currentRead ec) (lookup_extend bestRead ec)
    (boolList_extend optRep ec) tape
  let grown := mid++eo
  let ready := withCur.set .r1 op
  obtain ⟨static,gates,round,refresh,graph,config,pairs,shared,atConfig,atStatic,atRound,atRefresh,gatesRep,
    graphRep,configRep,keys,solver⟩ := parameters_extend (parameters_extend params ec) eo
  let args := ready.set .r2 gates
  have conf : (heap++(ec++eo))[r.c]?=some (.pair static gates) := by simpa only [List.append_assoc] using atConfig
  have move : tickNatural program (state grown ready [] tape 2)=some ⟨state grown args [] tape 3,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,conf,ready,withCur,args,grown,mid]
  obtain ⟨eg,out,root,k,gatesAt,body,within⟩ := AdaptiveGatesProgram.natural_gates (r:=args)
    (boolList_extend curStored eo) optStored gatesRep tape
  have invoke := ReferenceProgramInvocation.call gatesLabel gate_slots (caller:=3) (continuation:=4)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] body
  have gateRun : NaturalRun program (k+2) (state grown args [] tape 3) []
      (state (grown++eg) (args.set .r3 root) [] tape 4) := by
    simpa only [Registers.get,Registers.set,grown,mid] using invoke
  have extraGate : eg.length≤k := ControllerWordWidth.extension_bound body rfl
  have curScan := (BinaryTrimProgram.steps_bound curBits).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 8 (Nat.le_of_succ_le (ControllerWordWidth.word_length curRep))) 3)
  have optScan := (BinaryTrimProgram.steps_bound optBits).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 8 (Nat.le_of_succ_le (ControllerWordWidth.word_length optRep))) 3)
  rw [trim_length,trim_length,curValue,optValue] at within
  rw [curValue] at clen
  rw [optValue] at olen
  refine ⟨ec++eo++eg,args,root,(BinaryTrimProgram.steps curBits+8)+(BinaryTrimProgram.steps optBits+7+(k+2+1)),?_,?_,?_,?_⟩
  · obtain ⟨yes,active,pair,readyFlag,activeFlag⟩ := gatesAt
    refine ⟨yes,active,?_,?_,?_⟩
    · simpa only [grown,mid,List.append_assoc] using pair
    · simpa only [AdaptiveGatesProgram.ready,(trim_spec curBits).2.1,(trim_spec optBits).2.1,
        curValue,optValue,grown,mid,List.append_assoc] using readyFlag
    · simpa only [AdaptiveGatesProgram.active,AdaptiveGatesProgram.ready,(trim_spec curBits).2.1,(trim_spec optBits).2.1,
        curValue,optValue,grown,mid,List.append_assoc] using activeFlag
  · simpa only [grown,mid,ready,withCur,List.append_assoc,List.nil_append,Bool.false_eq_true,ite_false,ite_true] using
      append_run curRun (append_run optRun (.step move gateRun))
  · unfold instructionBound
    omega
  · simp only [List.length_append,allocationBound]
    omega

end DirectedFlowCutGap.CacheGatesProgram
