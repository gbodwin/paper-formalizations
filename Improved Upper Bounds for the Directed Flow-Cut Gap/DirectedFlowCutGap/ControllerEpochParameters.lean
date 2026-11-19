import DirectedFlowCutGap.PhysicalEpochScanProgram

/-! Each epoch freezes its threshold from the current mass after stabilization. -/

namespace DirectedFlowCutGap.ControllerEpochParameters

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochScanData (Graph Stored stored_extend cacheOf)
open CandidateEnumeration (Node Network)

def trimLabel (pc : Fin 13) : Fin 118 := ⟨96+pc.val,by omega⟩
def zeroLabel (pc : Fin 9) : Fin 118 := ⟨109+pc.val,by omega⟩

def program : Program 118 := fun pc =>
  if pc.val < 96 then
    match pc.val with
    | 0 => .call 16 1 .r1
    | 1 => .call 32 2 .r2
    | 2 => .call 48 3 .r0
    | 3 => .make .r3 (.pair .r2 .r0) 4
    | 16 => .field .r0 .r3 false 17
    | 17 => .field .r0 .r0 false 18
    | 18 => .field .r0 .r0 true 19
    | 19 => .call (trimLabel 11) 20 .r3
    | 20 => .ret .r3
    | 32 => .field .r0 .r2 false 33
    | 33 => .field .r2 .r2 true 34
    | 34 => .field .r2 .r2 false 35
    | 35 => .make .r2 (.pair .r2 .r1) 36
    | 36 => .make .r2 (.pair .r0 .r2) 37
    | 37 => .ret .r2
    | 48 => .field .r0 .r3 true 49
    | 49 => .field .r0 .r0 true 50
    | 50 => .call (zeroLabel 7) 51 .r3
    | 51 => .ret .r3
    | _ => .halt
  else if h : pc.val < 109 then
    if pc.val=108 then .ret .r3 else ReferenceProgramLabels.instruction trimLabel
      (BinaryTrimProgram.program ⟨pc.val-96,by omega⟩)
  else if pc.val=117 then .ret .r3 else ReferenceProgramLabels.instruction zeroLabel
    (BinaryZeroProgram.program ⟨pc.val-109,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 118

def instructionBound (H : ℕ) : ℕ := 12*H+30

private theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases stop : pc.val=12
  · have eq : pc=12 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,trimLabel,show ¬96+pc.val<96 by omega,show 96+pc.val<109 by omega,show 96+pc.val≠108 by omega]

private theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,zeroLabel,show ¬109+pc.val<96 by omega,show ¬109+pc.val<109 by omega,show 109+pc.val≠117 by omega]

set_option maxHeartbeats 2200000 in
private theorem trim_current {heap : NaturalHeap} {r : Registers ℕ} {live packed current : ℕ} {word : Bits}
    (cache : ∃ best,heap[r.d]?=some (.pair live best)) (stateAt : ∃ run,heap[live]?=some (.pair packed run))
    (massAt : ∃ masks,heap[packed]?=some (.pair masks current)) (stored : BoolList heap current word) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=(trim word).1.length ∧
      BoolList (heap++ext) root (trim word).1 ∧
      NaturalRun program (BinaryTrimProgram.steps word+8) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  obtain ⟨best,atCache⟩ := cache
  obtain ⟨runtime,atState⟩ := stateAt
  obtain ⟨masks,atMass⟩ := massAt
  let frame : Frame ℕ 118 := ⟨1,.r1,r⟩
  let args := r.set .r0 current
  have fields : NaturalRun program 4 (state heap r [] tape 0) [] (state heap args [frame] tape 19) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atCache,atState,atMass]
  let start : NaturalState 13 := ReferenceProgramInvocation.state heap args [] tape 11
  obtain ⟨ext,root,len,raw,rep⟩ := BinaryTrimProgram.trim_high start rfl rfl stored rfl
  have body : NaturalRun BinaryTrimProgram.program (1+BinaryTrimProgram.steps word) start []
      (ReferenceProgramInvocation.state (heap++ext) (args.set .r3 root) [] tape 12) := by
    simpa only [start,ReferenceProgramInvocation.state,BinaryTrimProgram.state,Registers.set,List.length_append] using raw
  have invoke := ReferenceProgramInvocation.call trimLabel trim_slots (caller:=19) (continuation:=20)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 20
  have walk : NaturalRun program (1+BinaryTrimProgram.steps word+2) (state heap args [frame] tape 19) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,len,rep,?_⟩
  have count : 4+(1+BinaryTrimProgram.steps word+2+1)=BinaryTrimProgram.steps word+8 := by omega
  rw [← count]
  exact append_run fields (append_run walk (.step ret (.done _)))

set_option maxHeartbeats 2200000 in
private theorem replace_threshold {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {adj : PairFlags n} {R old fresh : Bits}
    (params : Parameters (L:=L) heap r.c adj R old) (word : BoolList heap r.b fresh) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=2 ∧ Parameters (L:=L) (heap++ext) root adj R fresh ∧
      NaturalRun program 7 (state heap r [] tape 1) [] (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  obtain ⟨static,gates,round,refresh,graph,cfg,pairs,shared,atParams,atStatic,atRound,atRefresh,
    ⟨ratio,oldThreshold,atGates,ratioRep,oldRep⟩,graphRep,config,labels,family⟩ := params
  let frame : Frame ℕ 118 := ⟨2,.r2,r⟩
  let args : Registers ℕ := ⟨static,r.b,ratio,r.d⟩
  let gatePair : Cell ℕ := .pair ratio r.b
  let record : Cell ℕ := .pair static heap.length
  let ext : NaturalHeap := [gatePair,record]
  have fields : NaturalRun program 4 (state heap r [] tape 1) [] (state heap args [frame] tape 35) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atParams,atGates]
  have pack : NaturalRun program 3 (state heap args [frame] tape 35) []
      (state (heap++ext) (r.set .r2 (heap.length+1)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,gatePair,record,ext,allocateNatural,Recipe.cell]
  obtain ⟨a,b,rr,rf,g,cfg',ps,ss,inst,split,rd,rs,gate,gg,cc,keys,sh⟩ :=
    parameters_extend (L:=L) (root:=r.c)
      (show Parameters (L:=L) heap r.c adj R old from ⟨static,gates,round,refresh,graph,cfg,pairs,shared,
        atParams,atStatic,atRound,atRefresh,⟨ratio,oldThreshold,atGates,ratioRep,oldRep⟩,graphRep,config,labels,family⟩) ext
  let branch := lookup_extend atParams ext
  have id : a=static := (Cell.pair.inj (Option.some.inj (inst.symm.trans branch))).1
  subst a
  exact ⟨ext,heap.length+1,rfl,⟨static,heap.length,rr,rf,g,cfg',ps,ss,
    by simp [ext,record],split,rd,rs,⟨ratio,r.b,by simp [ext,gatePair],boolList_extend ratioRep ext,
      boolList_extend word ext⟩,gg,cc,keys,sh⟩,append_run fields pack⟩

set_option maxHeartbeats 2000000 in
private theorem test_optimum {heap : NaturalHeap} {r : Registers ℕ} {best mass : ℕ} {word : Bits}
    (cache : ∃ live,heap[r.d]?=some (.pair live best)) (answer : ∃ row,heap[best]?=some (.pair row mass))
    (stored : BoolList heap mass word) (tape : Bits) :
    let cell : Cell ℕ := .flag (isZero word).1
    NaturalRun program (BinaryZeroProgram.steps word+7) (state heap r [] tape 2) []
      (state (heap++[cell]) (r.set .r0 heap.length) [] tape 3) := by
  obtain ⟨live,atCache⟩ := cache
  obtain ⟨row,atBest⟩ := answer
  let frame : Frame ℕ 118 := ⟨3,.r0,r⟩
  let args := r.set .r0 mass
  let cell : Cell ℕ := .flag (isZero word).1
  have fields : NaturalRun program 3 (state heap r [] tape 2) [] (state heap args [frame] tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atCache,atBest]
  let start : NaturalState 9 := ReferenceProgramInvocation.state heap args [] tape 7
  obtain ⟨out,run,heapEq,nextEq,aEq,bEq,cEq,dEq,stackEq,tapeEq,pcEq,_,_⟩ := BinaryZeroProgram.zero_high start rfl rfl stored rfl
  have final : out=ReferenceProgramInvocation.state (heap++[cell]) (args.set .r3 heap.length) [] tape 8 := by
    rcases out with ⟨h,n,x,s,pc,t⟩
    rcases x with ⟨a,b,c,d⟩
    simp_all [start,cell,ReferenceProgramInvocation.state,Registers.set]
  rw [final] at run
  have invoke := ReferenceProgramInvocation.call zeroLabel zero_slots (caller:=50) (continuation:=51)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] run
  let stop := state (heap++[cell]) (args.set .r3 heap.length) [frame] tape 51
  have inner : NaturalRun program (1+BinaryZeroProgram.steps word+2) (state heap args [frame] tape 50) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++[cell]) (r.set .r0 heap.length) [] tape 3,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  have count : 3+(1+BinaryZeroProgram.steps word+2+1)=BinaryZeroProgram.steps word+7 := by omega
  rw [← count]
  exact append_run fields (append_run inner (.step ret (.done _)))

theorem natural_prepare {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {R M scale : Bits} {d : Data n} {optimum : ℕ} {candidate : Family n} {words candidateWords : List (List Bits)}
    (params : Parameters (L:=L) heap r.c adj R M)
    (cache : AdaptiveControllerStorage.CacheAt heap r.d d optimum candidate words candidateWords scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root thresholdRec zeroFlag trimRoot k : ℕ) (threshold : Bits),
      (heap++ext)[root]?=some (.pair thresholdRec zeroFlag) ∧ Parameters (L:=L) (heap++ext) thresholdRec adj R threshold ∧
      (heap++ext)[zeroFlag]?=some (.flag (optimum==0)) ∧ value threshold=d.current ∧ threshold.length=d.current.size ∧
      NaturalRun program k (state heap r [] tape 0) []
        (state (heap++ext) ⟨zeroFlag,trimRoot,thresholdRec,root⟩ [] tape 4) ∧
      k≤ instructionBound heap.length ∧ ext.length=d.current.size+4 := by
  obtain ⟨live,best,atCache,⟨packed,runtime,context,scaleRoot,weights,free,atState,update,rr,rc,rt,rf,rs,sv,rd⟩,
    ⟨table,optMass,optBits,atBest,bt,br,optRep,optVal⟩⟩ := cache
  obtain ⟨masks,mass,curBits,atPacked,maskRep,curRep,curVal⟩ := update
  obtain ⟨et,trimRoot,len,trimmed,trimRun⟩ := trim_current ⟨best,atCache⟩ ⟨runtime,atState⟩ ⟨masks,atPacked⟩ curRep tape
  let mid := heap++et
  let withTrim := r.set .r1 trimRoot
  obtain ⟨ep,thresholdRec,two,thresholdParams,packRun⟩ := replace_threshold
    (r:=withTrim) (parameters_extend params et) trimmed tape
  let grown := mid++ep
  let args := withTrim.set .r2 thresholdRec
  let zeroFlag := grown.length
  let cell : Cell ℕ := .flag (isZero optBits).1
  have atCache' : grown[args.d]?=some (.pair live best) := lookup_extend (lookup_extend atCache et) ep
  have atBest' : grown[best]?=some (.pair table optMass) := lookup_extend (lookup_extend atBest et) ep
  have optRep' : BoolList grown optMass optBits := boolList_extend (boolList_extend optRep et) ep
  have test := test_optimum (r:=args) ⟨live,atCache'⟩ ⟨table,atBest'⟩ optRep' tape
  let before := grown++[cell]
  let root := before.length
  let record : Cell ℕ := .pair thresholdRec zeroFlag
  let ext := et++ep++[cell,record]
  have finish : tickNatural program (state before (args.set .r0 zeroFlag) [] tape 3)=
      some ⟨state (before++[record]) ⟨zeroFlag,trimRoot,thresholdRec,root⟩ [] tape 4,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      before,args,withTrim,root,record,allocateNatural,Recipe.cell]
  have loc : (before++[record])[root]?=some record := by simp [root]
  have spec := (isZero_spec optBits).1
  rw [optVal] at spec
  have tag : (isZero optBits).1=(optimum==0) := by
    by_cases h : optimum=0
    · simp [h,spec.mpr h]
    · have no : (isZero optBits).1=false := Bool.eq_false_iff.mpr (fun z => h (spec.mp z))
      simp [no,h]
  have initialFlag : before[zeroFlag]?=some (.flag (optimum==0)) := by simp [before,zeroFlag,cell,tag]
  have flagAt := lookup_extend initialFlag [record]
  have keep := parameters_extend (parameters_extend thresholdParams [cell]) [record]
  have ht := (trim_spec curBits).2.1.trans curVal
  have width : (trim curBits).1.length=d.current.size := by rw [trim_length,curVal]
  have trimLen := ControllerWordWidth.word_length curRep
  have zeroLen := ControllerWordWidth.word_length optRep
  have trimTime := BinaryTrimProgram.steps_bound curBits
  have zeroTime := BinaryZeroProgram.steps_bound optBits
  refine ⟨ext,root,thresholdRec,zeroFlag,trimRoot,(BinaryTrimProgram.steps curBits+8)+(7+(BinaryZeroProgram.steps optBits+7+1)),
    (trim curBits).1,?_,?_,?_,ht,width,?_,?_,?_⟩
  · simpa only [ext,mid,grown,before,record,List.append_assoc,List.cons_append,List.nil_append] using loc
  · simpa only [ext,mid,grown,before,List.append_assoc,List.cons_append,List.nil_append] using keep
  · simpa only [ext,mid,grown,before,List.append_assoc,List.cons_append,List.nil_append] using flagAt
  · simpa only [ext,mid,grown,before,zeroFlag,cell,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_add] using
      append_run trimRun (append_run packRun (append_run test (.step finish (.done _))))
  · unfold instructionBound
    omega
  · simp only [ext,List.length_append,List.length_cons,List.length_nil,two,len,width]

end DirectedFlowCutGap.ControllerEpochParameters
