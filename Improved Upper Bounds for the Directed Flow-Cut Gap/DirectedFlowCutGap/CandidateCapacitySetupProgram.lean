import DirectedFlowCutGap.CandidateCapacityCellProgram
import DirectedFlowCutGap.CandidateBudgetProgram

/-! Prepare the capacity operands from the graph and scalar input words. -/

namespace DirectedFlowCutGap.CandidateCapacitySetupProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateNodeListsProgram (PortAt)
open CandidatePortAdjacencyProgram (rows)
open CandidatePhysicalCut (fuelWord budgetCap)
open CandidateDescriptorCapacityProgram (Context)
open CandidateCapacityCellProgram (Inputs)
open EncodedCandidateCapacity (Input)

def Parameters {n : ℕ} (heap : NaturalHeap) (root : ℕ) (bound : Bits) (s t : Fin n) : Prop :=
  ∃ cap pins source sink,heap[root]?=some (.pair cap pins) ∧ heap[pins]?=some (.pair source sink) ∧
    BoolList heap cap bound ∧ BoolList heap source s.val.bits ∧ BoolList heap sink t.val.bits

theorem parameters_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {bound : Bits} {s t : Fin n}
    (stored : Parameters heap root bound s t) (ext : NaturalHeap) : Parameters (heap++ext) root bound s t := by
  obtain ⟨c,p,u,v,pair,pins,cap,source,sink⟩ := stored
  exact ⟨c,p,u,v,lookup_extend pair ext,lookup_extend pins ext,boolList_extend cap ext,
    boolList_extend source ext,boolList_extend sink ext⟩

def budgetLabel (pc : Fin 157) : Fin 309 := ⟨64+pc.val,by omega⟩
def wordsLabel (pc : Fin 32) : Fin 309 := ⟨221+pc.val,by omega⟩
def minLabel (pc : Fin 56) : Fin 309 := ⟨253+pc.val,by omega⟩

def program : Program 309 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 16 1 .r1
    | 1 => .call 32 2 .r2
    | 2 => .call 48 3 .r3
    | 3 => .make .r3 (.pair .r2 .r3) 4
    | 16 => .field .r0 .r2 false 17
    | 17 => .field .r1 .r2 true 18
    | 18 => .call (budgetLabel 0) 19 .r0
    | 19 => .call (wordsLabel 0) 20 .r3
    | 20 => .ret .r3
    | 32 => .call 36 33 .r3
    | 33 => .call 42 34 .r3
    | 34 => .make .r3 (.pair .r3 .r1) 35
    | 35 => .field .r2 .r2 false 38
    | 36 => .field .r0 .r2 true 37
    | 37 => .field .r1 .r3 false (minLabel 0)
    | 38 => .make .r3 (.pair .r2 .r3) 39
    | 39 => .make .r3 (.pair .r0 .r3) 40
    | 40 => .ret .r3
    | 42 => .field .r2 .r2 true 43
    | 43 => .make .r3 (.pair .r2 .r3) 44
    | 44 => .ret .r3
    | 48 => .field .r3 .r3 true 49
    | 49 => .field .r0 .r3 false 50
    | 50 => .make .r1 (.flag false) 51
    | 51 => .make .r0 (.pair .r1 .r0) 52
    | 52 => .field .r3 .r3 true 53
    | 53 => .make .r1 (.flag true) 54
    | 54 => .make .r3 (.pair .r1 .r3) 55
    | 55 => .make .r3 (.pair .r0 .r3) 56
    | 56 => .ret .r3
    | _ => .halt
  else if h : pc.val<221 then
    if pc.val=69 then .ret .r3
    else ReferenceProgramLabels.instruction budgetLabel (CandidateBudgetProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<253 then
    if pc.val=230 then .ret .r3
    else ReferenceProgramLabels.instruction wordsLabel (CandidateCapacityWords.program ⟨pc.val-221,by omega⟩)
  else if pc.val=257 then .ret .r3
  else ReferenceProgramLabels.instruction minLabel
    (BinaryMinimumWordProgram.program ⟨pc.val-253,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 309))
    (tape : Bits) (pc : Fin 309) : NaturalState 309 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L gridWidth boundWidth : ℕ) : ℕ :=
  CandidateBudgetProgram.instructionBound n gridWidth+16*(budgetCap n L).size+
    16*(gridWidth+boundWidth+1)+67

private theorem budget_slots (pc : Fin 157) (h : CandidateBudgetProgram.program pc≠.halt) :
    program (budgetLabel pc)=ReferenceProgramLabels.instruction budgetLabel (CandidateBudgetProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,budgetLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<221 by omega,show 64+pc.val≠69 by omega]

private theorem words_slots (pc : Fin 32) (h : CandidateCapacityWords.program pc≠.halt) :
    program (wordsLabel pc)=ReferenceProgramLabels.instruction wordsLabel (CandidateCapacityWords.program pc) := by
  by_cases hp : pc.val=9
  · have eq : pc=9 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,wordsLabel,show ¬221+pc.val<64 by omega,show ¬221+pc.val<221 by omega,
      show 221+pc.val<253 by omega,show 221+pc.val≠230 by omega]

private theorem min_slots (pc : Fin 56) (h : BinaryMinimumWordProgram.program pc≠.halt) :
    program (minLabel pc)=ReferenceProgramLabels.instruction minLabel (BinaryMinimumWordProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,minLabel,show ¬253+pc.val<64 by omega,show ¬253+pc.val<221 by omega,
      show ¬253+pc.val<253 by omega,show 253+pc.val≠257 by omega]

private theorem calculate_budget {heap : NaturalHeap} {r : Registers ℕ} {flags grid : Bits} {removal scale : ℕ}
    (input : heap[r.c]?=some (.pair removal scale)) (mask : BoolList heap removal flags)
    (word : BoolList heap scale grid) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (CandidateBudgetProgram.result flags grid) ∧
      NaturalRun program (CandidateBudgetProgram.steps flags grid+5) (state heap r [] tape 0) []
        (state (heap++ext) (((r.set .r0 removal).set .r1 scale).set .r0 root) [⟨1,.r1,r⟩] tape 19) := by
  let args := (r.set .r0 removal).set .r1 scale
  let outer : Frame ℕ 309 := ⟨1,.r1,r⟩
  let inner : Frame ℕ 309 := ⟨19,.r0,args⟩
  have prep : NaturalRun program 4 (state heap r [] tape 0) [] (state heap args [inner,outer] tape (budgetLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,outer,inner,input]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateBudgetProgram.natural_budget (r:=args) mask word tape
  let stop := state (heap++ext) (regs.set .r3 root) [inner,outer] tape (budgetLabel 5)
  have lifted := ReferenceProgramLabels.run budgetLabel CandidateBudgetProgram.program program budget_slots body
  have lifted := ReferenceProgramStack.run program [inner,outer] lifted
  let work := CandidateBudgetProgram.steps flags grid
  have run : NaturalRun program work (state heap args [inner,outer] tape (budgetLabel 0)) [] stop := by
    simpa [state,stop,work,CandidateBudgetProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (args.set .r0 root) [outer] tape 19,[],0⟩ := by
    simp [state,stop,program,budgetLabel,tickNatural,inner,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 4+(work+1)=work+5 := by omega
  change NaturalRun program (work+5) _ [] _
  rw [← count]
  exact append_run prep (append_run run (.step ret (.done _)))

private theorem make_words {heap : NaturalHeap} {r : Registers ℕ} {budget : Bits}
    (input : BoolList heap r.a budget) (caller : Frame ℕ 309) (tape : Bits) :
    ∃ ext root,CandidateCapacityWords.Stored (heap++ext) root budget ∧
      NaturalRun program (CandidateCapacityWords.steps budget+3) (state heap r [caller] tape 19) []
        (state (heap++ext) (caller.saved.set caller.destination root) [] tape caller.continuation) := by
  let inner : Frame ℕ 309 := ⟨20,.r3,r⟩
  have enter : tickNatural program (state heap r [caller] tape 19)=
      some ⟨state heap r [inner,caller] tape (wordsLabel 0),[],0⟩ := rfl
  obtain ⟨ext,args,root,rep,body⟩ := CandidateCapacityWords.natural_make input tape
  let stop := state (heap++ext) (args.set .r3 root) [inner,caller] tape (wordsLabel 9)
  have lifted := ReferenceProgramLabels.run wordsLabel CandidateCapacityWords.program program words_slots body
  have lifted := ReferenceProgramStack.run program [inner,caller] lifted
  have run : NaturalRun program (CandidateCapacityWords.steps budget) (state heap r [inner,caller] tape (wordsLabel 0)) [] stop := by
    simpa [state,stop,CandidateCapacityWords.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : NaturalRun program 2 stop []
      (state (heap++ext) (caller.saved.set caller.destination root) [] tape caller.continuation) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,stop,state,program,wordsLabel,tickNatural,inner,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  simpa only [List.nil_append,Nat.add_assoc,Nat.add_comm 1] using NaturalRun.step enter (append_run run ret)

private theorem minimum_call {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits} {removal scale cap pins : ℕ}
    (input : heap[r.c]?=some (.pair removal scale)) (parameters : heap[r.d]?=some (.pair cap pins))
    (gridRep : BoolList heap scale grid) (boundRep : BoolList heap cap bound) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (BinaryMinimumWordProgram.word grid bound) ∧
      NaturalRun program (BinaryMinimumWordProgram.steps grid bound+5) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r3 root) [⟨2,.r2,r⟩] tape 33) := by
  let args := (r.set .r0 scale).set .r1 cap
  let outer : Frame ℕ 309 := ⟨2,.r2,r⟩
  let inner : Frame ℕ 309 := ⟨33,.r3,r⟩
  have prep : NaturalRun program 4 (state heap r [] tape 1) [] (state heap args [inner,outer] tape (minLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,outer,inner,input,parameters]
  obtain ⟨ext,root,rep,body⟩ := BinaryMinimumWordProgram.natural_minimum (r:=args) gridRep boundRep tape
  let stop := state (heap++ext) (args.set .r3 root) [inner,outer] tape (minLabel 4)
  have lifted := ReferenceProgramLabels.run minLabel BinaryMinimumWordProgram.program program min_slots body
  have lifted := ReferenceProgramStack.run program [inner,outer] lifted
  have run : NaturalRun program (BinaryMinimumWordProgram.steps grid bound) (state heap args [inner,outer] tape (minLabel 0)) [] stop := by
    simpa [state,stop,BinaryMinimumWordProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [outer] tape 33,[],0⟩ := by
    simp [state,stop,program,minLabel,tickNatural,inner,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 4+(BinaryMinimumWordProgram.steps grid bound+1)=BinaryMinimumWordProgram.steps grid bound+5 := by omega
  rw [← count]
  exact append_run prep (append_run run (.step ret (.done _)))

private theorem appended_at (heap ext : NaturalHeap) (i : ℕ) :
    (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1400000 in
private theorem pack_context {n : ℕ} {D : Input n} {heap : NaturalHeap} {r : Registers ℕ}
    {grid cap budget : Bits} {removal scale minRoot : ℕ}
    (input : heap[r.c]?=some (.pair removal scale)) (graph : GraphAdjacencyProgram.Matrix heap r.a (rows D))
    (mask : BoolList heap removal D.removed.toList) (word : BoolList heap scale grid)
    (minimum : BoolList heap minRoot cap) (palette : CandidateCapacityWords.Stored heap r.b budget) (tape : Bits) :
    ∃ ext root,Context (heap++ext) root D grid cap budget ∧
      NaturalRun program 9 (state heap (r.set .r3 minRoot) [⟨2,.r2,r⟩] tape 33) []
        (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  let i := heap.length
  let bounds : Cell ℕ := .pair scale minRoot
  let data : Cell ℕ := .pair i r.b
  let resources : Cell ℕ := .pair removal (i+1)
  let top : Cell ℕ := .pair r.a (i+2)
  let ext : NaturalHeap := [bounds,data,resources,top]
  let frame : Frame ℕ 309 := ⟨2,.r2,r⟩
  let args := r.set .r3 minRoot
  have first : NaturalRun program 4 (state heap args [frame] tape 33) []
      (state (heap++[bounds]) (r.set .r3 i) [frame] tape 34) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
      Recipe.cell,bounds,input,i,frame,args]
  have original : (heap++[bounds,data])[r.c]?=some (.pair removal scale) := lookup_extend input _
  have second : NaturalRun program 2 (state (heap++[bounds]) (r.set .r3 i) [frame] tape 34) []
      (state (heap++[bounds,data]) ((r.set .r3 (i+1)).set .r2 removal) [frame] tape 38) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
      Recipe.cell,i,data,original,List.append_assoc]
  have last : NaturalRun program 3
      (state (heap++[bounds,data]) ((r.set .r3 (i+1)).set .r2 removal) [frame] tape 38) []
      (state (heap++ext) (r.set .r2 (i+3)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
      Recipe.cell,i,ext,resources,top,frame,List.append_assoc,Nat.add_assoc]
  refine ⟨ext,i+3,⟨r.a,i+2,removal,i+1,i,r.b,appended_at heap ext 3,appended_at heap ext 2,
    appended_at heap ext 1,GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend mask ext,
    ⟨scale,minRoot,appended_at heap ext 0,boolList_extend word ext,boolList_extend minimum ext⟩,
    CandidateCapacityWords.stored_extend palette ext⟩,append_run first (append_run second last)⟩

def Pins {n : ℕ} (heap : NaturalHeap) (root : ℕ) (s t : Fin n) : Prop :=
  ∃ source sink,heap[root]?=some (.pair source sink) ∧ PortAt heap source (TerminalPorts.source s) ∧
    PortAt heap sink (TerminalPorts.sink t)

set_option maxHeartbeats 1400000 in
private theorem pack_pins {n : ℕ} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ} {bound : Bits}
    (input : Parameters heap r.d bound s t) (tape : Bits) :
    ∃ ext root,Pins (heap++ext) root s t ∧
      NaturalRun program 10 (state heap r [] tape 2) [] (state (heap++ext) (r.set .r3 root) [] tape 3) := by
  obtain ⟨cap,pins,u,v,pair,endpoints,_,source,sink⟩ := input
  let i := heap.length
  let a : Cell ℕ := .flag false
  let b : Cell ℕ := .pair i u
  let c : Cell ℕ := .flag true
  let d : Cell ℕ := .pair (i+2) v
  let e : Cell ℕ := .pair (i+1) (i+3)
  let ext : NaturalHeap := [a,b,c,d,e]
  let frame : Frame ℕ 309 := ⟨3,.r3,r⟩
  let mid := heap++[a,b]
  let args : Registers ℕ := ⟨i+1,i,r.c,pins⟩
  have first : NaturalRun program 5 (state heap r [] tape 2) [] (state mid args [frame] tape 52) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
      Recipe.cell,i,a,b,pair,endpoints,mid,args,frame,List.append_assoc]
  have old : mid[pins]?=some (.pair u v) := lookup_extend endpoints _
  have last : NaturalRun program 5 (state mid args [frame] tape 52) []
      (state (heap++ext) (r.set .r3 (i+4)) [] tape 3) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,
      Recipe.cell,i,c,d,e,old,mid,args,frame,ext,List.append_assoc,Nat.add_assoc]
  refine ⟨ext,i+4,⟨i+1,i+3,appended_at heap ext 4,⟨i,u,appended_at heap ext 1,appended_at heap ext 0,boolList_extend source ext⟩,
    ⟨i+2,v,appended_at heap ext 3,appended_at heap ext 2,boolList_extend sink ext⟩⟩,append_run first last⟩

theorem natural_setup {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap}
    {r : Registers ℕ} {grid bound : Bits} {removal scale : ℕ}
    (graph : GraphAdjacencyProgram.Matrix heap r.a (rows D))
    (input : heap[r.c]?=some (.pair removal scale)) (mask : BoolList heap removal D.removed.toList)
    (word : BoolList heap scale grid) (numeric : value grid=L) (parameters : Parameters heap r.d bound s t) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),Inputs (heap++ext) root D s t L B grid bound ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound n L grid.length bound.length := by
  obtain ⟨eb,b,stored,budgetRun⟩ := calculate_budget input mask word tape
  have exactBudget : CandidateBudgetProgram.result D.removed.toList grid=fuelWord D s t L B := by
    rw [CandidateBudgetProgram.result_eq,numeric,fuelWord,CandidateBudgetData.budget_exact]
  rw [exactBudget] at stored
  let hb := heap++eb
  let args := ((r.set .r0 removal).set .r1 scale).set .r0 b
  let caller : Frame ℕ 309 := ⟨1,.r1,r⟩
  obtain ⟨ew,palette,words,wordRun⟩ := make_words (r:=args) stored caller tape
  let hw := hb++ew
  let ready := r.set .r1 palette
  have params : Parameters hw ready.d bound s t := parameters_extend (parameters_extend parameters eb) ew
  obtain ⟨cap,pins,u,v,paramPair,endpoints,capRep,sRep,tRep⟩ := params
  have inputReady : hw[ready.c]?=some (.pair removal scale) := lookup_extend (lookup_extend input eb) ew
  have gridReady : BoolList hw scale grid := boolList_extend (boolList_extend word eb) ew
  obtain ⟨em,m,minimum,minRun⟩ := minimum_call (r:=ready) inputReady paramPair gridReady capRep tape
  let hm := hw++em
  obtain ⟨ec,core,context,contextRun⟩ := pack_context (r:=ready) (lookup_extend inputReady em)
    (GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend graph eb) ew) em)
    (boolList_extend (boolList_extend (boolList_extend mask eb) ew) em) (boolList_extend gridReady em)
    minimum (CandidateCapacityWords.stored_extend words em) tape
  let hc := hm++ec
  let withCore := ready.set .r2 core
  have rawParams : Parameters hw ready.d bound s t := ⟨cap,pins,u,v,paramPair,endpoints,capRep,sRep,tRep⟩
  obtain ⟨ep,pinned,pinContext,pinRun⟩ := pack_pins (r:=withCore)
    (parameters_extend (parameters_extend rawParams em) ec) tape
  let hp := hc++ep
  let out := withCore.set .r3 pinned
  let final : Cell ℕ := .pair core pinned
  have done : NaturalRun program 1 (state hp out [] tape 3) []
      (state (hp++[final]) (out.set .r3 hp.length) [] tape 4) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,out,withCore,final,
      allocateNatural,Recipe.cell]
  obtain ⟨p,q,pinPair,sp,tp⟩ := pinContext
  have answer : Inputs (hp++[final]) hp.length D s t L B grid bound :=
    ⟨core,pinned,p,q,by simp [final],lookup_extend pinPair [final],CandidateNodeListsProgram.port_extend sp [final],
      CandidateNodeListsProgram.port_extend tp [final],CandidateDescriptorCapacityProgram.context_extend
        (CandidateDescriptorCapacityProgram.context_extend context ep) [final]⟩
  let a := CandidateBudgetProgram.steps D.removed.toList grid
  let b := CandidateCapacityWords.steps (fuelWord D s t L B)
  let c := BinaryMinimumWordProgram.steps grid bound
  refine ⟨eb++ew++em++ec++ep++[final],out,hp.length,a+5+(b+3+(c+5+(9+(10+1)))),?_,?_,?_⟩
  · simpa only [hb,hw,hm,hc,hp,List.append_assoc] using answer
  · simpa only [hb,hw,hm,hc,hp,a,b,c,caller,List.append_assoc,List.nil_append] using
      append_run budgetRun (append_run wordRun (append_run minRun (append_run contextRun (append_run pinRun done))))
  · have costBudget := CandidateBudgetProgram.steps_le D.removed.toList grid
    rw [Vector.length_toList] at costBudget
    have costWords := CandidateCapacityWords.steps_le (fuelWord D s t L B)
    have wager : (fuelWord D s t L B).length ≤ (budgetCap n L).size := by
      rw [fuelWord,Nat.size_eq_bits_len]
      apply Nat.size_le_size
      simpa only [CandidatePhysicalCut.problem,Fintype.card_fin] using
        CandidateClosureProvider.candidate_budget_le D.graph s t D.cut L B
    have compare := BinaryComparisonProgram.steps_bound grid bound
    unfold instructionBound a b c BinaryMinimumWordProgram.steps
    omega

end DirectedFlowCutGap.CandidateCapacitySetupProgram
