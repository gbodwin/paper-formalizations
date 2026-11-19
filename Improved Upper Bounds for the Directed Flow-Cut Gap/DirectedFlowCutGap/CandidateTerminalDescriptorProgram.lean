import DirectedFlowCutGap.CandidateDescriptorCapacityProgram
import DirectedFlowCutGap.CandidateTerminalCapacityProgram

/-! Compute a terminal capacity from the actual pinned port and node. -/

namespace DirectedFlowCutGap.CandidateTerminalDescriptorProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Node Port)
open CandidateNodeListsProgram (Descriptor PortAt)
open CandidateDescriptorCapacityProgram (Context context_extend)
open CandidateShiftSelectProgram (Flags)
open CandidatePhysicalCut (capacities fuelWord numberEquiv)
open EncodedCandidateCapacity (Input)

def equalityLabel (pc : Fin 72) : Fin 269 := ⟨64+pc.val,by omega⟩
def gapLabel (pc : Fin 68) : Fin 269 := ⟨136+pc.val,by omega⟩
def terminalLabel (pc : Fin 65) : Fin 269 := ⟨204+pc.val,by omega⟩

def program : Program 269 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 20 1 .r1
    | 1 => .call 24 2 .r2
    | 2 => .field .r0 .r0 true 3
    | 3 => .make .r1 (.pair .r3 .r1) 4
    | 4 => .field .r3 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .make .r1 (.pair .r1 .r2) 7
    | 7 => .field .r2 .r2 false 8
    | 8 => .make .r3 (.pair .r3 .r2) 9
    | 9 => .field .r2 .r1 false 10
    | 10 => .make .r1 (.pair .r3 .r1) 11
    | 11 => .field .r3 .r1 true 12
    | 12 => .field .r3 .r3 true 13
    | 13 => .field .r3 .r3 true 14
    | 14 => .field .r1 .r1 false 15
    | 15 => .call (terminalLabel 0) 16 .r3
    | 20 => .field .r0 .r0 false (equalityLabel 0)
    | 24 => .call 40 25 .r1
    | 25 => .field .r1 .r1 false 26
    | 26 => .field .r2 .r2 true 27
    | 27 => .field .r2 .r2 true 28
    | 28 => .field .r2 .r2 true 29
    | 29 => .make .r3 (.pair .r1 .r2) 30
    | 30 => .ret .r3
    | 40 => .field .r0 .r0 false 41
    | 41 => .field .r2 .r2 true 42
    | 42 => .field .r1 .r2 false 43
    | 43 => .field .r2 .r2 true 44
    | 44 => .field .r2 .r2 false (gapLabel 0)
    | _ => .halt
  else if h : pc.val<136 then
    if pc.val=82 then .ret .r3
    else ReferenceProgramLabels.instruction equalityLabel (CandidatePortEqualityProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<204 then
    if pc.val=137 then .ret .r3
    else ReferenceProgramLabels.instruction gapLabel (CandidatePortGapAtProgram.program ⟨pc.val-136,by omega⟩)
  else if pc.val=209 then .ret .r3
  else ReferenceProgramLabels.instruction terminalLabel
    (CandidateTerminalCapacityProgram.program ⟨pc.val-204,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 269))
    (tape : Bits) (pc : Fin 269) : NaturalState 269 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L : ℕ) : ℕ :=
  CandidatePortEqualityProgram.instructionBound n+CandidatePortGapAtProgram.instructionBound n+4*L.size+56

private theorem equality_slots (pc : Fin 72) (h : CandidatePortEqualityProgram.program pc≠.halt) :
    program (equalityLabel pc)=ReferenceProgramLabels.instruction equalityLabel (CandidatePortEqualityProgram.program pc) := by
  by_cases hp : pc.val=18
  · have eq : pc=18 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,equalityLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<136 by omega,show 64+pc.val≠82 by omega]

private theorem gap_slots (pc : Fin 68) (h : CandidatePortGapAtProgram.program pc≠.halt) :
    program (gapLabel pc)=ReferenceProgramLabels.instruction gapLabel (CandidatePortGapAtProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,gapLabel,show ¬136+pc.val<64 by omega,show ¬136+pc.val<136 by omega,
      show 136+pc.val<204 by omega,show 136+pc.val≠137 by omega]

private theorem terminal_slots (pc : Fin 65) (h : CandidateTerminalCapacityProgram.program pc≠.halt) :
    program (terminalLabel pc)=ReferenceProgramLabels.instruction terminalLabel (CandidateTerminalCapacityProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,terminalLabel,show ¬204+pc.val<64 by omega,show ¬204+pc.val<136 by omega,
      show ¬204+pc.val<204 by omega,show 204+pc.val≠209 by omega]

private theorem pin_call {n : ℕ} {p q : Port n} {heap : NaturalHeap} {r : Registers ℕ} {h f : ℕ}
    (pair : heap[r.a]?=some (.pair h f)) (port : PortAt heap h p) (pin : PortAt heap r.b q) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (decide (p=q))) ∧
      NaturalRun program (CandidatePortEqualityProgram.steps p q+3) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  let args := r.set .r0 h
  let frame : Frame ℕ 269 := ⟨1,.r1,r⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape (equalityLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,pair,args,frame]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidatePortEqualityProgram.natural_equality (r:=args) port pin tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (equalityLabel 18)
  have lifted := ReferenceProgramLabels.run equalityLabel CandidatePortEqualityProgram.program program equality_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  let work := CandidatePortEqualityProgram.steps p q
  have run : NaturalRun program work (state heap args [frame] tape (equalityLabel 0)) [] stop := by
    simpa [state,stop,work,CandidatePortEqualityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,equalityLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 2+(work+1)=work+3 := by omega
  change NaturalRun program (work+3) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

def ActivePalette (heap : NaturalHeap) (root : ℕ) (active : Bool) (budget : Bits) : Prop :=
  ∃ flag palette,heap[root]?=some (.pair flag palette) ∧ heap[flag]?=some (.flag active) ∧
    CandidateCapacityWords.Stored heap palette budget

set_option maxHeartbeats 1000000 in
private theorem active_call {n : ℕ} {D : Input n} {p : Port n} {heap : NaturalHeap} {r : Registers ℕ}
    {grid cap budget : Bits} {h f : ℕ} (pair : heap[r.a]?=some (.pair h f)) (port : PortAt heap h p)
    (context : Context heap r.c D grid cap budget) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),ActivePalette (heap++ext) root (CandidatePortGapProgram.active D p) budget ∧
      NaturalRun program k (state heap r [] tape 1) [] (state (heap++ext) (r.set .r2 root) [] tape 2) ∧
      k ≤ CandidatePortGapAtProgram.instructionBound n+14 := by
  obtain ⟨g,resources,removed,rest,limits,palette,ctx,res,bundle,_,mask,bounds,words⟩ := context
  let args : Registers ℕ := ⟨h,removed,limits,r.d⟩
  let outer : Frame ℕ 269 := ⟨2,.r2,r⟩
  let inner : Frame ℕ 269 := ⟨25,.r1,r⟩
  have first : NaturalRun program 4 (state heap r [] tape 1) []
      (state heap ((r.set .r0 h).set .r2 resources) [inner,outer] tape 42) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,outer,inner,pair,ctx]
  have second : NaturalRun program 3 (state heap ((r.set .r0 h).set .r2 resources) [inner,outer] tape 42) []
      (state heap args [inner,outer] tape (gapLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,res,bundle]
  obtain ⟨eg,out,rep,body⟩ := CandidatePortGapAtProgram.natural_gap D (r:=args) port mask bounds tape
  let mid := heap++eg
  let stop := state mid (args.set .r3 out) [inner,outer] tape (gapLabel 1)
  have lifted := ReferenceProgramLabels.run gapLabel CandidatePortGapAtProgram.program program gap_slots body
  have lifted := ReferenceProgramStack.run program [inner,outer] lifted
  let work := CandidatePortGapProgram.steps (CandidatePortAdjacencyProgram.kind p)
    (CandidatePortAdjacencyProgram.vertex p).val.bits+4
  have run : NaturalRun program work (state heap args [inner,outer] tape (gapLabel 0)) [] stop := by
    simpa [state,stop,mid,work,CandidatePortGapAtProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state mid (r.set .r1 out) [outer] tape 25,[],0⟩ := by
    simp [state,stop,program,gapLabel,tickNatural,inner,Registers.get,Registers.set]
  obtain ⟨active,gap,entry,enabled,_⟩ := rep
  let cell : Cell ℕ := .pair active palette
  let entered := r.set .r1 out
  have hctx : mid[r.c]?=some (.pair g resources) := lookup_extend ctx eg
  have hres : mid[resources]?=some (.pair removed rest) := lookup_extend res eg
  have hbundle : mid[rest]?=some (.pair limits palette) := lookup_extend bundle eg
  have stored : mid[out]?=some (.pair active gap) := entry
  let ready : Registers ℕ := ⟨r.a,active,rest,r.d⟩
  have fields : NaturalRun program 3 (state mid entered [outer] tape 25) []
      (state mid ready [outer] tape 28) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,entered,ready,stored,hctx,hres]
  have output : NaturalRun program 3 (state mid ready [outer] tape 28) []
      (state (mid++[cell]) (r.set .r2 mid.length) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,ready,outer,hbundle,
      cell,allocateNatural,Recipe.cell]
  have finish : NaturalRun program 6 (state mid entered [outer] tape 25) []
      (state (mid++[cell]) (r.set .r2 mid.length) [] tape 2) := append_run fields output
  refine ⟨eg++[cell],mid.length,work+14,?_,?_,?_⟩
  · have y : (mid++[cell])[mid.length]?=some cell := by simp
    exact ⟨active,palette,by simpa only [mid,cell,List.append_assoc] using y,
      by simpa only [mid,List.append_assoc] using lookup_extend enabled [cell],
      CandidateCapacityWords.stored_extend words (eg++[cell])⟩
  · have count : 4+(3+(work+(6+1)))=work+14 := by omega
    rw [← count]
    simpa only [mid,entered,List.append_assoc,List.nil_append] using
      append_run first (append_run second (append_run run (.step ret finish)))
  · have limit := CandidatePortGapAtProgram.steps_le p
    omega

private theorem appended_at (heap ext : NaturalHeap) (i : ℕ) :
    (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1500000 in
private theorem terminal_args {heap : NaturalHeap} {r : Registers ℕ} {sign active side pin : Bool}
    {level budget : Bits} {port fields signRoot levelRoot : ℕ}
    (outer : heap[r.a]?=some (.pair port fields)) (inside : heap[fields]?=some (.pair signRoot levelRoot))
    (signRep : heap[signRoot]?=some (.flag sign)) (levelRep : BoolList heap levelRoot level)
    (sideRep : heap[r.d]?=some (.flag side)) (pinRep : heap[r.b]?=some (.flag pin))
    (activePalette : ActivePalette heap r.c active budget) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ),
      BoolList (heap++ext) args.a level ∧ Flags (heap++ext) args.b sign active ∧
      Flags (heap++ext) args.c side pin ∧ CandidateCapacityWords.Stored (heap++ext) args.d budget ∧
      NaturalRun program 13 (state heap r [] tape 2) [] (state (heap++ext) args [] tape 15) := by
  obtain ⟨activeRoot,palette,activePair,activeRep,words⟩ := activePalette
  let i := heap.length
  let term : Cell ℕ := .pair r.d r.b
  let ctx : Cell ℕ := .pair i r.c
  let bits : Cell ℕ := .pair signRoot activeRoot
  let both : Cell ℕ := .pair (i+2) (i+1)
  let ext : NaturalHeap := [term,ctx,bits,both]
  let args : Registers ℕ := ⟨levelRoot,i+2,i,palette⟩
  let mid := heap++[term]
  let r1 : Registers ℕ := ⟨levelRoot,i,r.c,signRoot⟩
  let prep := heap++[term,ctx]
  let r2 : Registers ℕ := ⟨levelRoot,i+1,activeRoot,signRoot⟩
  let grown := heap++ext
  let r3 : Registers ℕ := ⟨levelRoot,i+3,i,i+2⟩
  have old : mid[fields]?=some (.pair signRoot levelRoot) := lookup_extend inside [term]
  have first : NaturalRun program 4 (state heap r [] tape 2) [] (state mid r1 [] tape 6) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      outer,old,mid,r1,term,i]
  have available : (heap++[term,ctx])[r.c]?=some (.pair activeRoot palette) := lookup_extend activePair [term,ctx]
  have second : NaturalRun program 2 (state mid r1 [] tape 6) [] (state prep r2 [] tape 8) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      available,mid,prep,r1,r2,ctx,term,i,List.append_assoc]
  have third : NaturalRun program 3 (state prep r2 [] tape 8) [] (state grown r3 [] tape 11) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      grown,prep,ext,r2,r3,bits,both,ctx,term,i,List.append_assoc,Nat.add_assoc]
  have storedBoth : grown[i+3]?=some both := appended_at heap ext 3
  have storedCtx : grown[i+1]?=some ctx := appended_at heap ext 1
  have storedInput : grown[r.c]?=some (.pair activeRoot palette) := lookup_extend activePair ext
  have finish : NaturalRun program 4 (state grown r3 [] tape 11) [] (state grown args [] tape 15) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,r3,both,ctx,
      storedBoth,storedCtx,storedInput]
  refine ⟨ext,args,boolList_extend levelRep ext,
    ⟨signRoot,activeRoot,appended_at heap ext 2,lookup_extend signRep ext,lookup_extend activeRep ext⟩,
    ⟨r.d,r.b,appended_at heap ext 0,lookup_extend sideRep ext,lookup_extend pinRep ext⟩,
    CandidateCapacityWords.stored_extend words ext,?_⟩
  simpa only [grown,prep,mid,List.append_assoc,List.nil_append] using append_run first (append_run second (append_run third finish))

private theorem capacity_call {heap : NaturalHeap} {r : Registers ℕ} {level budget : Bits} {side sign active pin : Bool}
    (levels : BoolList heap r.a level) (node : Flags heap r.b sign active)
    (terms : Flags heap r.c side pin) (palette : CandidateCapacityWords.Stored heap r.d budget) (tape : Bits) :
    let fields := CandidateTerminalFlagsProgram.result side (isZero level).1 sign active pin
    ∃ (ext : NaturalHeap) (root : ℕ),BoolList (heap++ext) root (CandidateCapacityWords.word budget fields.1 fields.2) ∧
      NaturalRun program (CandidateTerminalCapacityProgram.steps level+2) (state heap r [] tape 15) []
        (state (heap++ext) (r.set .r3 root) [] tape 16) := by
  dsimp only
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateTerminalCapacityProgram.natural_capacity levels node terms palette tape
  let frame : Frame ℕ 269 := ⟨16,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 15)=some ⟨state heap r [frame] tape (terminalLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (terminalLabel 5)
  have lifted := ReferenceProgramLabels.run terminalLabel CandidateTerminalCapacityProgram.program program terminal_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (CandidateTerminalCapacityProgram.steps level)
      (state heap r [frame] tape (terminalLabel 0)) [] stop := by
    simpa [state,stop,CandidateTerminalCapacityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 16,[],0⟩ := by
    simp [state,stop,program,terminalLabel,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

theorem natural_terminal_word {n L : ℕ} {D : Input n} {a : Node n L} {pinned : Port n} {side : Bool}
    {heap : NaturalHeap} {r : Registers ℕ} {grid cap budget : Bits}
    (node : Descriptor heap r.a (.inl a)) (pin : PortAt heap r.b pinned) (sideRep : heap[r.d]?=some (.flag side))
    (context : Context heap r.c D grid cap budget) (tape : Bits) :
    let fields := CandidateTerminalFlagsProgram.result side (isZero a.2.val.bits).1 a.1.2
      (CandidatePortGapProgram.active D a.1.1) (decide (a.1.1=pinned))
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (CandidateCapacityWords.word budget fields.1 fields.2) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 16) ∧
      k ≤ instructionBound n L := by
  rcases a with ⟨⟨p,sign⟩,l⟩
  obtain ⟨port,fields,sg,lv,pair,portRep,combined,sgRep,lvRep⟩ := node
  obtain ⟨ee,point,same,compare⟩ := pin_call pair portRep pin tape
  let mid := heap++ee
  let withPin := r.set .r1 point
  obtain ⟨ea,act,k,active,readActive,readBound⟩ := active_call (r:=withPin) (lookup_extend pair ee)
    (CandidateNodeListsProgram.port_extend portRep ee) (context_extend context ee) tape
  let grown := mid++ea
  let ready := withPin.set .r2 act
  obtain ⟨ep,args,level,signs,terms,words,pack⟩ := terminal_args (r:=ready) (lookup_extend (lookup_extend pair ee) ea)
    (lookup_extend (lookup_extend combined ee) ea) (lookup_extend (lookup_extend sgRep ee) ea)
    (boolList_extend (boolList_extend lvRep ee) ea) (lookup_extend (lookup_extend sideRep ee) ea)
    (lookup_extend same ea) active tape
  obtain ⟨ec,root,rep,compute⟩ := capacity_call level signs terms words tape
  let e := CandidatePortEqualityProgram.steps p pinned
  let c := CandidateTerminalCapacityProgram.steps l.val.bits
  refine ⟨ee++ea++ep++ec,args,root,e+3+(k+(13+(c+2))),?_,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using rep
  · simpa only [grown,mid,e,c,List.append_assoc,List.nil_append] using append_run compare
      (append_run readActive (append_run pack compute))
  · have h := CandidatePortEqualityProgram.steps_le p pinned
    have w : l.val.bits.length≤L.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size (by have := l.isLt; omega)
    have bound := CandidateTerminalCapacityProgram.steps_le l.val.bits
    unfold instructionBound
    omega

theorem source_word_eq {n L : ℕ} (D : Input n) (s t : Fin n) (B : ℕ) (a : Node n L) :
    let fields := CandidateTerminalFlagsProgram.result false (isZero a.2.val.bits).1 a.1.2
      (CandidatePortGapProgram.active D a.1.1) (decide (a.1.1=TerminalPorts.sink t))
    CandidateCapacityWords.word (fuelWord D s t L B) fields.1 fields.2 =
      (capacities D s t L B (numberEquiv n L (.inr false)) (numberEquiv n L (.inl a))).bits := by
  dsimp only
  rw [CandidateTerminalFlagsProgram.result_source D s t L B a _ (value_bits _)]
  exact CandidateCapacityValues.capacity_word D s t L B (.inr false) (.inl a)

theorem sink_word_eq {n L : ℕ} (D : Input n) (s t : Fin n) (B : ℕ) (a : Node n L) :
    let fields := CandidateTerminalFlagsProgram.result true (isZero a.2.val.bits).1 a.1.2
      (CandidatePortGapProgram.active D a.1.1) (decide (a.1.1=TerminalPorts.source s))
    CandidateCapacityWords.word (fuelWord D s t L B) fields.1 fields.2 =
      (capacities D s t L B (numberEquiv n L (.inl a)) (numberEquiv n L (.inr true))).bits := by
  dsimp only
  rw [CandidateTerminalFlagsProgram.result_sink D s t L B a _ (value_bits _)]
  exact CandidateCapacityValues.capacity_word D s t L B (.inl a) (.inr true)

end DirectedFlowCutGap.CandidateTerminalDescriptorProgram
