import DirectedFlowCutGap.CandidateTerminalDescriptorProgram

/-! Select the exact capacity case using the two stored network tags. -/

namespace DirectedFlowCutGap.CandidateCapacityCellProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Node Network Port)
open CandidateNodeListsProgram (Descriptor PortAt port_extend)
open CandidatePhysicalCut (capacities numberEquiv fuelWord)
open EncodedCandidateCapacity (Input)

def Inputs {n : ℕ} (heap : NaturalHeap) (root : ℕ) (D : Input n) (s t : Fin n) (L B : ℕ) (grid bound : Bits) : Prop :=
  ∃ core pins start finish,heap[root]?=some (.pair core pins) ∧ heap[pins]?=some (.pair start finish) ∧
    PortAt heap start (TerminalPorts.source s) ∧ PortAt heap finish (TerminalPorts.sink t) ∧
    CandidateDescriptorCapacityProgram.Context heap core D grid (BinaryMinimumWordProgram.word grid bound) (fuelWord D s t L B)

theorem inputs_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {s t : Fin n} {L B : ℕ} {grid bound : Bits}
    (input : Inputs heap root D s t L B grid bound) (ext : NaturalHeap) : Inputs (heap++ext) root D s t L B grid bound := by
  obtain ⟨core,pins,start,finish,entry,pair,sp,tp,context⟩ := input
  exact ⟨core,pins,start,finish,lookup_extend entry ext,lookup_extend pair ext,port_extend sp ext,port_extend tp ext,
    CandidateDescriptorCapacityProgram.context_extend context ext⟩

def coreLabel (pc : Fin 576) : Fin 877 := ⟨32+pc.val,by omega⟩
def termLabel (pc : Fin 269) : Fin 877 := ⟨608+pc.val,by omega⟩

def program : Program 877 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .branch .r0 31 8 5 1
    | 1 => .branch .r1 31 5 16 12
    | 5 => .make .r3 .nil 28
    | 8 => .branch .r1 31 5 5 20
    | 12 => .call 13 28 .r3
    | 13 => .field .r2 .r2 false (coreLabel 0)
    | 16 => .call 17 28 .r3
    | 17 => .move .r3 .r1 18
    | 18 => .field .r1 .r2 true 19
    | 19 => .field .r1 .r1 false 24
    | 20 => .call 21 28 .r3
    | 21 => .move .r3 .r0 22
    | 22 => .move .r0 .r1 23
    | 23 => .field .r1 .r2 true 25
    | 24 => .field .r2 .r2 false (termLabel 0)
    | 25 => .field .r1 .r1 true 24
    | _ => .halt
  else if h : pc.val<608 then
    if pc.val=45 then .ret .r3
    else ReferenceProgramLabels.instruction coreLabel
      (CandidateDescriptorCapacityProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=624 then .ret .r3
  else ReferenceProgramLabels.instruction termLabel
    (CandidateTerminalDescriptorProgram.program ⟨pc.val-608,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 877))
    (tape : Bits) (pc : Fin 877) : NaturalState 877 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L gridWidth boundWidth : ℕ) : ℕ :=
  max (CandidateDescriptorCapacityProgram.instructionBound n L gridWidth boundWidth)
    (CandidateTerminalDescriptorProgram.instructionBound n L)+9

private theorem core_slots (pc : Fin 576) (h : CandidateDescriptorCapacityProgram.program pc≠.halt) :
    program (coreLabel pc)=ReferenceProgramLabels.instruction coreLabel (CandidateDescriptorCapacityProgram.program pc) := by
  by_cases hp : pc.val=13
  · have eq : pc=13 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,coreLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<608 by omega,show 32+pc.val≠45 by omega]

private theorem term_slots (pc : Fin 269) (h : CandidateTerminalDescriptorProgram.program pc≠.halt) :
    program (termLabel pc)=ReferenceProgramLabels.instruction termLabel (CandidateTerminalDescriptorProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,termLabel,show ¬608+pc.val<32 by omega,show ¬608+pc.val<608 by omega,show 608+pc.val≠624 by omega]

def next {n L : ℕ} : Network n L → Network n L → Fin 877
  | .inl _,.inl _ => 12
  | .inl _,.inr true => 16
  | .inr false,.inl _ => 20
  | _,_ => 5

def dispatchSteps {n L : ℕ} (a : Network n L) : ℕ := if a=.inr true then 1 else 2

private theorem dispatch {n L : ℕ} {a b : Network n L} {heap : NaturalHeap} {r : Registers ℕ}
    (left : Descriptor heap r.a a) (right : Descriptor heap r.b b) (tape : Bits) :
    NaturalRun program (dispatchSteps a) (state heap r [] tape 0) [] (state heap r [] tape (next a b)) := by
  apply ReferenceProgramSteps.sound
  rcases a with ⟨⟨a,side⟩,l⟩ | a <;> rcases b with ⟨⟨b,sg⟩,k⟩ | b
  · obtain ⟨pa,fa,_,_,hp,_⟩ := left
    obtain ⟨pb,fb,_,_,hq,_⟩ := right
    simp [ReferenceProgramSteps.run,state,program,dispatchSteps,next,tickNatural,Registers.get,tagBranch,hp,hq]
  · obtain ⟨pa,fa,_,_,hp,_⟩ := left
    change heap[r.b]?=some (.flag b) at right
    cases b <;> simp [ReferenceProgramSteps.run,state,program,dispatchSteps,next,tickNatural,Registers.get,tagBranch,hp,right]
  · obtain ⟨pb,fb,_,_,hq,_⟩ := right
    change heap[r.a]?=some (.flag a) at left
    cases a <;> simp [ReferenceProgramSteps.run,state,program,dispatchSteps,next,tickNatural,Registers.get,tagBranch,left,hq]
  · change heap[r.a]?=some (.flag a) at left
    change heap[r.b]?=some (.flag b) at right
    cases a <;> cases b <;>
      simp [ReferenceProgramSteps.run,state,program,dispatchSteps,next,tickNatural,Registers.get,tagBranch,left,right]

private theorem core_call {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Node n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits} {core pins : ℕ}
    (left : Descriptor heap r.a (.inl a)) (right : Descriptor heap r.b (.inl b))
    (bundle : heap[r.c]?=some (.pair core pins))
    (ctx : CandidateDescriptorCapacityProgram.Context heap core D grid (BinaryMinimumWordProgram.word grid bound) (fuelWord D s t L B))
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L (.inl a)) (numberEquiv n L (.inl b))).bits ∧
      NaturalRun program k (state heap r [] tape 12) [] (state (heap++ext) (r.set .r3 root) [] tape 28) ∧
      k ≤ CandidateDescriptorCapacityProgram.instructionBound n L grid.length bound.length+3 := by
  let args := r.set .r2 core
  let frame : Frame ℕ 877 := ⟨28,.r3,r⟩
  have prep : NaturalRun program 2 (state heap r [] tape 12) [] (state heap args [frame] tape (coreLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,bundle]
  obtain ⟨ext,regs,root,k,rep,body,limit⟩ := CandidateDescriptorCapacityProgram.natural_descriptor_capacity
    (r:=args) left right ctx scale cap tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (coreLabel 13)
  have lifted := ReferenceProgramLabels.run coreLabel CandidateDescriptorCapacityProgram.program program core_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have trace : NaturalRun program k (state heap args [frame] tape (coreLabel 0)) [] stop := by
    simpa [state,stop,CandidateDescriptorCapacityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 28,[],0⟩ := by
    simp [state,stop,program,coreLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,k+3,rep,?_,by omega⟩
  have count : 2+(k+1)=k+3 := by omega
  rw [← count]
  exact append_run prep (append_run trace (.step ret (.done _)))

private theorem terminal_run {n L : ℕ} {D : Input n} {a : Node n L} {pin : Port n} {side : Bool}
    {heap : NaturalHeap} {r args : Registers ℕ} {grid cap budget : Bits} {pc : Fin 877} {pre : ℕ} {tape : Bits}
    (prep : NaturalRun program pre (state heap r [] tape pc) []
      (state heap args [⟨28,.r3,r⟩] tape (termLabel 0)))
    (node : Descriptor heap args.a (.inl a)) (pinned : PortAt heap args.b pin)
    (marker : heap[args.d]?=some (.flag side)) (ctx : CandidateDescriptorCapacityProgram.Context heap args.c D grid cap budget) :
    let fields := CandidateTerminalFlagsProgram.result side (isZero a.2.val.bits).1 a.1.2
      (CandidatePortGapProgram.active D a.1.1) (decide (a.1.1=pin))
    ∃ (ext : NaturalHeap) (root k : ℕ),BoolList (heap++ext) root (CandidateCapacityWords.word budget fields.1 fields.2) ∧
      NaturalRun program k (state heap r [] tape pc) [] (state (heap++ext) (r.set .r3 root) [] tape 28) ∧
      k ≤ CandidateTerminalDescriptorProgram.instructionBound n L+pre+1 := by
  dsimp only
  obtain ⟨ext,regs,root,k,rep,body,bound⟩ := CandidateTerminalDescriptorProgram.natural_terminal_word node pinned marker ctx tape
  let frame : Frame ℕ 877 := ⟨28,.r3,r⟩
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (termLabel 16)
  have lifted := ReferenceProgramLabels.run termLabel CandidateTerminalDescriptorProgram.program program term_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have trace : NaturalRun program k (state heap args [frame] tape (termLabel 0)) [] stop := by
    simpa [state,stop,CandidateTerminalDescriptorProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 28,[],0⟩ := by
    simp [state,stop,program,termLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,pre+k+1,rep,?_,by omega⟩
  simpa only [Nat.add_assoc,Nat.zero_add,List.nil_append] using append_run prep (append_run trace (.step ret (.done _)))

private theorem source_call {n L B : ℕ} {D : Input n} {s t : Fin n} {b : Node n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid cap : Bits} {core pins start finish : ℕ}
    (tag : heap[r.a]?=some (.flag false)) (node : Descriptor heap r.b (.inl b))
    (bundle : heap[r.c]?=some (.pair core pins)) (terminal : heap[pins]?=some (.pair start finish))
    (pinned : PortAt heap finish (TerminalPorts.sink t))
    (ctx : CandidateDescriptorCapacityProgram.Context heap core D grid cap (fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L (.inr false)) (numberEquiv n L (.inl b))).bits ∧
      NaturalRun program k (state heap r [] tape 20) [] (state (heap++ext) (r.set .r3 root) [] tape 28) ∧
      k ≤ CandidateTerminalDescriptorProgram.instructionBound n L+7 := by
  let args : Registers ℕ := ⟨r.b,finish,core,r.a⟩
  let frame : Frame ℕ 877 := ⟨28,.r3,r⟩
  have first : NaturalRun program 3 (state heap r [] tape 20) []
      (state heap ((r.set .r3 r.a).set .r0 r.b) [frame] tape 23) := by
    apply ReferenceProgramSteps.sound
    rfl
  have second : NaturalRun program 3 (state heap ((r.set .r3 r.a).set .r0 r.b) [frame] tape 23) []
      (state heap args [frame] tape (termLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,bundle,terminal]
  have prep : NaturalRun program 6 (state heap r [] tape 20) []
      (state heap args [frame] tape (termLabel 0)) := append_run first second
  obtain ⟨ext,root,k,rep,body,bound⟩ := terminal_run prep node pinned tag ctx
  refine ⟨ext,root,k,?_,body,by omega⟩
  rw [← CandidateTerminalDescriptorProgram.source_word_eq D s t B b]
  exact rep

private theorem sink_call {n L B : ℕ} {D : Input n} {s t : Fin n} {a : Node n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid cap : Bits} {core pins start finish : ℕ}
    (node : Descriptor heap r.a (.inl a)) (tag : heap[r.b]?=some (.flag true))
    (bundle : heap[r.c]?=some (.pair core pins)) (terminal : heap[pins]?=some (.pair start finish))
    (pinned : PortAt heap start (TerminalPorts.source s))
    (ctx : CandidateDescriptorCapacityProgram.Context heap core D grid cap (fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L (.inl a)) (numberEquiv n L (.inr true))).bits ∧
      NaturalRun program k (state heap r [] tape 16) [] (state (heap++ext) (r.set .r3 root) [] tape 28) ∧
      k ≤ CandidateTerminalDescriptorProgram.instructionBound n L+6 := by
  let args : Registers ℕ := ⟨r.a,start,core,r.b⟩
  let frame : Frame ℕ 877 := ⟨28,.r3,r⟩
  have prep : NaturalRun program 5 (state heap r [] tape 16) []
      (state heap args [frame] tape (termLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,bundle,terminal]
  obtain ⟨ext,root,k,rep,body,bound⟩ := terminal_run prep node pinned tag ctx
  refine ⟨ext,root,k,?_,body,by omega⟩
  rw [← CandidateTerminalDescriptorProgram.sink_word_eq D s t B a]
  exact rep

private theorem zero_call {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Network n L}
    {heap : NaturalHeap} {r : Registers ℕ}
    (zero : CandidateCapacityFlags.flags D s t L B a b=(false,false)) (tape : Bits) :
    BoolList (heap++[.nil]) heap.length (capacities D s t L B (numberEquiv n L a) (numberEquiv n L b)).bits ∧
      NaturalRun program 1 (state heap r [] tape 5) [] (state (heap++[.nil]) (r.set .r3 heap.length) [] tape 28) := by
  constructor
  · rw [← CandidateCapacityValues.capacity_word D s t L B a b,zero]
    exact .nil (by simp)
  · apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell]

theorem natural_cell {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Network n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (left : Descriptor heap r.a a) (right : Descriptor heap r.b b) (inputs : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L a) (numberEquiv n L b)).bits ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 28) ∧
      k ≤ instructionBound n L grid.length bound.length := by
  have prep := dispatch left right tape
  obtain ⟨core,pins,start,finish,bundle,terminal,sp,tp,ctx⟩ := inputs
  have coreBound := Nat.le_max_left (CandidateDescriptorCapacityProgram.instructionBound n L grid.length bound.length)
    (CandidateTerminalDescriptorProgram.instructionBound n L)
  have termBound := Nat.le_max_right (CandidateDescriptorCapacityProgram.instructionBound n L grid.length bound.length)
    (CandidateTerminalDescriptorProgram.instructionBound n L)
  rcases a with a | a <;> rcases b with b | b
  · obtain ⟨ext,root,k,rep,body,limit⟩ := core_call left right bundle ctx scale cap tape
    refine ⟨ext,root,2+k,rep,append_run prep body,?_⟩
    unfold instructionBound
    omega
  · cases b
    · have ⟨rep,body⟩ := zero_call (D:=D) (s:=s) (t:=t) (L:=L) (B:=B) (a:=.inl a) (b:=.inr false) (heap:=heap) (r:=r) rfl tape
      exact ⟨[.nil],heap.length,3,rep,append_run prep body,by unfold instructionBound; omega⟩
    · obtain ⟨ext,root,k,rep,body,limit⟩ := sink_call left right bundle terminal sp ctx tape
      refine ⟨ext,root,2+k,rep,append_run prep body,?_⟩
      unfold instructionBound
      omega
  · cases a
    · obtain ⟨ext,root,k,rep,body,limit⟩ := source_call left right bundle terminal tp ctx tape
      refine ⟨ext,root,2+k,rep,append_run prep body,?_⟩
      unfold instructionBound
      omega
    · have ⟨rep,body⟩ := zero_call (D:=D) (s:=s) (t:=t) (L:=L) (B:=B) (a:=.inr true) (b:=.inl b) (heap:=heap) (r:=r) rfl tape
      exact ⟨[.nil],heap.length,2,rep,append_run prep body,by unfold instructionBound; omega⟩
  · have ⟨rep,body⟩ := zero_call (D:=D) (s:=s) (t:=t) (L:=L) (B:=B) (a:=.inr a) (b:=.inr b) (heap:=heap) (r:=r)
      (by cases a <;> cases b <;> rfl) tape
    have bound : dispatchSteps (n:=n) (L:=L) (.inr a) ≤ 2 := by cases a <;> simp [dispatchSteps]
    have label : next (.inr a : Network n L) (.inr b)=5 := by cases a <;> cases b <;> rfl
    rw [label] at prep
    exact ⟨[.nil],heap.length,dispatchSteps (n:=n) (L:=L) (.inr a)+1,rep,append_run prep body,by unfold instructionBound; omega⟩

end DirectedFlowCutGap.CandidateCapacityCellProgram
