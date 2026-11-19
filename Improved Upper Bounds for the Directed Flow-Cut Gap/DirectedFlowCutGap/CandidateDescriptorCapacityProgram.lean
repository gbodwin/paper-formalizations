import DirectedFlowCutGap.CandidateCoreRelationsProgram

/-! Compute a core-node capacity from the actual descriptors and graph data. -/

namespace DirectedFlowCutGap.CandidateDescriptorCapacityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Node)
open CandidateNodeListsProgram (Descriptor PortAt descriptor_extend)
open CandidateCoreCapacityProgram (Relations)
open CandidatePortAdjacencyProgram (rows result)
open CandidatePortGapProgram (InputBounds bounds_extend)
open CandidatePhysicalCut (capacities numberEquiv fuelWord)
open EncodedCandidateCapacity (Input)

def Context {n : ℕ} (heap : NaturalHeap) (root : ℕ) (D : Input n) (grid cap budget : Bits) : Prop :=
  ∃ graph resources removed rest limits palette,
    heap[root]?=some (.pair graph resources) ∧ heap[resources]?=some (.pair removed rest) ∧
      heap[rest]?=some (.pair limits palette) ∧ GraphAdjacencyProgram.Matrix heap graph (rows D) ∧
      BoolList heap removed D.removed.toList ∧ InputBounds heap limits grid cap ∧
      CandidateCapacityWords.Stored heap palette budget

theorem context_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {grid cap budget : Bits}
    (context : Context heap root D grid cap budget) (ext : NaturalHeap) : Context (heap++ext) root D grid cap budget := by
  obtain ⟨g,resources,m,rest,limits,palette,pair,res,bundle,graph,removed,bounds,words⟩ := context
  exact ⟨g,resources,m,rest,limits,palette,lookup_extend pair ext,lookup_extend res ext,lookup_extend bundle ext,
    GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend removed ext,bounds_extend bounds ext,
    CandidateCapacityWords.stored_extend words ext⟩

def relationLabel (pc : Fin 236) : Fin 576 := ⟨64+pc.val,by omega⟩
def gapLabel (pc : Fin 68) : Fin 576 := ⟨300+pc.val,by omega⟩
def coreLabel (pc : Fin 208) : Fin 576 := ⟨368+pc.val,by omega⟩

def program : Program 576 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .call 32 2 .r2
    | 2 => .field .r0 .r0 true 3
    | 3 => .field .r0 .r0 true 4
    | 4 => .field .r1 .r1 true 5
    | 5 => .field .r1 .r1 true 6
    | 6 => .make .r0 (.pair .r0 .r1) 7
    | 7 => .field .r1 .r2 false 8
    | 8 => .make .r2 (.pair .r3 .r2) 9
    | 9 => .field .r3 .r2 true 10
    | 10 => .field .r3 .r3 true 11
    | 11 => .field .r2 .r2 false 12
    | 12 => .call (coreLabel 0) 13 .r3
    | 16 => .field .r2 .r2 false (relationLabel 0)
    | 32 => .call 48 33 .r1
    | 33 => .field .r1 .r1 true 34
    | 34 => .field .r2 .r2 true 35
    | 35 => .field .r2 .r2 true 36
    | 36 => .field .r0 .r2 false 37
    | 37 => .field .r0 .r0 false 38
    | 38 => .make .r1 (.pair .r0 .r1) 39
    | 39 => .field .r2 .r2 true 40
    | 40 => .make .r3 (.pair .r1 .r2) 41
    | 41 => .ret .r3
    | 48 => .field .r0 .r0 false 49
    | 49 => .field .r2 .r2 true 50
    | 50 => .field .r1 .r2 false 51
    | 51 => .field .r2 .r2 true 52
    | 52 => .field .r2 .r2 false (gapLabel 0)
    | _ => .halt
  else if h : pc.val<300 then
    if pc.val=75 then .ret .r3
    else ReferenceProgramLabels.instruction relationLabel
      (CandidateCoreRelationsProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<368 then
    if pc.val=301 then .ret .r3
    else ReferenceProgramLabels.instruction gapLabel (CandidatePortGapAtProgram.program ⟨pc.val-300,by omega⟩)
  else if pc.val=372 then .ret .r3
  else ReferenceProgramLabels.instruction coreLabel
    (CandidateCoreCapacityProgram.program ⟨pc.val-368,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 576))
    (tape : Bits) (pc : Fin 576) : NaturalState 576 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L gridWidth boundWidth : ℕ) : ℕ :=
  CandidateCoreRelationsProgram.instructionBound n+CandidatePortGapAtProgram.instructionBound n+
    CandidateCoreCapacityProgram.instructionBound L.size L.size gridWidth boundWidth+32

private theorem relation_slots (pc : Fin 236) (h : CandidateCoreRelationsProgram.program pc≠.halt) :
    program (relationLabel pc)=ReferenceProgramLabels.instruction relationLabel (CandidateCoreRelationsProgram.program pc) := by
  by_cases hp : pc.val=11
  · have eq : pc=11 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,relationLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<300 by omega,show 64+pc.val≠75 by omega]

private theorem gap_slots (pc : Fin 68) (h : CandidatePortGapAtProgram.program pc≠.halt) :
    program (gapLabel pc)=ReferenceProgramLabels.instruction gapLabel (CandidatePortGapAtProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,gapLabel,show ¬300+pc.val<64 by omega,show ¬300+pc.val<300 by omega,
      show 300+pc.val<368 by omega,show 300+pc.val≠301 by omega]

private theorem core_slots (pc : Fin 208) (h : CandidateCoreCapacityProgram.program pc≠.halt) :
    program (coreLabel pc)=ReferenceProgramLabels.instruction coreLabel (CandidateCoreCapacityProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,coreLabel,show ¬368+pc.val<64 by omega,show ¬368+pc.val<300 by omega,
      show ¬368+pc.val<368 by omega,show 368+pc.val≠372 by omega]

private theorem relation_call {n L : ℕ} {D : Input n} {a b : Node n L} {heap : NaturalHeap} {r : Registers ℕ}
    {g resources : ℕ} (left : Descriptor heap r.a (.inl a)) (right : Descriptor heap r.b (.inl b))
    (context : heap[r.c]?=some (.pair g resources)) (graph : GraphAdjacencyProgram.Matrix heap g (rows D))
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Relations (heap++ext) root a.1.2 b.1.2 (decide (a.1.1=b.1.1)) (result D b.1.1 a.1.1) (decide (a.1=b.1)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k ≤ CandidateCoreRelationsProgram.instructionBound n+3 := by
  let args := r.set .r2 g
  let frame : Frame ℕ 576 := ⟨1,.r3,r⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape (relationLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,context,args,frame]
  obtain ⟨ext,regs,root,k,rep,body,bound⟩ := CandidateCoreRelationsProgram.natural_relations (r:=args) left right graph tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (relationLabel 11)
  have lifted := ReferenceProgramLabels.run relationLabel CandidateCoreRelationsProgram.program program relation_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program k (state heap args [frame] tape (relationLabel 0)) [] stop := by
    simpa [state,stop,CandidateCoreRelationsProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,relationLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,k+3,rep,?_,by omega⟩
  have count : 2+(k+1)=k+3 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem gap_call {n L : ℕ} {D : Input n} {a : Node n L} {heap : NaturalHeap} {r : Registers ℕ}
    {grid cap : Bits} {g resources removed rest bounds palette : ℕ}
    (left : Descriptor heap r.a (.inl a)) (context : heap[r.c]?=some (.pair g resources))
    (res : heap[resources]?=some (.pair removed rest)) (bundle : heap[rest]?=some (.pair bounds palette))
    (mask : BoolList heap removed D.removed.toList) (limits : InputBounds heap bounds grid cap) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      CandidatePortGapProgram.Stored (heap++ext) root (CandidatePortGapProgram.active D a.1.1)
        (CandidatePortGapProgram.gap D grid cap a.1.1) ∧
      NaturalRun program k (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r1 root) [⟨2,.r2,r⟩] tape 33) ∧
      k ≤ CandidatePortGapAtProgram.instructionBound n+8 := by
  rcases a with ⟨⟨p,side⟩,l⟩
  obtain ⟨port,fields,h,f,leftPair,portRep,_⟩ := left
  let args : Registers ℕ := ⟨port,removed,bounds,r.d⟩
  let outer : Frame ℕ 576 := ⟨2,.r2,r⟩
  let inner : Frame ℕ 576 := ⟨33,.r1,r⟩
  let ready := (r.set .r0 port).set .r2 resources
  have first : NaturalRun program 4 (state heap r [] tape 1) [] (state heap ready [inner,outer] tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,ready,outer,inner,context,leftPair]
  have second : NaturalRun program 3 (state heap ready [inner,outer] tape 50) []
      (state heap args [inner,outer] tape (gapLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,ready,args,res,bundle]
  have setup : NaturalRun program 7 (state heap r [] tape 1) [] (state heap args [inner,outer] tape (gapLabel 0)) :=
    append_run first second
  obtain ⟨ext,root,rep,body⟩ := CandidatePortGapAtProgram.natural_gap D (r:=args) portRep mask limits tape
  let stop := state (heap++ext) (args.set .r3 root) [inner,outer] tape (gapLabel 1)
  have lifted := ReferenceProgramLabels.run gapLabel CandidatePortGapAtProgram.program program gap_slots body
  have lifted := ReferenceProgramStack.run program [inner,outer] lifted
  let work := CandidatePortGapProgram.steps (CandidatePortAdjacencyProgram.kind p)
    (CandidatePortAdjacencyProgram.vertex p).val.bits+4
  have run : NaturalRun program work (state heap args [inner,outer] tape (gapLabel 0)) [] stop := by
    simpa [state,stop,work,CandidatePortGapAtProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [outer] tape 33,[],0⟩ := by
    simp [state,stop,program,gapLabel,tickNatural,inner,Registers.get,Registers.set]
  refine ⟨ext,root,work+8,rep,?_,?_⟩
  · have count : 7+(work+1)=work+8 := by omega
    rw [← count]
    exact append_run setup (append_run run (.step ret (.done _)))
  · have limit := CandidatePortGapAtProgram.steps_le p
    omega

def Ready (heap : NaturalHeap) (root : ℕ) (grid gap budget : Bits) : Prop :=
  ∃ bounds palette,heap[root]?=some (.pair bounds palette) ∧
    InputBounds heap bounds grid gap ∧ CandidateCapacityWords.Stored heap palette budget

set_option maxHeartbeats 1600000 in
private theorem make_ready {n : ℕ} {D : Input n} {heap : NaturalHeap} {r : Registers ℕ} {root : ℕ}
    {grid cap gap budget : Bits} {active : Bool}
    (context : Context heap r.c D grid cap budget) (stored : CandidatePortGapProgram.Stored heap root active gap) (tape : Bits) :
    ∃ ext output,Ready (heap++ext) output grid gap budget ∧
      NaturalRun program 9 (state heap (r.set .r1 root) [⟨2,.r2,r⟩] tape 33) []
        (state (heap++ext) (r.set .r2 output) [] tape 2) := by
  obtain ⟨g,resources,removed,rest,limits,palette,hctx,hres,hrest,_,_,⟨scale,capPtr,hlimits,word,_⟩,words⟩ := context
  obtain ⟨flag,gapRoot,pair,_,gapRep⟩ := stored
  let i := heap.length
  let newBounds : Cell ℕ := .pair scale gapRoot
  let extended := heap++[newBounds]
  let ext : NaturalHeap := [newBounds,.pair i palette]
  have last : (heap++ext)[i+1]?=some (.pair i palette) := by
    rw [List.getElem?_append_right (by omega : heap.length ≤ i+1)]
    rw [show i+1-heap.length=1 by simp [i]]
    rfl
  refine ⟨ext,i+1,⟨i,palette,last,⟨scale,gapRoot,by simp [i,ext,newBounds],boolList_extend word ext,
    boolList_extend gapRep ext⟩,CandidateCapacityWords.stored_extend words ext⟩,?_⟩
  let frame : Frame ℕ 576 := ⟨2,.r2,r⟩
  let args : Registers ℕ := ⟨scale,gapRoot,rest,r.d⟩
  have prepare : NaturalRun program 5 (state heap (r.set .r1 root) [frame] tape 33) []
      (state heap args [frame] tape 38) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,pair,hctx,hres,hrest,hlimits]
  have afterFirst : extended[rest]?=some (.pair limits palette) := lookup_extend hrest [newBounds]
  have finish : NaturalRun program 4 (state heap args [frame] tape 38) []
      (state (heap++ext) (r.set .r2 (i+1)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,
      ext,i,newBounds,extended,afterFirst,allocateNatural,Recipe.cell,List.append_assoc]
  exact append_run prepare finish

set_option maxHeartbeats 1600000 in
private theorem core_call {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Node n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (left : Descriptor heap r.a (.inl a)) (right : Descriptor heap r.b (.inl b))
    (ready : Ready heap r.c grid
      (CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid bound) a.1.1) (fuelWord D s t L B))
    (rel : Relations heap r.d a.1.2 b.1.2 (decide (a.1.1=b.1.1)) (result D b.1.1 a.1.1) (decide (a.1=b.1)))
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L (.inl a)) (numberEquiv n L (.inl b))).bits ∧
      NaturalRun program k (state heap r [] tape 2) [] (state (heap++ext) (args.set .r3 root) [] tape 13) ∧
      k ≤ CandidateCoreCapacityProgram.instructionBound a.2.val.bits.length b.2.val.bits.length grid.length bound.length+12 := by
  rcases a with ⟨⟨pa,sa⟩,la⟩
  rcases b with ⟨⟨pb,sb⟩,lb⟩
  obtain ⟨pA,fA,sA,lA,entryA,_,fieldsA,_,wordA⟩ := left
  obtain ⟨pB,fB,sB,lB,entryB,_,fieldsB,_,wordB⟩ := right
  obtain ⟨input,palette,pair,bounds,words⟩ := ready
  let i := heap.length
  let levels : Cell ℕ := .pair lA lB
  let mid := heap++[levels]
  let saved : Registers ℕ := ⟨i,lB,r.c,r.d⟩
  have stage : NaturalRun program 5 (state heap r [] tape 2) [] (state mid saved [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      entryA,entryB,fieldsA,fieldsB,levels,mid,saved,i]
  let fresh : Cell ℕ := .pair r.d r.c
  let ext : NaturalHeap := [levels,fresh]
  let grown := heap++ext
  have heapEq : mid++[fresh]=grown := by simp only [mid,grown,ext,List.append_assoc,List.cons_append,List.nil_append]
  let args : Registers ℕ := ⟨i,input,r.d,palette⟩
  let frame : Frame ℕ 576 := ⟨13,.r3,args⟩
  have storedPair : mid[r.c]?=some (.pair input palette) := lookup_extend pair [levels]
  have bundleAfter : grown[r.c]?=some (.pair input palette) := lookup_extend pair ext
  let ready : Registers ℕ := ⟨i,input,mid.length,r.d⟩
  have first : NaturalRun program 2 (state mid saved [] tape 7) [] (state grown ready [] tape 9) := by
    rw [← heapEq]
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      storedPair,mid,ready,saved,fresh,i]
  have freshPair : grown[mid.length]?=some fresh := by
    have h : (mid++[fresh])[mid.length]?=some fresh := by simp
    simpa only [heapEq] using h
  have second : NaturalRun program 4 (state grown ready [] tape 9) [] (state grown args [frame] tape (coreLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
      freshPair,bundleAfter,ready,fresh,args,frame]
  have rest : NaturalRun program 6 (state mid saved [] tape 7) [] (state grown args [frame] tape (coreLabel 0)) :=
    append_run first second
  have levelsRep : InputBounds grown args.a la.val.bits lb.val.bits :=
    ⟨lA,lB,by simp [grown,ext,i,args,levels],boolList_extend wordA ext,boolList_extend wordB ext⟩
  have relRep : Relations grown args.c sa sb (decide (pa=pb)) (result D pb pa) (decide ((pa,sa)=(pb,sb))) := by
    exact CandidateCoreRelationsProgram.relations_extend rel ext
  obtain ⟨ec,regs,root,k,rep,body,limit⟩ := CandidateCoreCapacityProgram.natural_core_capacity
    D s t L B ((pa,sa),la) ((pb,sb),lb) la.val.bits lb.val.bits grid bound (value_bits _) (value_bits _)
    scale cap levelsRep (bounds_extend bounds ext) relRep (CandidateCapacityWords.stored_extend words ext) tape
  let stop := state (grown++ec) (regs.set .r3 root) [frame] tape (coreLabel 4)
  have lifted := ReferenceProgramLabels.run coreLabel CandidateCoreCapacityProgram.program program core_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program k (state grown args [frame] tape (coreLabel 0)) [] stop := by
    simpa [state,stop,grown,CandidateCoreCapacityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (grown++ec) (args.set .r3 root) [] tape 13,[],0⟩ := by
    simp [state,stop,program,coreLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext++ec,args,root,k+12,?_,?_,?_⟩
  · simpa only [grown,List.append_assoc] using rep
  · have count : 5+(6+(k+1))=k+12 := by omega
    rw [← count]
    simpa only [grown,List.append_assoc,List.nil_append,Nat.zero_add] using append_run stage
      (append_run rest (append_run run (.step ret (.done _))))
  · change k+12 ≤ CandidateCoreCapacityProgram.instructionBound la.val.bits.length lb.val.bits.length grid.length bound.length+12
    omega

theorem natural_descriptor_capacity {n L B : ℕ} {D : Input n} {s t : Fin n} {a b : Node n L}
    {heap : NaturalHeap} {r : Registers ℕ} {grid bound : Bits}
    (left : Descriptor heap r.a (.inl a)) (right : Descriptor heap r.b (.inl b))
    (context : Context heap r.c D grid (BinaryMinimumWordProgram.word grid bound) (fuelWord D s t L B))
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (capacities D s t L B (numberEquiv n L (.inl a)) (numberEquiv n L (.inl b))).bits ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 13) ∧
      k ≤ instructionBound n L grid.length bound.length := by
  obtain ⟨g,resources,removed,rest,bounds,palette,hctx,hres,hrest,graph,mask,limits,words⟩ := context
  have raw : Context heap r.c D grid (BinaryMinimumWordProgram.word grid bound) (fuelWord D s t L B) :=
    ⟨g,resources,removed,rest,bounds,palette,hctx,hres,hrest,graph,mask,limits,words⟩
  obtain ⟨er,rel,k,relation,relations,relBound⟩ := relation_call left right hctx graph tape
  let mid := heap++er
  let withRel := r.set .r3 rel
  obtain ⟨eg,gap,m,gapRep,readGap,gapBound⟩ := gap_call (r:=withRel) (descriptor_extend left er)
    (lookup_extend hctx er) (lookup_extend hres er) (lookup_extend hrest er)
    (boolList_extend mask er) (bounds_extend limits er) tape
  let grown := mid++eg
  obtain ⟨eb,boundsRoot,ready,prepare⟩ := make_ready (r:=withRel)
    (context_extend (context_extend raw er) eg) gapRep tape
  let full := grown++eb
  let args := withRel.set .r2 boundsRoot
  have relationsReady : Relations full args.d a.1.2 b.1.2
      (decide (a.1.1=b.1.1)) (result D b.1.1 a.1.1) (decide (a.1=b.1)) :=
    CandidateCoreRelationsProgram.relations_extend (CandidateCoreRelationsProgram.relations_extend relation eg) eb
  obtain ⟨ec,regs,root,o,out,compute,coreBound⟩ := core_call (r:=args)
    (descriptor_extend (descriptor_extend (descriptor_extend left er) eg) eb)
    (descriptor_extend (descriptor_extend (descriptor_extend right er) eg) eb)
    ready relationsReady scale cap tape
  refine ⟨er++eg++eb++ec,regs,root,k+(m+(9+o)),?_,?_,?_⟩
  · simpa only [full,grown,mid,List.append_assoc] using out
  · simpa only [full,grown,mid,List.append_assoc,List.nil_append] using append_run relations
      (append_run readGap (append_run prepare compute))
  · have aWidth : a.2.val.bits.length≤L.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size (by have := a.2.isLt; omega)
    have bWidth : b.2.val.bits.length≤L.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size (by have := b.2.isLt; omega)
    unfold instructionBound CandidateCoreCapacityProgram.instructionBound at *
    omega

end DirectedFlowCutGap.CandidateDescriptorCapacityProgram
