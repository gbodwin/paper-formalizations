import DirectedFlowCutGap.LastTwoWordProgram
import DirectedFlowCutGap.CandidatePhysicalCut

/-!
# The numbered candidate search configuration

The program enumerates the vertex words, builds their ordered Cartesian
product, and reads the last two words for the artificial terminals. The
configuration points to the returned lists and terminal words.
-/

namespace DirectedFlowCutGap.CandidateSearchConfigurationProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open PathCostMaterialization (WordList list_extend)
open GraphWalkExtension (Edge EdgeList edgeList_extend)
open GraphDiscoveryProgram (Vertices)
open ResidualFlowLoopProgram (Configuration)
open ResidualFlowStepProgram (wordTable pairTable)
open BinaryLabelRangeProgram (wordsFrom)
open ConcreteExpressionProgram (append_run)

def rangeLabel (pc : Fin 65) : Fin 129 := ⟨16+pc.val,by omega⟩
def productLabel (pc : Fin 32) : Fin 129 := ⟨81+pc.val,by omega⟩
def endpointsLabel (pc : Fin 16) : Fin 129 := ⟨113+pc.val,by omega⟩

def program : Program 129 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (rangeLabel 0) 1 .r0
    | 1 => .move .r1 .r0 2
    | 2 => .call (productLabel 0) 3 .r2
    | 3 => .call (endpointsLabel 0) 4 .r1
    | 4 => .field .r3 .r1 true 5
    | 5 => .make .r2 (.pair .r3 .r2) 6
    | 6 => .field .r3 .r1 false 7
    | 7 => .make .r2 (.pair .r3 .r2) 8
    | 8 => .make .r3 (.pair .r0 .r2) 9
    | _ => .halt
  else if h : pc.val<81 then
    if pc.val=20 then .ret .r3
    else ReferenceProgramLabels.instruction rangeLabel (BinaryLabelRangeProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<113 then
    if pc.val=83 then .ret .r3
    else ReferenceProgramLabels.instruction productLabel (WordPairProductProgram.program ⟨pc.val-81,by omega⟩)
  else if pc.val=122 then .ret .r3
  else ReferenceProgramLabels.instruction endpointsLabel (LastTwoWordProgram.program ⟨pc.val-113,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 129))
    (tape : Bits) (pc : Fin 129) : NaturalState 129 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (count : Bits) : ℕ :=
  BinaryLabelRangeProgram.steps count+WordPairProductProgram.steps (value count) (value count)+
    LastTwoWordProgram.steps (value count-2)+12

def instructionBound (n width : ℕ) : ℕ :=
  n*(8*n.size+19)+10*width+9+WordPairProductProgram.steps n n+4*n+18

theorem steps_le (count : Bits) : steps count ≤ instructionBound (value count) count.length := by
  have labels := BinaryLabelRangeProgram.steps_le count
  have ends : LastTwoWordProgram.steps (value count-2)≤4*value count+6 := by
    unfold LastTwoWordProgram.steps
    omega
  unfold steps instructionBound
  omega

private theorem range_slots (pc : Fin 65) (h : BinaryLabelRangeProgram.program pc≠.halt) :
    program (rangeLabel pc) = ReferenceProgramLabels.instruction rangeLabel (BinaryLabelRangeProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,rangeLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<81 by omega,show 16+pc.val≠20 by omega]

private theorem product_slots (pc : Fin 32) (h : WordPairProductProgram.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (WordPairProductProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,productLabel,show ¬81+pc.val<16 by omega,show ¬81+pc.val<81 by omega,
      show 81+pc.val<113 by omega,show 81+pc.val≠83 by omega]

private theorem endpoints_slots (pc : Fin 16) (h : LastTwoWordProgram.program pc≠.halt) :
    program (endpointsLabel pc)=ReferenceProgramLabels.instruction endpointsLabel (LastTwoWordProgram.program pc) := by
  by_cases hp : pc.val=9
  · have eq : pc=9 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,endpointsLabel,show ¬113+pc.val<16 by omega,show ¬113+pc.val<81 by omega,
      show ¬113+pc.val<113 by omega,show 113+pc.val≠122 by omega]

private theorem range_call {heap : NaturalHeap} {r : Registers ℕ} {count : Bits}
    (input : BoolList heap r.a count) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (wordsFrom 0 (value count)) ∧
      NaturalRun program (BinaryLabelRangeProgram.steps count+2) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  obtain ⟨ext,args,root,rep,body⟩ := BinaryLabelRangeProgram.natural_range input tape
  let frame : Frame ℕ 129 := ⟨1,.r0,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (rangeLabel 4)
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (rangeLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run rangeLabel BinaryLabelRangeProgram.program program range_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (BinaryLabelRangeProgram.steps count) (state heap r [frame] tape (rangeLabel 0)) [] stop := by
    simpa [state,stop,BinaryLabelRangeProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [state,stop,rangeLabel,program,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem product_call {heap : NaturalHeap} {r : Registers ℕ} {vs : List Bits}
    (input : WordList heap r.a vs) (tape : Bits) :
    ∃ ext root,EdgeList (heap++ext) root (vs.product vs) ∧
      NaturalRun program (WordPairProductProgram.steps vs.length vs.length+3) (state heap r [] tape 1) []
        (state (heap++ext) ((r.set .r1 r.a).set .r2 root) [] tape 3) := by
  let args := r.set .r1 r.a
  obtain ⟨ext,regs,root,rep,body⟩ := WordPairProductProgram.natural_product (r:=args) input input tape
  let frame : Frame ℕ 129 := ⟨3,.r2,args⟩
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (productLabel 2)
  have move : tickNatural program (state heap r [] tape 1)=some ⟨state heap args [] tape 2,[],0⟩ := rfl
  have enter : tickNatural program (state heap args [] tape 2)=
      some ⟨state heap args [frame] tape (productLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run productLabel WordPairProductProgram.program program product_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (WordPairProductProgram.steps vs.length vs.length)
      (state heap args [frame] tape (productLabel 0)) [] stop := by
    simpa [state,stop,WordPairProductProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (args.set .r2 root) [] tape 3,[],0⟩ := by
    simp [state,stop,productLabel,program,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step move (.step enter (append_run run (.step ret (.done _))))⟩

private theorem ends_call {heap : NaturalHeap} {r : Registers ℕ} {m : ℕ} (room : 2≤m)
    (input : WordList heap r.a (wordsFrom 0 m)) (tape : Bits) :
    ∃ ext root,Edge (heap++ext) root ((m-2).bits,(m-1).bits) ∧
      NaturalRun program (LastTwoWordProgram.steps (m-2)+2) (state heap r [] tape 3) []
        (state (heap++ext) (r.set .r1 root) [] tape 4) := by
  obtain ⟨ext,args,root,rep,body⟩ := LastTwoWordProgram.natural_last_range room input tape
  let frame : Frame ℕ 129 := ⟨4,.r1,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (endpointsLabel 9)
  have enter : tickNatural program (state heap r [] tape 3)=some ⟨state heap r [frame] tape (endpointsLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run endpointsLabel LastTwoWordProgram.program program endpoints_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (LastTwoWordProgram.steps (m-2))
      (state heap r [frame] tape (endpointsLabel 0)) [] stop := by
    simpa [state,stop,LastTwoWordProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 4,[],0⟩ := by
    simp [state,stop,endpointsLabel,program,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem from_words {heap : NaturalHeap} {root : ℕ} {vs : List Bits}
    (input : WordList heap root vs) : Vertices heap root vs := by
  induction input with
  | nil hp => exact .nil hp
  | cons hp hw _ ih => exact .cons hp hw ih

private theorem pack {heap : NaturalHeap} {r : Registers ℕ} {vs : List Bits} {s t : Bits} {es : List (Bits×Bits)}
    (vertices : WordList heap r.a vs) (ends : Edge heap r.b (s,t)) (pairs : EdgeList heap r.c es) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Configuration (heap++ext) root vs s t es ∧
      NaturalRun program 5 (state heap r [] tape 4) [] (state (heap++ext) (args.set .r3 root) [] tape 9) := by
  obtain ⟨source,target,pair,sourceWord,targetWord⟩ := ends
  let i := heap.length
  let first : Cell ℕ := .pair target r.c
  let second : Cell ℕ := .pair source i
  let third : Cell ℕ := .pair r.a (i+1)
  let ext := [first,second,third]
  let args := (r.set .r3 source).set .r2 (i+1)
  have h₁ : (heap++ext)[i]?=some first := by simp [i,ext]
  have h₂ : (heap++ext)[i+1]?=some second := by
    rw [List.getElem?_append_right (show heap.length ≤ i+1 from Nat.le_succ _)]
    rw [show i+1-heap.length=1 by simp [i]]
    rfl
  have h₃ : (heap++ext)[i+2]?=some third := by
    rw [List.getElem?_append_right (show heap.length ≤ i+2 by change i ≤ i+2; omega)]
    rw [show i+2-heap.length=2 by simp [i]]
    rfl
  refine ⟨ext,args,i+2,⟨r.a,i+1,source,i,h₃,h₂,from_words (list_extend vertices ext),
    boolList_extend sourceWord ext,⟨target,r.c,h₁,boolList_extend targetWord ext,edgeList_extend pairs ext⟩⟩,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
    allocateNatural,Recipe.cell,args,i,ext,first,second,third,pair,lookup_extend pair [first],List.append_assoc,Nat.add_assoc]

theorem natural_configuration {heap : NaturalHeap} {r : Registers ℕ} {count : Bits} (room : 2≤value count)
    (input : BoolList heap r.a count) (tape : Bits) :
    let vs := wordsFrom 0 (value count)
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Configuration (heap++ext) root vs (value count-2).bits (value count-1).bits (vs.product vs) ∧
      NaturalRun program (steps count) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 9) := by
  dsimp only
  obtain ⟨er,vertices,labels,build⟩ := range_call input tape
  let mid := heap++er
  let withLabels := r.set .r0 vertices
  obtain ⟨ep,edges,edgeRep,product⟩ := product_call (r:=withLabels) labels tape
  let grown := mid++ep
  let withPairs := (withLabels.set .r1 withLabels.a).set .r2 edges
  obtain ⟨ee,ports,ends,scan⟩ := ends_call (r:=withPairs) room (list_extend labels ep) tape
  let ready := withPairs.set .r1 ports
  have verticesRep : WordList (grown++ee) ready.a (wordsFrom 0 (value count)) :=
    list_extend (list_extend labels ep) ee
  obtain ⟨epack,args,root,rep,finish⟩ := pack (r:=ready) verticesRep ends (edgeList_extend edgeRep ee) tape
  refine ⟨er++ep++ee++epack,args,root,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using rep
  · have run := append_run build (append_run product (append_run scan finish))
    simp only [BinaryLabelRangeProgram.words_length] at run
    unfold steps
    convert run using 1 <;> first | rfl | omega | simp only [grown,mid,List.append_assoc]

private theorem product_labels {n : ℕ} (label : Fin n→Bits) (xs ys : List (Fin n)) :
    (xs.map label).product (ys.map label)=(xs.product ys).map (SupportSearchEncoding.encodeEdge label) := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
    simp [List.product,List.map_append,List.map_map,SupportSearchEncoding.encodeEdge,Function.comp_def] at ih ⊢
    exact ih

open CandidatePhysicalCut (networkSize numberEquiv label)
open MinimumClosureCut (source sink)

theorem natural_candidate_configuration {heap : NaturalHeap} {r : Registers ℕ} {n L : ℕ} {count : Bits}
    (numeric : value count=networkSize n L) (input : BoolList heap r.a count) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Configuration (heap++ext) root (wordTable (label (n:=n) (L:=L)))
        (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))) ∧
      NaturalRun program (steps count) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 9) := by
  have room : 2≤value count := by rw [numeric]; unfold networkSize; omega
  obtain ⟨ext,args,root,rep,run⟩ := natural_configuration room input tape
  have labels : wordsFrom 0 (value count)=wordTable (label (n:=n) (L:=L)) := by
    rw [numeric,BinaryLabelRangeProgram.words_fin]
    rfl
  have pairs : (wordsFrom 0 (value count)).product (wordsFrom 0 (value count))=pairTable (label (n:=n) (L:=L)) := by
    rw [labels]
    exact product_labels _ _ _
  have hs : (value count-2).bits=label ((numberEquiv n L) source) := by
    rw [numeric,label,CandidatePhysicalCut.numberEquiv_value]
    simp [CandidateEnumeration.networkIndex]
  have ht : (value count-1).bits=label ((numberEquiv n L) sink) := by
    rw [numeric,label,CandidatePhysicalCut.numberEquiv_value]
    simp [CandidateEnumeration.networkIndex]
  refine ⟨ext,args,root,?_,run⟩
  rw [pairs,labels,hs,ht] at rep
  exact rep

private theorem at_entry (s : NaturalState 129) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_candidate_configuration {n L H A : ℕ} (count : Bits) (numeric : value count=networkSize n L)
    (initial : BitState 129) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a count) :
    ∃ charge out, Run program (steps count) charge initial [] out ∧
      Configuration (eraseState out).heap (eraseState out).registers.d (wordTable (label (n:=n) (L:=L)))
        (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=9 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 129 H A (instructionBound (networkSize n L) count.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,rep,body⟩ := natural_candidate_configuration numeric input old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 9
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program (steps count) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,charge,unchanged⟩ := terminating_simulation bounded run stop
  have countBound := steps_le count
  rw [numeric] at countBound
  refine ⟨paid,out,execution,?_,unchanged,?_,?_,⟨ext,?_⟩,hstop,
    charge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ countBound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateSearchConfigurationProgram
