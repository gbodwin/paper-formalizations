import DirectedFlowCutGap.CandidatePortEqualityProgram
import DirectedFlowCutGap.CandidatePortReadPrograms
import DirectedFlowCutGap.CandidateCoreCapacityProgram

/-!
# Core relations from actual node descriptors

The operands are two stored descriptors and the original adjacency matrix.
The node comparison and reverse-arc lookup supply the relation record
used directly by the capacity program.
-/

namespace DirectedFlowCutGap.CandidateCoreRelationsProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Node Port)
open CandidateNodeListsProgram (Descriptor PortAt)
open CandidateCoreCapacityProgram (Relations)
open CandidatePortAdjacencyProgram (rows result)
open EncodedCandidateCapacity (Input)

def equalityLabel (pc : Fin 72) : Fin 236 := ⟨32+pc.val,by omega⟩
def adjacencyLabel (pc : Fin 132) : Fin 236 := ⟨104+pc.val,by omega⟩

def program : Program 236 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .call 20 2 .r2
    | 2 => .make .r2 (.pair .r3 .r2) 3
    | 3 => .field .r0 .r0 true 4
    | 4 => .field .r0 .r0 false 5
    | 5 => .field .r1 .r1 true 6
    | 6 => .field .r1 .r1 false 7
    | 7 => .call 24 8 .r3
    | 8 => .make .r0 (.pair .r0 .r1) 9
    | 9 => .make .r2 (.pair .r0 .r2) 10
    | 10 => .make .r3 (.pair .r2 .r3) 11
    | 16 => .field .r0 .r0 false 17
    | 17 => .field .r1 .r1 false (equalityLabel 0)
    | 20 => .field .r0 .r0 false 21
    | 21 => .field .r1 .r1 false (adjacencyLabel 0)
    | 24 => .branch .r3 31 29 25 31
    | 25 => .branch .r0 31 26 27 31
    | 26 => .branch .r1 31 28 29 31
    | 27 => .branch .r1 31 29 28 31
    | 28 => .make .r3 (.flag true) 30
    | 29 => .make .r3 (.flag false) 30
    | 30 => .ret .r3
    | _ => .halt
  else if h : pc.val<104 then
    if pc.val=50 then .ret .r3
    else ReferenceProgramLabels.instruction equalityLabel
      (CandidatePortEqualityProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=105 then .ret .r3
  else ReferenceProgramLabels.instruction adjacencyLabel
    (CandidateReverseAdjacencyProgram.program ⟨pc.val-104,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 236))
    (tape : Bits) (pc : Fin 236) : NaturalState 236 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n : ℕ) : ℕ :=
  CandidatePortEqualityProgram.instructionBound n+CandidateReverseAdjacencyProgram.instructionBound n+22

private theorem equality_slots (pc : Fin 72) (h : CandidatePortEqualityProgram.program pc≠.halt) :
    program (equalityLabel pc)=ReferenceProgramLabels.instruction equalityLabel (CandidatePortEqualityProgram.program pc) := by
  by_cases hp : pc.val=18
  · have eq : pc=18 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,equalityLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<104 by omega,show 32+pc.val≠50 by omega]

private theorem adjacency_slots (pc : Fin 132) (h : CandidateReverseAdjacencyProgram.program pc≠.halt) :
    program (adjacencyLabel pc)=
      ReferenceProgramLabels.instruction adjacencyLabel (CandidateReverseAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,adjacencyLabel,show ¬104+pc.val<32 by omega,show ¬104+pc.val<104 by omega,show 104+pc.val≠105 by omega]

private theorem equality_call {n : ℕ} {p q : Port n} {heap : NaturalHeap} {r : Registers ℕ} {i j a b : ℕ}
    (left : heap[r.a]?=some (.pair i a)) (right : heap[r.b]?=some (.pair j b))
    (first : PortAt heap i p) (second : PortAt heap j q) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (decide (p=q))) ∧
      NaturalRun program (CandidatePortEqualityProgram.steps p q+4) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let args := (r.set .r0 i).set .r1 j
  let caller : Frame ℕ 236 := ⟨1,.r3,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [caller] tape (equalityLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,caller,left,right]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidatePortEqualityProgram.natural_equality (r:=args) first second tape
  let stop := state (heap++ext) (regs.set .r3 root) [caller] tape (equalityLabel 18)
  have lifted := ReferenceProgramLabels.run equalityLabel CandidatePortEqualityProgram.program program equality_slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  let work := CandidatePortEqualityProgram.steps p q
  have run : NaturalRun program work (state heap args [caller] tape (equalityLabel 0)) [] stop := by
    simpa [state,stop,work,CandidatePortEqualityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,equalityLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem adjacency_call {n : ℕ} {D : Input n} {p q : Port n} {heap : NaturalHeap} {r : Registers ℕ}
    {i j a b : ℕ} (left : heap[r.a]?=some (.pair i a)) (right : heap[r.b]?=some (.pair j b))
    (first : PortAt heap i p) (second : PortAt heap j q)
    (graph : GraphAdjacencyProgram.Matrix heap r.c (rows D)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),(heap++ext)[root]?=some (.flag (result D q p)) ∧
      NaturalRun program k (state heap r [] tape 1) [] (state (heap++ext) (r.set .r2 root) [] tape 2) ∧
      k ≤ CandidateReverseAdjacencyProgram.instructionBound n+4 := by
  let args := (r.set .r0 i).set .r1 j
  let caller : Frame ℕ 236 := ⟨2,.r2,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 1) [] (state heap args [caller] tape (adjacencyLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,caller,left,right]
  obtain ⟨ext,root,k,rep,body,bound⟩ := CandidateReverseAdjacencyProgram.natural_reverse (r:=args) first second graph tape
  let stop := state (heap++ext) (args.set .r3 root) [caller] tape (adjacencyLabel 1)
  have lifted := ReferenceProgramLabels.run adjacencyLabel CandidateReverseAdjacencyProgram.program program adjacency_slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  have run : NaturalRun program k (state heap args [caller] tape (adjacencyLabel 0)) [] stop := by
    simpa [state,stop,CandidateReverseAdjacencyProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,adjacencyLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext,root,k+4,rep,?_,by omega⟩
  have count : 3+(k+1)=k+4 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

def pointSteps (same : Bool) : ℕ := if same then 6 else 4

private theorem point_call {heap : NaturalHeap} {r : Registers ℕ} {a b same : Bool}
    (left : heap[r.a]?=some (.flag a)) (right : heap[r.b]?=some (.flag b)) (port : heap[r.d]?=some (.flag same))
    (tape : Bits) :
    NaturalRun program (pointSteps same) (state heap r [] tape 7) []
      (state (heap++[.flag (same && (a==b))]) (r.set .r3 heap.length) [] tape 8) := by
  let frame : Frame ℕ 236 := ⟨8,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 7)=some ⟨state heap r [frame] tape 24,[],0⟩ := rfl
  cases same with
  | false =>
    have body : NaturalRun program 3 (state heap r [frame] tape 24) []
        (state (heap++[.flag false]) (r.set .r3 heap.length) [] tape 8) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,
        allocateNatural,Recipe.cell,port,frame]
    exact .step enter body
  | true =>
    have begin : NaturalRun program 2 (state heap r [frame] tape 24) []
        (state heap r [frame] tape (if a then 27 else 26)) := by
      apply ReferenceProgramSteps.sound
      cases a <;> simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,tagBranch,port,left]
    have finish : NaturalRun program 3 (state heap r [frame] tape (if a then 27 else 26)) []
        (state (heap++[.flag (a==b)]) (r.set .r3 heap.length) [] tape 8) := by
      apply ReferenceProgramSteps.sound
      cases a <;> cases b <;>
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,
          allocateNatural,Recipe.cell,right,frame]
    exact .step enter (append_run begin finish)

theorem relations_extend {heap : NaturalHeap} {root : ℕ} {a b same edge point : Bool}
    (rel : Relations heap root a b same edge point) (ext : NaturalHeap) : Relations (heap++ext) root a b same edge point := by
  obtain ⟨rl,f,hr,⟨sg,ls,hsg,⟨u,v,hp,hu,hv⟩,⟨x,y,hrels,hx,hy⟩⟩,hf⟩ := rel
  exact ⟨rl,f,lookup_extend hr ext,⟨sg,ls,lookup_extend hsg ext,
    ⟨u,v,lookup_extend hp ext,lookup_extend hu ext,lookup_extend hv ext⟩,
    ⟨x,y,lookup_extend hrels ext,lookup_extend hx ext,lookup_extend hy ext⟩⟩,lookup_extend hf ext⟩

private theorem appended_at (heap ext : NaturalHeap) (i : ℕ) :
    (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1500000 in
private theorem pack {heap : NaturalHeap} {r : Registers ℕ} {a b same edge : Bool} {fa fb sa sb la lb pa pb : ℕ}
    (left : heap[r.a]?=some (.pair pa fa)) (right : heap[r.b]?=some (.pair pb fb))
    (first : heap[fa]?=some (.pair sa la)) (second : heap[fb]?=some (.pair sb lb))
    (sign1 : heap[sa]?=some (.flag a)) (sign2 : heap[sb]?=some (.flag b))
    (port : heap[r.d]?=some (.flag same)) (arc : heap[r.c]?=some (.flag edge)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Relations (heap++ext) root a b same edge (same && (a==b)) ∧
      NaturalRun program (pointSteps same+8) (state heap r [] tape 2) []
        (state (heap++ext) (args.set .r3 root) [] tape 11) := by
  let rel : Cell ℕ := .pair r.d r.c
  let mid := heap++[rel]
  let args := (((r.set .r2 heap.length).set .r0 sa).set .r1 sb)
  have afterLeft : mid[r.a]?=some (.pair pa fa) := lookup_extend left [rel]
  have afterRight : mid[r.b]?=some (.pair pb fb) := lookup_extend right [rel]
  have afterFirst : mid[fa]?=some (.pair sa la) := lookup_extend first [rel]
  have afterSecond : mid[fb]?=some (.pair sb lb) := lookup_extend second [rel]
  have setup : NaturalRun program 5 (state heap r [] tape 2) [] (state mid args [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      rel,mid,args,afterLeft,afterRight,afterFirst,afterSecond]
  let point : Cell ℕ := .flag (same && (a==b))
  let ready := args.set .r3 mid.length
  let grown := mid++[point]
  have call := point_call (r:=args) (lookup_extend sign1 [rel]) (lookup_extend sign2 [rel]) (lookup_extend port [rel]) tape
  let i := grown.length
  let nodes : NaturalHeap := [.pair sa sb,.pair i heap.length,.pair (i+1) mid.length]
  let packed := (ready.set .r0 i).set .r2 (i+1)
  have finish : NaturalRun program 3 (state grown ready [] tape 8) []
      (state (grown++nodes) (packed.set .r3 (i+2)) [] tape 11) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      nodes,i,packed,ready,args,List.append_assoc,Nat.add_assoc]
  have beforePoint : (mid++[point])[mid.length]?=some point := by simp
  have relPair : (grown++nodes)[heap.length]?=some rel :=
    lookup_extend (lookup_extend (by simp [mid]) [point]) nodes
  have relations : Relations (grown++nodes) (i+2) a b same edge (same && (a==b)) :=
    ⟨i+1,mid.length,appended_at grown nodes 2,
      ⟨i,heap.length,appended_at grown nodes 1,
        ⟨sa,sb,by simp [i,nodes],by simpa only [grown,mid,List.append_assoc] using lookup_extend sign1 ([rel]++[point]++nodes),
          by simpa only [grown,mid,List.append_assoc] using lookup_extend sign2 ([rel]++[point]++nodes)⟩,
        ⟨r.d,r.c,relPair,by simpa only [grown,mid,List.append_assoc] using lookup_extend port ([rel]++[point]++nodes),
          by simpa only [grown,mid,List.append_assoc] using lookup_extend arc ([rel]++[point]++nodes)⟩⟩,
      lookup_extend beforePoint nodes⟩
  refine ⟨[rel]++[point]++nodes,packed,i+2,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using relations
  · have count : 5+(pointSteps same+3)=pointSteps same+8 := by omega
    rw [← count]
    simpa only [grown,mid,ready,point,List.append_assoc,List.nil_append] using append_run setup (append_run call finish)

theorem natural_relations {n L : ℕ} {D : Input n} {a b : Node n L} {heap : NaturalHeap} {r : Registers ℕ}
    (left : Descriptor heap r.a (.inl a)) (right : Descriptor heap r.b (.inl b))
    (graph : GraphAdjacencyProgram.Matrix heap r.c (rows D)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      Relations (heap++ext) root a.1.2 b.1.2 (decide (a.1.1=b.1.1)) (result D b.1.1 a.1.1) (decide (a.1=b.1)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 11) ∧
      k ≤ instructionBound n := by
  rcases a with ⟨⟨p,sa⟩,la⟩
  rcases b with ⟨⟨q,sb⟩,lb⟩
  obtain ⟨i,a,fa,al,lp,pr,af,ta,_⟩ := left
  obtain ⟨j,b,fb,bl,rp,qr,bf,tb,_⟩ := right
  obtain ⟨ee,eq,equals,eqRun⟩ := equality_call lp rp pr qr tape
  let mid := heap++ee
  let withEq := r.set .r3 eq
  obtain ⟨er,edge,k,adjacent,adjRun,bound⟩ := adjacency_call (r:=withEq) (lookup_extend lp ee) (lookup_extend rp ee)
    (CandidateNodeListsProgram.port_extend pr ee) (CandidateNodeListsProgram.port_extend qr ee)
    (GraphAdjacencyProgram.matrix_extend graph ee) tape
  let grown := mid++er
  let packed := withEq.set .r2 edge
  obtain ⟨ep,args,root,out,finish⟩ := pack (r:=packed) (lookup_extend (lookup_extend lp ee) er)
    (lookup_extend (lookup_extend rp ee) er) (lookup_extend (lookup_extend af ee) er)
    (lookup_extend (lookup_extend bf ee) er) (lookup_extend (lookup_extend ta ee) er)
    (lookup_extend (lookup_extend tb ee) er) (lookup_extend equals er) adjacent tape
  have eqPoint : (decide (p=q) && (sa==sb))=decide ((p,sa)=(q,sb)) := by
    rw [Bool.eq_iff_iff]
    simp [Prod.ext_iff]
  let e := CandidatePortEqualityProgram.steps p q
  let f := pointSteps (decide (p=q))
  refine ⟨ee++er++ep,args,root,e+4+k+(f+8),?_,?_,?_⟩
  · simpa only [eqPoint,mid,grown,List.append_assoc] using out
  · have count : e+4+(k+(f+8))=e+4+k+(f+8) := by omega
    rw [← count]
    simpa only [mid,grown,e,f,List.append_assoc,List.nil_append] using append_run eqRun (append_run adjRun finish)
  · have limit := CandidatePortEqualityProgram.steps_le p q
    have small : f ≤ 6 := by unfold f pointSteps; split <;> decide
    unfold instructionBound
    omega

end DirectedFlowCutGap.CandidateCoreRelationsProgram
