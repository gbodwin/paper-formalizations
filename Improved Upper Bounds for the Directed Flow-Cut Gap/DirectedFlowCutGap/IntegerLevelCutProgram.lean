import DirectedFlowCutGap.IntegerLevelVertexProgram

/-!
# Physical scan for an integer midpoint cut

Each call constructs its own graph recovery context from the current
target and the shared graph bundle. Its input row contains stored target
labels and their weights in output order. The result is the exact Boolean
cut mask, allocated tail-first in the same heap.
-/

namespace DirectedFlowCutGap.IntegerLevelCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open IntegerDistanceFromPhysical (encodedRow)

def vertexLabel (pc : Fin 1540) : Fin 1572 := ⟨32+pc.val,by omega⟩

def program : Program 1572 := fun pc =>
  if pc.val < 32 then
    match pc.val with
    | 0 => .call 1 31 .r3
    | 1 => .branch .r1 2 31 31 4
    | 2 => .make .r3 .nil 3
    | 3 => .ret .r3
    | 4 => .field .r3 .r1 false 5
    | 5 => .field .r1 .r1 true 6
    | 6 => .call 1 7 .r1
    | 7 => .call 10 8 .r3
    | 8 => .make .r3 (.pair .r3 .r1) 3
    | 10 => .call 20 11 .r1
    | 11 => .call 24 12 .r3
    | 12 => .field .r2 .r2 true 13
    | 13 => .field .r2 .r2 false 14
    | 14 => .call (vertexLabel 8) 15 .r3
    | 15 => .ret .r3
    | 20 => .field .r1 .r3 false 21
    | 21 => .field .r2 .r2 false 22
    | 22 => .make .r3 (.pair .r1 .r2) 23
    | 23 => .ret .r3
    | 24 => .field .r1 .r2 true 25
    | 25 => .field .r1 .r1 true 26
    | 26 => .field .r3 .r3 true 27
    | 27 => .make .r3 (.pair .r1 .r3) 28
    | 28 => .ret .r3
    | _ => .halt
  else if pc.val=41 then .ret .r3
  else ReferenceProgramLabels.instruction vertexLabel
    (IntegerLevelVertexProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 1572))
    (tape : Bits) (pc : Fin 1572) : NaturalState 1572 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

/-- A target-independent part of the graph call and the two shared words. -/
def InputContext (heap : NaturalHeap) (root : ℕ) (vertices matrix : List Bits)
    (row : List BinaryRational.Fraction) (sw source level : Bits) : Prop :=
  ∃ bundle sl enumRoot mix mat cost sr j,
    heap[root]? = some (.pair bundle sl) ∧ heap[sl]? = some (.pair sr j) ∧
    heap[bundle]? = some (.pair enumRoot mix) ∧ heap[mix]? = some (.pair mat cost) ∧
    GraphDiscoveryProgram.Vertices heap enumRoot vertices ∧ GraphAdjacencyProgram.Matrix heap mat matrix ∧
    OutgoingCostProgram.Context heap cost row sw ∧ BoolList heap sr source ∧ BoolList heap j level

theorem context_extend {heap : NaturalHeap} {root : ℕ} {vertices matrix : List Bits}
    {row : List BinaryRational.Fraction} {sw source level : Bits}
    (h : InputContext heap root vertices matrix row sw source level) (ext : NaturalHeap) :
    InputContext (heap++ext) root vertices matrix row sw source level := by
  obtain ⟨bundle,sl,e,m,mat,cost,sr,j,hp,hsl,hb,hm,he,ha,hc,hs,hj⟩ := h
  exact ⟨bundle,sl,e,m,mat,cost,sr,j,lookup_extend hp ext,lookup_extend hsl ext,
    lookup_extend hb ext,lookup_extend hm ext,GraphDiscoveryProgram.vertices_extend he ext,
    GraphAdjacencyProgram.matrix_extend ha ext,PathCostMaterialization.context_extend hc ext,
    boolList_extend hs ext,boolList_extend hj ext⟩

def fields {n : ℕ} (a : Row n) (label : Fin n → Bits) (positions : List (Fin n)) :
    List (Bits × Bits) :=
  positions.map fun t => (label t,a[t.val].bits)

def flag {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (level : ℕ) (t : Fin n) : Bool :=
  (IntegerLevelCuts.cellTest (EncodedIntegerShortestPaths.distance E adjacency a s t).1 a[t.val] level).1

def steps {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (sw : Bits) (label : Fin n → Bits) (level : Bits) : List (Fin n) → ℕ
  | [] => 3
  | t::ts => steps E adjacency a s sw label level ts +
    IntegerLevelVertexProgram.instructions E adjacency a s t sw label a[t.val].bits level + 24

private theorem vertex_slots (pc : Fin 1540) (h : IntegerLevelVertexProgram.program pc ≠ .halt) :
    program (vertexLabel pc) =
      ReferenceProgramLabels.instruction vertexLabel (IntegerLevelVertexProgram.program pc) := by
  by_cases hp : pc.val=9
  · have eq : pc=9 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,vertexLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠41 by omega]

private theorem join {s u v : NaturalState 1572} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem vertex_return {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level : Bits) (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext heap r.b (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (source : BoolList heap r.c (label s))
    (hw : IntegerLevelVertexProgram.LevelAndWeight heap r.d a[t.val].bits level)
    (caller : Frame ℕ 1572) (stack : List (Frame ℕ 1572)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag (flag E adjacency a s (value level) t)) ∧
      NaturalRun program (IntegerLevelVertexProgram.instructions E adjacency a s t sw label a[t.val].bits level+2)
        (state heap r (caller::stack) tape (vertexLabel 8)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨ext,root,hflag,hrun⟩ := IntegerLevelVertexProgram.natural_vertex E adjacency a s t sw hs label hlabel
    input context source a[t.val].bits level hw tape
  have lift := ReferenceProgramLabels.run vertexLabel IntegerLevelVertexProgram.program program vertex_slots hrun
  have lift := ReferenceProgramStack.run program (caller::stack) lift
  let before := state (heap++ext) (r.set .r3 root) (caller::stack) tape (vertexLabel 9)
  let after := state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (IntegerLevelVertexProgram.instructions E adjacency a s t sw label a[t.val].bits level+1)
      (state heap r (caller::stack) tape (vertexLabel 8)) [] before := by
    simpa [state,before,IntegerLevelVertexProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before = some ⟨after,[],0⟩ := by
    cases r
    simp [before,after,state,program,vertexLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,?_,join body (.step ret (.done after))⟩
  simpa only [flag,value_bits] using hflag

private theorem make_context {heap : NaturalHeap} {r : Registers ℕ} {target weight bundle sl : ℕ}
    (item : heap[r.d]? = some (.pair target weight))
    (shared : heap[r.c]? = some (.pair bundle sl))
    (caller : Frame ℕ 1572) (stack : List (Frame ℕ 1572)) (tape : Bits) :
    NaturalRun program 4 (state heap r (caller::stack) tape 20) []
      (state (heap++[.pair target bundle]) (caller.saved.set caller.destination heap.length) stack tape caller.continuation) := by
  let saved := caller::stack
  let r1 := r.set .r1 target
  let r2 := r1.set .r2 bundle
  let grown := heap++[.pair target bundle]
  let before := state grown (r2.set .r3 heap.length) saved tape 23
  have t20 : tickNatural program (state heap r saved tape 20) = some ⟨state heap r1 saved tape 21,[],0⟩ := by
    simp [r1,state,tickNatural,program,Registers.get,item]
  have t21 : tickNatural program (state heap r1 saved tape 21) = some ⟨state heap r2 saved tape 22,[],0⟩ := by
    cases r
    simp [r1,r2,state,tickNatural,program,Registers.get,Registers.set,shared]
  have t22 : tickNatural program (state heap r2 saved tape 22) = some ⟨before,[],0⟩ := by
    cases r
    simp [before,grown,r1,r2,state,tickNatural,program,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have t23 : tickNatural program before =
      some ⟨state grown (caller.saved.set caller.destination heap.length) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [before,saved,r1,r2,state,tickNatural,program,Registers.get,Registers.set]
  exact .step t20 (.step t21 (.step t22 (.step t23 (.done _))))

private theorem make_args {heap : NaturalHeap} {r : Registers ℕ} {target weight bundle sl sr j : ℕ}
    (item : heap[r.d]? = some (.pair target weight))
    (shared : heap[r.c]? = some (.pair bundle sl)) (words : heap[sl]? = some (.pair sr j))
    (caller : Frame ℕ 1572) (stack : List (Frame ℕ 1572)) (tape : Bits) :
    NaturalRun program 5 (state heap r (caller::stack) tape 24) []
      (state (heap++[.pair j weight]) (caller.saved.set caller.destination heap.length) stack tape caller.continuation) := by
  let saved := caller::stack
  let r1 := r.set .r1 sl
  let r2 := r1.set .r1 j
  let r3 := r2.set .r3 weight
  let grown := heap++[.pair j weight]
  let before := state grown (r3.set .r3 heap.length) saved tape 28
  have t24 : tickNatural program (state heap r saved tape 24) = some ⟨state heap r1 saved tape 25,[],0⟩ := by
    simp [r1,state,tickNatural,program,Registers.get,shared]
  have t25 : tickNatural program (state heap r1 saved tape 25) = some ⟨state heap r2 saved tape 26,[],0⟩ := by
    cases r
    simp [r1,r2,state,tickNatural,program,Registers.get,Registers.set,words]
  have t26 : tickNatural program (state heap r2 saved tape 26) = some ⟨state heap r3 saved tape 27,[],0⟩ := by
    cases r
    simp [r1,r2,r3,state,tickNatural,program,Registers.get,Registers.set,item]
  have t27 : tickNatural program (state heap r3 saved tape 27) = some ⟨before,[],0⟩ := by
    cases r
    simp [before,grown,r1,r2,r3,state,tickNatural,program,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have t28 : tickNatural program before =
      some ⟨state grown (caller.saved.set caller.destination heap.length) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [before,saved,r1,r2,r3,state,tickNatural,program,Registers.get,Registers.set]
  exact .step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.done _)))))

private theorem test_one {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level : Bits) (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (context : InputContext heap r.c (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level)
    (hit : ∃ tr w, heap[r.d]? = some (.pair tr w) ∧ BoolList heap tr (label t) ∧ BoolList heap w a[t.val].bits)
    (caller : Frame ℕ 1572) (stack : List (Frame ℕ 1572)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag (flag E adjacency a s (value level) t)) ∧
      NaturalRun program (IntegerLevelVertexProgram.instructions E adjacency a s t sw label a[t.val].bits level+17)
        (state heap r (caller::stack) tape 10) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨bundle,sl,e,m,mat,cost,sr,j,hp,hsl,hb,hm,he,ha,hc,hsrc,hj⟩ := context
  obtain ⟨tr,w,hi,ht,hw⟩ := hit
  let saved := caller::stack
  let contextCells : NaturalHeap := [.pair tr bundle]
  let mid := heap++contextCells
  let pairCells : NaturalHeap := [.pair j w]
  let grown := mid++pairCells
  let rb := r.set .r1 heap.length
  let rf := rb.set .r3 mid.length
  let words := rf.set .r2 sl
  let args := words.set .r2 sr
  let fctx : Frame ℕ 1572 := ⟨11,.r1,r⟩
  let fargs : Frame ℕ 1572 := ⟨12,.r3,rb⟩
  let ftest : Frame ℕ 1572 := ⟨15,.r3,args⟩
  have callContext : tickNatural program (state heap r saved tape 10) =
      some ⟨state heap r (fctx::saved) tape 20,[],0⟩ := rfl
  have hcontext := make_context hi hp fctx saved tape
  have callArgs : tickNatural program (state mid rb saved tape 11) =
      some ⟨state mid rb (fargs::saved) tape 24,[],0⟩ := rfl
  have getItem : mid[rb.d]? = some (.pair tr w) := by
    cases r
    exact lookup_extend hi contextCells
  have getFields : mid[rb.c]? = some (.pair bundle sl) := by
    cases r
    exact lookup_extend hp contextCells
  have hargs := make_args getItem getFields (lookup_extend hsl contextCells) fargs saved tape
  let prep := contextCells++pairCells
  have shape : grown=heap++prep := by simp only [grown,mid,prep,List.append_assoc]
  have t12 : tickNatural program (state grown rf saved tape 12) =
      some ⟨state grown words saved tape 13,[],0⟩ := by
    have h := lookup_extend hp prep
    rw [← shape] at h
    cases r
    simp [rf,rb,words,state,tickNatural,program,Registers.get,Registers.set,h]
  have t13 : tickNatural program (state grown words saved tape 13) =
      some ⟨state grown args saved tape 14,[],0⟩ := by
    have h := lookup_extend hsl prep
    rw [← shape] at h
    cases r
    simp [rf,rb,words,args,state,tickNatural,program,Registers.get,Registers.set,h]
  have callVertex : tickNatural program (state grown args saved tape 14) =
      some ⟨state grown args (ftest::saved) tape (vertexLabel 8),[],0⟩ := rfl
  have hg : GraphDiscoveryProgram.GlobalContext grown args.b (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t) := by
    refine ⟨tr,bundle,e,m,mat,cost,?_,?_,?_,?_,?_,?_,?_⟩
    · have first : mid[heap.length]? = some (.pair tr bundle) := by simp [mid,contextCells]
      cases r
      exact lookup_extend first pairCells
    all_goals rw [shape]
    · exact lookup_extend hb prep
    · exact lookup_extend hm prep
    · exact boolList_extend ht prep
    · exact GraphDiscoveryProgram.vertices_extend he prep
    · exact GraphAdjacencyProgram.matrix_extend ha prep
    · exact PathCostMaterialization.context_extend hc prep
  have enumeration : GraphDiscoveryProgram.Vertices grown args.a (E.vertices.map label) := by
    rw [shape]
    cases r
    exact GraphDiscoveryProgram.vertices_extend input prep
  have sourceWord : BoolList grown args.c (label s) := by
    rw [shape]
    cases r
    exact boolList_extend hsrc prep
  have operands : IntegerLevelVertexProgram.LevelAndWeight grown args.d a[t.val].bits level := by
    refine ⟨j,w,?_,?_,?_⟩
    · cases r
      change grown[mid.length]? = some (.pair j w)
      simp [grown,pairCells]
    · rw [shape]
      exact boolList_extend hw prep
    · rw [shape]
      exact boolList_extend hj prep
  obtain ⟨ext,root,hflag,hvertex⟩ := vertex_return E adjacency a s t sw hs label hlabel level
    enumeration hg sourceWord operands ftest saved tape
  have ret : tickNatural program (state (grown++ext) (args.set .r3 root) saved tape 15) =
      some ⟨state (grown++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [args,words,rf,rb,saved,state,tickNatural,program,Registers.get,Registers.set]
  refine ⟨prep++ext,root,?_,?_⟩
  · simpa only [shape,List.append_assoc] using hflag
  · have trace := NaturalRun.step callContext (join hcontext (NaturalRun.step callArgs
      (join hargs (NaturalRun.step t12 (NaturalRun.step t13
        (NaturalRun.step callVertex (join hvertex (.step ret (.done _)))))))))
    convert trace using 1 <;> first | rfl | omega | simp only [shape,List.append_assoc]

theorem scan_subroutine {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s : Fin n) (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level : Bits) (positions : List (Fin n)) (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (targets : WordPairTableRead.Table heap r.b (fields a label positions))
    (context : InputContext heap r.c (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level)
    (caller : Frame ℕ 1572) (stack : List (Frame ℕ 1572)) (tape : Bits) :
    ∃ ext root, BoolList (heap++ext) root (positions.map (flag E adjacency a s (value level))) ∧
      NaturalRun program (steps E adjacency a s sw label level positions)
        (state heap r (caller::stack) tape 1) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction positions generalizing heap r caller stack with
  | nil =>
    change WordPairTableRead.Table heap r.b [] at targets
    cases targets with
    | nil hn =>
      let saved := caller::stack
      let fresh := heap.length
      let grown := heap++[.nil]
      let before := state grown (r.set .r3 fresh) saved tape 3
      have branch : tickNatural program (state heap r saved tape 1) =
          some ⟨state heap r saved tape 2,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hn]
      have alloc : tickNatural program (state heap r saved tape 2) =
          some ⟨before,[],0⟩ := by
        simp [before,grown,fresh,state,tickNatural,program,allocateNatural,Recipe.cell]
      have ret : tickNatural program before =
          some ⟨state grown (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,saved,state,tickNatural,program,Registers.get,Registers.set]
      exact ⟨[.nil],fresh,.nil (by simp [fresh]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons t ts ih =>
    change WordPairTableRead.Table heap r.b ((label t,a[t.val].bits)::fields a label ts) at targets
    cases targets with
    | @cons _ item tail target w _ _ _ hpair hitem ht hw htail =>
      let saved := caller::stack
      let withItem := r.set .r3 item
      let tailArgs := withItem.set .r1 tail
      let frame : Frame ℕ 1572 := ⟨7,.r1,tailArgs⟩
      have branch : tickNatural program (state heap r saved tape 1) =
          some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hpair]
      have load : tickNatural program (state heap r saved tape 4) =
          some ⟨state heap withItem saved tape 5,[],0⟩ := by
        simp [withItem,state,tickNatural,program,Registers.get,hpair]
      have advance : tickNatural program (state heap withItem saved tape 5) =
          some ⟨state heap tailArgs saved tape 6,[],0⟩ := by
        cases r
        simp [withItem,tailArgs,state,tickNatural,program,Registers.get,Registers.set,hpair]
      have callTail : tickNatural program (state heap tailArgs saved tape 6) =
          some ⟨state heap tailArgs (frame::saved) tape 1,[],0⟩ := rfl
      have tailEnumeration : GraphDiscoveryProgram.Vertices heap tailArgs.a (E.vertices.map label) := by
        cases r
        exact input
      have tailTable : WordPairTableRead.Table heap tailArgs.b (fields a label ts) := by
        cases r
        exact htail
      have tailContext : InputContext heap tailArgs.c (E.vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level := by
        cases r
        exact context
      obtain ⟨et,rest,hrest,hrun⟩ := ih tailEnumeration tailTable tailContext frame saved
      let mid := heap++et
      let headArgs := tailArgs.set .r1 rest
      let headFrame : Frame ℕ 1572 := ⟨8,.r3,headArgs⟩
      have callHead : tickNatural program (state mid headArgs saved tape 7) =
          some ⟨state mid headArgs (headFrame::saved) tape 10,[],0⟩ := rfl
      have headEnumeration : GraphDiscoveryProgram.Vertices mid headArgs.a (E.vertices.map label) := by
        cases r
        exact GraphDiscoveryProgram.vertices_extend input et
      have headContext : InputContext mid headArgs.c (E.vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level := by
        cases r
        exact context_extend context et
      have headItem : mid[headArgs.d]? = some (.pair target w) := by
        cases r
        exact lookup_extend hitem et
      obtain ⟨eh,bit,hbit,hhead⟩ := test_one E adjacency a s t sw hs label hlabel level
        headEnumeration headContext ⟨target,w,headItem,boolList_extend ht et,boolList_extend hw et⟩ headFrame saved tape
      let grown := mid++eh
      let fresh := grown.length
      let cell : Cell ℕ := .pair bit rest
      let outHeap := grown++[cell]
      let newRegs := headArgs.set .r3 bit
      let last := state outHeap (newRegs.set .r3 fresh) saved tape 3
      have alloc : tickNatural program (state grown newRegs saved tape 8) = some ⟨last,[],0⟩ := by
        cases r
        simp [last,outHeap,cell,fresh,newRegs,headArgs,tailArgs,withItem,state,tickNatural,program,
          Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program last =
          some ⟨state outHeap (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [last,saved,newRegs,headArgs,tailArgs,withItem,state,tickNatural,program,Registers.get,Registers.set]
      have result : BoolList outHeap fresh ((t::ts).map (flag E adjacency a s (value level))) := by
        apply BoolList.cons (head := bit) (tail := rest)
        · simp [outHeap,fresh,cell]
        · exact lookup_extend hbit [cell]
        · exact boolList_extend (boolList_extend hrest eh) [cell]
      refine ⟨et++eh++[cell],fresh,?_,?_⟩
      · simpa only [outHeap,grown,mid,List.append_assoc] using result
      · have trace := NaturalRun.step branch (NaturalRun.step load (NaturalRun.step advance
            (NaturalRun.step callTail (join hrun (NaturalRun.step callHead (join hhead
              (.step alloc (.step ret (.done _)))))))))
        simp only [steps]
        convert trace using 1 <;> first | rfl | omega | simp only [outHeap,grown,mid,List.append_assoc]

theorem mask_value {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (j : ℕ) :
    (List.finRange n).map (flag E adjacency a s j) = (EncodedRoundingInput.cutFlags E adjacency a s j).1.toList := by
  have h : Vector.ofFn (flag E adjacency a s j) = (EncodedRoundingInput.cutFlags E adjacency a s j).1 := by
    rw [EncodedRoundingInput.cutFlags,EncodedRoundingInput.tabulate_value]
    rfl
  simpa only [Vector.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def] using congrArg Vector.toList h

def instructionBound (n W S : ℕ) : ℕ :=
  n*(IntegerLevelVertexProgram.instructionBound n W S+24)+4

theorem steps_le {n W : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i, value (label i)=i.val) (level : Bits)
    (hW : 1 ≤ W) (hsw : sw.length ≤ W) (labels : ∀ i, (label i).length ≤ W)
    (hrow : ∀ i : Fin n, a[i.val].bits.length ≤ W) (hj : level.length ≤ W) :
    steps E adjacency a s sw label level (List.finRange n) + 1 ≤ instructionBound n W sw.length := by
  let cap := IntegerLevelVertexProgram.instructionBound n W sw.length
  have h (xs : List (Fin n)) : steps E adjacency a s sw label level xs ≤ xs.length*(cap+24)+3 := by
    induction xs with
    | nil => simp [steps]
    | cons t ts ih =>
      have head := IntegerLevelVertexProgram.instructions_le E adjacency a s t sw hs label hlabel
        a[t.val].bits level hW hsw labels hrow (hrow t) hj
      change _+1 ≤ cap at head
      simp only [steps,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [instructionBound,List.length_finRange,Nat.add_assoc] using
    Nat.add_le_add_right (h (List.finRange n)) 1

theorem natural_cut {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s : Fin n) (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level tape : Bits)
    (input : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (targets : WordPairTableRead.Table heap r.b (fields a label (List.finRange n)))
    (context : InputContext heap r.c (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level) :
    ∃ ext root, BoolList (heap++ext) root (EncodedRoundingInput.cutFlags E adjacency a s (value level)).1.toList ∧
      NaturalRun program (steps E adjacency a s sw label level (List.finRange n)+1)
        (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 31) := by
  let frame : Frame ℕ 1572 := ⟨31,.r3,r⟩
  obtain ⟨ext,root,hrep,body⟩ := scan_subroutine E adjacency a s sw hs label hlabel level
    (List.finRange n) input targets context frame [] tape
  have call : tickNatural program (state heap r [] tape 0) =
      some ⟨state heap r [frame] tape 1,[],0⟩ := rfl
  rw [mask_value] at hrep
  exact ⟨ext,root,hrep,.step call body⟩

private theorem at_entry (s : NaturalState 1572) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_cut {n H A W : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (level : Bits)
    (hW : 1 ≤ W) (hsw : sw.length ≤ W) (labels : ∀ i, (label i).length ≤ W)
    (hrow : ∀ i : Fin n, a[i.val].bits.length ≤ W) (hj : level.length ≤ W)
    (initial : BitState 1572) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      (E.vertices.map label))
    (targets : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (fields a label (List.finRange n)))
    (context : InputContext (eraseState initial).heap (eraseState initial).registers.c (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label s) level) :
    ∃ charge out, Run program (steps E adjacency a s sw label level (List.finRange n)+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (EncodedRoundingInput.cutFlags E adjacency a s (value level)).1.toList ∧
      out.source = initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=31 ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap++ext) ∧ (attempt program out).result=none ∧
      charge + (attempt program out).operations ≤ completeBound 1572 H A (instructionBound n W sw.length) := by
  let old := eraseState initial
  obtain ⟨ext,root,hrep,body⟩ := natural_cut E adjacency a s sw hs label hlabel level old.source input targets context
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 31
  have hrun : NaturalRun program (steps E adjacency a s sw label level (List.finRange n)+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have halt : tickNatural program final = none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded hrun halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]
    exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have hsteps := steps_le E adjacency a s sw hs label hlabel level hW hsw labels hrow hj
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.IntegerLevelCutProgram
