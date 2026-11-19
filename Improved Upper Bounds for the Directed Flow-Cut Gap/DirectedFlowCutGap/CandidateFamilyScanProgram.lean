import DirectedFlowCutGap.CandidateDemandRowProgram
import DirectedFlowCutGap.RoundInputPackProgram

/-! Materialize all candidate rows on one heap by traversing actual pair and mask lists. -/

namespace DirectedFlowCutGap.CandidateFamilyScanProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow CandidateClosureProvider
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node Network)
open CandidateDemandRowProgram (GraphSizeAt GridAt rowWords graph_extend grid_extend)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge EdgeList edge_extend edgeList_extend)
open RetainedMassTableProgram (TableAt)
open PathCostMaterialization (WordList list_extend)

def Context {n : ℕ} (heap : NaturalHeap) (root : ℕ) (D : Input n) (vertices grid bound : Bits) : Prop :=
  ∃ params emptyRow graph rest removal cap,heap[root]?=some (.pair params emptyRow) ∧ heap[params]?=some (.pair graph rest) ∧
    heap[rest]?=some (.pair removal cap) ∧ GraphSizeAt heap graph D vertices ∧ GridAt heap removal D grid ∧
    BoolList heap cap bound ∧ WordList heap emptyRow (List.replicate n [])

theorem context_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {vertices grid bound : Bits}
    (h : Context heap root D vertices grid bound) (ext : NaturalHeap) : Context (heap++ext) root D vertices grid bound := by
  obtain ⟨p,z,g,r,m,b,outer,params,rest,graph,grid,bound,zeros⟩ := h
  exact ⟨p,z,g,r,m,b,lookup_extend outer ext,lookup_extend params ext,lookup_extend rest ext,
    graph_extend graph ext,grid_extend grid ext,boolList_extend bound ext,list_extend zeros ext⟩

noncomputable def selectedRow {n L : ℕ} (D : Input n) (a : PairFlags n) (B : ℕ) (grid : Bits)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) (p : Pair n) : List Bits :=
  if flag a p then rowWords D p L B grid EN E else List.replicate n []

def rowLabel (pc : Fin 3813) : Fin 3877 := ⟨64+pc.val,by omega⟩

def program : Program 3877 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 9 63 63 12
    | 9 => .make .r3 .nil 15
    | 12 => .call 40 13 .r3
    | 13 => .call 24 14 .r1
    | 14 => .make .r3 (.pair .r1 .r3) 15
    | 15 => .ret .r3
    | 24 => .field .r1 .r1 false 25
    | 25 => .branch .r1 63 26 28 63
    | 26 => .field .r3 .r2 true 27
    | 27 => .ret .r3
    | 28 => .field .r0 .r0 false 29
    | 29 => .field .r2 .r2 false 30
    | 30 => .field .r1 .r2 false 31
    | 31 => .field .r2 .r2 true 32
    | 32 => .field .r3 .r2 true 33
    | 33 => .field .r2 .r2 false 34
    | 34 => .call (rowLabel 0) 35 .r3
    | 35 => .ret .r3
    | 40 => .field .r0 .r0 true 41
    | 41 => .field .r1 .r1 true 8
    | _ => .halt
  else if pc.val=68 then .ret .r3
  else ReferenceProgramLabels.instruction rowLabel
    (CandidateDemandRowProgram.program ⟨pc.val-64,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3877

def rowLimit (n L vertices grid bound : ℕ) : ℕ :=
  CandidateDemandRowProgram.instructionBound n L vertices grid bound+18

def instructionBound (n L vertices grid bound : ℕ) : ℕ := (n*n)*rowLimit n L vertices grid bound+4

private theorem slots (pc : Fin 3813) (h : CandidateDemandRowProgram.program pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (CandidateDemandRowProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,rowLabel,show ¬64+pc.val<64 by omega,show 64+pc.val≠68 by omega]

set_option maxHeartbeats 1300000 in
private theorem one_row {n L B : ℕ} {D : Input n} {a : PairFlags n} {p : Pair n}
    {heap : NaturalHeap} {r : Registers ℕ} {key tail bit more : ℕ} {vertices grid bound : Bits}
    (positive : 0<L) (feasible : flag a p=true→CandidateFeasible D.graph p.1 p.2 D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (head : heap[r.a]?=some (.pair key tail)) (label : Edge heap key (labelPair p))
    (atMask : heap[r.b]?=some (.pair bit more)) (atBit : heap[bit]?=some (.flag (flag a p)))
    (context : Context heap r.c D vertices grid bound) (size : value vertices=n) (gridValue : value grid=L)
    (cap : value bound=B) (stack : List (Frame ℕ 3877)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),WordList (heap++ext) root (selectedRow D a B grid EN E p) ∧
      NaturalRun program k (state heap r stack tape 13) [] (state (heap++ext) (r.set .r1 root) stack tape 14) ∧
      k ≤ CandidateDemandRowProgram.instructionBound n L vertices.length grid.length bound.length+12 := by
  obtain ⟨params,emptyRow,graph,rest,g,b,atRoot,atParams,atRest,graphRep,gridRep,boundRep,zeroRep⟩ := context
  let caller : Frame ℕ 3877 := ⟨14,.r1,r⟩
  cases active : flag a p with
  | false =>
    rw [active] at atBit
    refine ⟨[],emptyRow,5,?_,?_,by omega⟩
    · simpa [selectedRow,active] using zeroRep
    · apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,atMask,atBit,atRoot]
  | true =>
    rw [active] at atBit
    let selected := r.set .r1 bit
    let withGraph : Registers ℕ := ⟨key,graph,params,r.d⟩
    let args : Registers ℕ := ⟨key,graph,g,b⟩
    have test : NaturalRun program 3 (state heap r stack tape 13) [] (state heap selected (caller::stack) tape 28) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,atMask,atBit,caller,selected]
    have prep : NaturalRun program 3 (state heap selected (caller::stack) tape 28) []
        (state heap withGraph (caller::stack) tape 31) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        head,atRoot,atParams,selected,withGraph]
    have load : NaturalRun program 3 (state heap withGraph (caller::stack) tape 31) []
        (state heap args (caller::stack) tape 34) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        atParams,atRest,withGraph,args]
    obtain ⟨ext,out,root,k,result,body,limit⟩ := CandidateDemandRowProgram.natural_row (r:=args)
      positive (feasible active) EN E label graphRep gridRep boundRep size gridValue cap tape
    have invoke := ReferenceProgramInvocation.call rowLabel slots (caller:=34) (continuation:=35)
      (result:=.r3) (dst:=.r3) (by rfl) (by rfl) (caller::stack) body
    let stop := state (heap++ext) (args.set .r3 root) (caller::stack) tape 35
    have trace : NaturalRun program (k+2) (state heap args (caller::stack) tape 34) [] stop := by
      simpa [stop,Registers.get,Registers.set] using invoke
    have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) stack tape 14,[],0⟩ := by
      simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,caller]
    refine ⟨ext,root,k+12,by simpa [selectedRow,active] using result,?_,by omega⟩
    have full := append_run test (append_run prep (append_run load (append_run trace (.step ret (.done _)))))
    have count : 3+(3+(3+(k+2+1)))=k+12 := by omega
    rw [← count]
    simpa only [Nat.zero_add,List.nil_append] using full

set_option maxHeartbeats 2100000 in
private theorem scan_return {n L B : ℕ} {D : Input n} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    {pairs : List (Pair n)} {vertices grid bound : Bits} (positive : 0<L)
    (feasible : ∀ p,flag a p=true→CandidateFeasible D.graph p.1 p.2 D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (keys : EdgeList heap r.a (pairs.map labelPair)) (mask : BoolList heap r.b (pairs.map (flag a)))
    (context : Context heap r.c D vertices grid bound) (size : value vertices=n) (gridValue : value grid=L)
    (cap : value bound=B) (caller : Frame ℕ 3877) (stack : List (Frame ℕ 3877)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),TableAt (heap++ext) root (pairs.map (selectedRow D a B grid EN E)) ∧
      NaturalRun program k (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) ∧
      k ≤ pairs.length*rowLimit n L vertices.length grid.length bound.length+3 := by
  induction pairs generalizing heap r caller stack with
  | nil =>
    cases keys with
    | nil empty =>
      refine ⟨[.nil],heap.length,3,.nil (by simp),?_,by simp⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,allocateNatural,Recipe.cell,empty]
  | cons p ps ih =>
    cases keys with
    | @cons _ key tail _ _ head label keys =>
      cases mask with
      | @cons _ bit more _ _ atMask atBit mask =>
        let saved := caller::stack
        let frame : Frame ℕ 3877 := ⟨13,.r3,r⟩
        let smaller := (r.set .r0 tail).set .r1 more
        have enter : NaturalRun program 4 (state heap r saved tape 8) []
            (state heap smaller (frame::saved) tape 8) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
            tagBranch,head,atMask,smaller,frame]
        obtain ⟨et,rowTail,t,tailRep,tailRun,tailBound⟩ := ih (r:=smaller) keys mask context frame saved
        let mid := heap++et
        let withTail := r.set .r3 rowTail
        obtain ⟨eh,rowHead,h,headRep,headRun,headBound⟩ := one_row (r:=withTail) positive (feasible p) EN E
          (lookup_extend head et) (edge_extend label et) (lookup_extend atMask et) (lookup_extend atBit et)
          (context_extend context et) size gridValue cap saved tape
        let grown := mid++eh
        let ready := withTail.set .r1 rowHead
        let cell : Cell ℕ := .pair rowHead rowTail
        have finish : NaturalRun program 2 (state grown ready saved tape 14) []
            (state (grown++[cell]) (caller.saved.set caller.destination grown.length) stack tape caller.continuation) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
            allocateNatural,Recipe.cell,ready,withTail,cell,saved]
        have out : TableAt (grown++[cell]) grown.length ((p::ps).map (selectedRow D a B grid EN E)) := by
          exact .cons (by simp [cell]) (list_extend headRep [cell])
            (RoundInputPackProgram.weights_extend (RoundInputPackProgram.weights_extend tailRep eh) [cell])
        refine ⟨et++eh++[cell],grown.length,4+(t+(h+2)),?_,?_,?_⟩
        · simpa only [grown,mid,List.append_assoc] using out
        · simpa only [grown,mid,List.append_assoc,List.nil_append] using
            append_run enter (append_run tailRun (append_run headRun finish))
        · rw [List.length_cons,Nat.succ_mul]
          unfold rowLimit at tailBound ⊢
          omega

theorem natural_family {n L B : ℕ} {D : Input n} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    {vertices grid bound : Bits} (positive : 0<L)
    (feasible : ∀ p,flag a p=true→CandidateFeasible D.graph p.1 p.2 D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (keys : EdgeList heap r.a ((RetainedMassTableProgram.pairOrder n).map labelPair))
    (mask : BoolList heap r.b (RetainedEpochFromMasks.flags a))
    (context : Context heap r.c D vertices grid bound) (size : value vertices=n) (gridValue : value grid=L)
    (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),TableAt (heap++ext) root
        ((RetainedMassTableProgram.pairOrder n).map (selectedRow D a B grid EN E)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k ≤ instructionBound n L vertices.length grid.length bound.length := by
  let caller : Frame ℕ 3877 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,k,rep,body,limit⟩ := scan_return positive feasible EN E keys mask context size gridValue cap caller [] tape
  rw [RetainedMassTableProgram.pairOrder_length] at limit
  exact ⟨ext,root,k+1,rep,.step enter body,by unfold instructionBound; omega⟩

end DirectedFlowCutGap.CandidateFamilyScanProgram
