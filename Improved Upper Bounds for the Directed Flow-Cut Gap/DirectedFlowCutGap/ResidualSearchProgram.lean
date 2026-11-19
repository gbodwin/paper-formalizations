import DirectedFlowCutGap.ResidualSearchData

/-!
# Physical search of the computed residual graph

The program computes the adjacency matrix from retained signed flow cells.
It constructs the graph-search context around that same matrix root and runs
the existing fixed predecessor search. The input includes vertex words,
source and sink words, and the complete pair list in their stored layouts.
-/

namespace DirectedFlowCutGap.ResidualSearchProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open GraphDiscoveryProgram (Vertices vertices_extend)
open SupportRecoveryProgram (StoredGlobalContext SupportContext)
open ResidualRowProgram (Entry)
open ResidualMatrixProgram (StoredTable)
open BinarySigned (Canonical)

def matrixLabel (pc : Fin 92) : Fin 388 := ⟨16+pc.val,by omega⟩
def searchLabel (pc : Fin 280) : Fin 388 := ⟨108+pc.val,by omega⟩

def program : Program 388 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (matrixLabel 14) 1 .r0
    | 1 => .call 6 2 .r3
    | 2 => .move .r0 .r1 3
    | 3 => .move .r1 .r3 4
    | 4 => .call (searchLabel 270) 5 .r3
    | 6 => .field .r2 .r3 true 7
    | 7 => .make .r0 (.pair .r0 .r2) 8
    | 8 => .make .r0 (.pair .r1 .r0) 9
    | 9 => .field .r2 .r3 false 10
    | 10 => .make .r3 (.pair .r2 .r0) 11
    | 11 => .ret .r3
    | _ => .halt
  else if h : pc.val<108 then
    if pc.val=31 then .ret .r3
    else ReferenceProgramLabels.instruction matrixLabel
      (ResidualMatrixProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=387 then .ret .r3
  else ReferenceProgramLabels.instruction searchLabel
    (SupportRecoveryProgram.program ⟨pc.val-108,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 388))
    (tape : Bits) (pc : Fin 388) : NaturalState 388 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def Endpoints (heap : NaturalHeap) (root : ℕ) (target : Bits) (es : List (Bits×Bits)) : Prop :=
  ∃ word edges,heap[root]?=some (.pair word edges) ∧ BoolList heap word target ∧ EdgeList heap edges es

theorem endpoints_extend {heap : NaturalHeap} {root : ℕ} {target : Bits} {es : List (Bits×Bits)}
    (input : Endpoints heap root target es) (extra : NaturalHeap) :
    Endpoints (heap++extra) root target es := by
  obtain ⟨word,edges,hp,hw,he⟩ := input
  exact ⟨word,edges,lookup_extend hp extra,boolList_extend hw extra,edgeList_extend he extra⟩

private theorem matrix_slots (pc : Fin 92) (h : ResidualMatrixProgram.program pc≠.halt) :
    program (matrixLabel pc) =
      ReferenceProgramLabels.instruction matrixLabel (ResidualMatrixProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,matrixLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<108 by omega,
      show 16+pc.val≠31 by omega]

private theorem search_slots (pc : Fin 280) (h : SupportRecoveryProgram.program pc≠.halt) :
    program (searchLabel pc) =
      ReferenceProgramLabels.instruction searchLabel (SupportRecoveryProgram.program pc) := by
  by_cases hp : pc.val=279
  · have eq : pc=279 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,searchLabel,show ¬108+pc.val<16 by omega,show ¬108+pc.val<108 by omega,
      show 108+pc.val≠387 by omega]

private theorem join {s u v : NaturalState 388} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem matrix_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1) (tape : Bits) :
    ∃ ext root,GraphAdjacencyProgram.Matrix (heap++ext) root (ResidualMatrixProgram.flags xs) ∧
      NaturalRun program (ResidualMatrixProgram.steps xs+3) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  obtain ⟨ext,root,hrep,body⟩ := ResidualMatrixProgram.natural_matrix input canonical tape
  let frame : Frame ℕ 388 := ⟨1,.r0,r⟩
  let before := state (heap++ext) (r.set .r3 root) [frame] tape (matrixLabel 15)
  have call : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape (matrixLabel 14),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run matrixLabel ResidualMatrixProgram.program program matrix_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualMatrixProgram.steps xs+1)
      (state heap r [frame] tape (matrixLabel 14)) [] before := by
    simpa [before,state,ResidualMatrixProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    cases r
    simp [before,frame,state,program,matrixLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,hrep,?_⟩
  exact .step call (join trace (.step ret (.done _)))

private theorem prepare_context {heap : NaturalHeap} {r : Registers ℕ} {vs : List Bits}
    {adj : List Bits} {es : List (Bits×Bits)} {target : Bits}
    (hm : GraphAdjacencyProgram.Matrix heap r.a adj) (hv : Vertices heap r.b vs)
    (hends : Endpoints heap r.d target es) (tape : Bits) :
    ∃ ext root,StoredGlobalContext (heap++ext) root vs adj es target ∧
      NaturalRun program 7 (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r3 root) [] tape 2) := by
  obtain ⟨word,edgeList,hpair,hword,hedges⟩ := hends
  let p := heap.length
  let m : Cell ℕ := .pair r.a edgeList
  let b : Cell ℕ := .pair r.b p
  let g : Cell ℕ := .pair word (p+1)
  let saved : List (Frame ℕ 388) := [⟨2,.r3,r⟩]
  let re := r.set .r2 edgeList
  let rm := re.set .r0 p
  let rb := rm.set .r0 (p+1)
  let rt := rb.set .r2 word
  let rg := rt.set .r3 (p+2)
  let hm' := heap++[m]
  let hb' := heap++[m,b]
  let hg' := heap++[m,b,g]
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r saved tape 6,[],0⟩ := rfl
  have edge : tickNatural program (state heap r saved tape 6)=some ⟨state heap re saved tape 7,[],0⟩ := by
    simp [re,state,program,tickNatural,Registers.get,hpair]
  have matrix : tickNatural program (state heap re saved tape 7)=some ⟨state hm' rm saved tape 8,[],0⟩ := by
    cases r
    simp [re,rm,hm',m,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have bundle : tickNatural program (state hm' rm saved tape 8)=some ⟨state hb' rb saved tape 9,[],0⟩ := by
    cases r
    simp [re,rm,rb,hm',hb',b,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have target : tickNatural program (state hb' rb saved tape 9)=some ⟨state hb' rt saved tape 10,[],0⟩ := by
    have hp := lookup_extend hpair [m,b]
    cases r
    simp [hp,re,rm,rb,rt,hb',state,program,tickNatural,Registers.get,Registers.set]
  have whole : tickNatural program (state hb' rt saved tape 10)=some ⟨state hg' rg saved tape 11,[],0⟩ := by
    cases r
    simp [re,rm,rb,rt,rg,hb',hg',g,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have ret : tickNatural program (state hg' rg saved tape 11)=
      some ⟨state hg' (r.set .r3 (p+2)) [] tape 2,[],0⟩ := by
    cases r
    simp [re,rm,rb,rt,rg,saved,state,program,tickNatural,Registers.get,Registers.set]
  have rootLookup : hg'[p+2]?=some (.pair word (p+1)) := by
    simp [hg',p,g]
  have bundleLookup : hg'[p+1]?=some (.pair r.b p) := by
    simp [hg',p,b]
  have matrixLookup : hg'[p]?=some (.pair r.a edgeList) := by
    simp [hg',p,m]
  refine ⟨[m,b,g],p+2,⟨word,p+1,r.b,p,rootLookup,bundleLookup,
    boolList_extend hword _,vertices_extend hv _,r.a,edgeList,matrixLookup,
    GraphAdjacencyProgram.matrix_extend hm _,edgeList_extend hedges _⟩,?_⟩
  exact .step enter (.step edge (.step matrix (.step bundle (.step target (.step whole (.step ret (.done _)))))))

private theorem search_call {heap : NaturalHeap} {r : Registers ℕ} {vs adj : List Bits}
    {es : List (Bits×Bits)} {source target : Bits}
    (N : ℕ) (hv : Vertices heap r.a vs) (ctx : StoredGlobalContext heap r.b vs adj es target)
    (hs : BoolList heap r.c source) (rows : N ≤ adj.length)
    (cols : ∀ i (hi : i<N),N ≤ (adj[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    ∃ ext root,EdgeList (heap++ext) root (SupportRecoveryProgram.search vs adj es source target) ∧
      NaturalRun program (SupportRecoveryProgram.searchSteps vs adj es source target+3)
        (state heap r [] tape 4) [] (state (heap++ext) (r.set .r3 root) [] tape 5) := by
  let small := SupportRecoveryProgram.state heap heap.length r.a r.b r.c r.d [] tape 270
  obtain ⟨ext,root,_,body,hrep⟩ := SupportRecoveryProgram.search_high N small rfl rfl rfl
    hv ctx hs rows cols labels endLabel
  let frame : Frame ℕ 388 := ⟨5,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) [frame] tape (searchLabel 279)
  have call : tickNatural program (state heap r [] tape 4)=
      some ⟨state heap r [frame] tape (searchLabel 270),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run searchLabel SupportRecoveryProgram.program program search_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (SupportRecoveryProgram.searchSteps vs adj es source target+1)
      (state heap r [frame] tape (searchLabel 270)) [] before := by
    cases r
    simpa [before,small,state,SupportRecoveryProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,Registers.set] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) [] tape 5,[],0⟩ := by
    cases r
    simp [before,frame,state,program,searchLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,hrep,.step call (join trace (.step ret (.done _)))⟩

def steps (xs : List (List Entry)) (vs : List Bits) (es : List (Bits×Bits)) (source target : Bits) : ℕ :=
  ResidualMatrixProgram.steps xs + SupportRecoveryProgram.searchSteps vs
    (ResidualMatrixProgram.flags xs) es source target + 15

theorem natural_path {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)} {vs : List Bits}
    {es : List (Bits×Bits)} {source target : Bits} (N : ℕ)
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (hv : Vertices heap r.b vs) (hs : BoolList heap r.c source)
    (ends : Endpoints heap r.d target es) (rows : N ≤ (ResidualMatrixProgram.flags xs).length)
    (cols : ∀ i (hi : i<N),N ≤ ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (root : ℕ),EdgeList (heap++ext) root
      (SupportRecoveryProgram.search vs (ResidualMatrixProgram.flags xs) es source target) ∧
      NaturalRun program (steps xs vs es source target) (state heap r [] tape 0) []
        (state (heap++ext) (out.set .r3 root) [] tape 5) := by
  obtain ⟨em,matrix,hm,mt⟩ := matrix_call input canonical tape
  let mid := heap++em
  let received := r.set .r0 matrix
  have vm : Vertices mid received.b vs := by
    simpa only [mid,received,Registers.set] using vertices_extend hv em
  have ep : Endpoints mid received.d target es := by
    simpa only [mid,received,Registers.set] using endpoints_extend ends em
  have mm : GraphAdjacencyProgram.Matrix mid received.a (ResidualMatrixProgram.flags xs) := hm
  obtain ⟨ec,context,hcontext,ct⟩ := prepare_context mm vm ep tape
  let grown := mid++ec
  let ready := received.set .r3 context
  let first := ready.set .r0 r.b
  let args := first.set .r1 context
  have m0 : tickNatural program (state grown ready [] tape 2)=some ⟨state grown first [] tape 3,[],0⟩ := rfl
  have m1 : tickNatural program (state grown first [] tape 3)=some ⟨state grown args [] tape 4,[],0⟩ := rfl
  have vertex : Vertices grown args.a vs := vertices_extend vm ec
  have ctx : StoredGlobalContext grown args.b vs (ResidualMatrixProgram.flags xs) es target := hcontext
  have sourceRep : BoolList grown args.c source := boolList_extend (boolList_extend hs em) ec
  obtain ⟨esuffix,root,hrep,search⟩ := search_call N vertex ctx sourceRep rows cols labels endLabel tape
  refine ⟨em++ec++esuffix,args,root,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using hrep
  · have trace := join mt (join ct (.step m0 (.step m1 search)))
    simp only [steps]
    convert trace using 1 <;> first | rfl | omega | simp only [mid,grown,List.append_assoc]

open IntegralNetworkFlow
open ResidualMatrixProgram (ValueTable)
open ResidualSearchData (PathResult pairs)
open SupportRecoveryProgram (WordBound EdgeWidths)
open SupportSearchEncoding (encodeEdge)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

def instructionBound (n B W : ℕ) : ℕ :=
  ResidualMatrixProgram.instructionBound n n B+SupportRecoveryProgram.searchCap n (n*n) W n+14

private theorem value_steps_le (f : Flow c s t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1) {B : ℕ}
    (capWidths : ∀ row ∈ xs,∀ e ∈ row,e.2.length≤B)
    (amountWidths : ∀ u v,(max (c u v) (c v u)).size≤B) :
    ResidualMatrixProgram.steps xs+1 ≤ ResidualMatrixProgram.instructionBound n n B := by
  have hxs : xs.length=n := values.length_eq.trans List.length_finRange
  have width (row : List Entry) (hrow : row ∈ xs) :
      row.length=n ∧ ∀ e ∈ row,e.1.magnitude.length≤B ∧ e.2.length≤B := by
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hrow
    have hu : i < (List.finRange n).length := by rwa [← values.length_eq]
    have rel := values.get hi hu
    refine ⟨rel.length_eq.trans List.length_finRange,?_⟩
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
    have hv : j < (List.finRange n).length := by rwa [← rel.length_eq]
    have field := rel.get hj hv
    exact ⟨(ResidualCapacityProgram.amount_width f _ _ _ field.1 (canonical _ hrow _ he)).trans
      (amountWidths _ _),capWidths _ hrow _ he⟩
  simpa only [hxs] using ResidualMatrixProgram.steps_le xs n B width

private theorem at_entry (s : NaturalState 388) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_path {H A B W : ℕ} (f : Flow c s t) (different : s≠t)
    (xs : List (List Entry)) (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (capWidths : ∀ row ∈ xs,∀ e ∈ row,e.2.length≤B)
    (amountWidths : ∀ u v,(max (c u v) (c v u)).size≤B)
    (E : ResidualSearch.Enumeration (Fin n)) (label : Fin n → Bits)
    (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (initial : BitState 388) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (vertices : Vertices (eraseState initial).heap (eraseState initial).registers.b (E.vertices.map label))
    (sourceRep : BoolList (eraseState initial).heap (eraseState initial).registers.c source)
    (ends : Endpoints (eraseState initial).heap (eraseState initial).registers.d
      (label t) ((pairs n).map (encodeEdge label))) :
    ∃ path charge out,Run program
      (steps xs (E.vertices.map label) ((pairs n).map (encodeEdge label)) source (label t)) charge initial [] out ∧
      EdgeList (eraseState out).heap (eraseState out).registers.d path ∧ PathResult f label path ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=5 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 388 H A (instructionBound n B W) := by
  let old := eraseState initial
  let vs := E.vertices.map label
  let pairsRep := (pairs n).map (encodeEdge label)
  let matrix := ResidualSearchData.adjacency f
  have adj : ResidualMatrixProgram.flags xs=GraphRelaxationRefinement.matrix matrix :=
    (ResidualMatrixProgram.flags_eq f values).trans (ResidualSearchData.matrix_eq f).symm
  have rows : n ≤ (ResidualMatrixProgram.flags xs).length := by
    rw [adj,GraphRelaxationRefinement.matrix_length]
  have cols : ∀ i (hi : i<n),n ≤ ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)).length := by
    intro i hi
    have row : ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)) =
        ((GraphRelaxationRefinement.matrix matrix)[i]'(by simp [GraphRelaxationRefinement.matrix_length,hi])) :=
      List.getElem_of_eq adj _
    rw [row]
    exact (GraphRelaxationRefinement.matrix_row_length matrix ⟨i,hi⟩).ge
  have hv : ∀ u ∈ vs,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t)<n := by rw [hlabel]; exact t.isLt
  obtain ⟨ext,args,root,hrep,body⟩ := natural_path n input canonical vertices sourceRep ends rows cols hv ht old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 5
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps xs vs pairsRep source (label t)) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  let path := SupportRecoveryProgram.search vs (ResidualMatrixProgram.flags xs) pairsRep source (label t)
  refine ⟨path,charge,out,hr,?_,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]
    simpa only [final,state,Registers.set,path] using hrep
  · simpa only [path,ResidualMatrixProgram.flags_eq f values] using
      ResidualSearchData.result_exact f different E label hlabel source hsource
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have vw : ∀ u ∈ vs,WordBound W n u := by
      intro u hu
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
      exact ⟨labels i,(hv (label i) hu).le⟩
    have ew : ∀ e ∈ pairsRep,EdgeWidths W e := by
      intro e he
      obtain ⟨uv,_,rfl⟩ := List.mem_map.mp he
      exact ⟨labels uv.1,labels uv.2⟩
    have sk := SupportRecoveryProgram.search_steps_le W n vs (ResidualMatrixProgram.flags xs)
      pairsRep source (label t) vw ⟨labels t,ht.le⟩ sourceWidth ew
    simp only [vs,pairsRep,List.length_map,E.length_eq_card,Fintype.card_fin,ResidualSearchData.pair_count] at sk
    have mk := value_steps_le f xs values canonical capWidths amountWidths
    apply SupportSearchEncoding.complete_mono
    unfold steps instructionBound vs pairsRep
    omega

end DirectedFlowCutGap.ResidualSearchProgram
