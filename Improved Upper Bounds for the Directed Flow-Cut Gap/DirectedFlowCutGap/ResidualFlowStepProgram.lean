import DirectedFlowCutGap.ResidualSearchProgram
import DirectedFlowCutGap.ResidualTableUpdateProgram

/-!
# One complete residual-flow step

The fixed program searches the current table for a residual path. If the
returned path is nonempty, the program passes its address to the table
updater. If the path is empty, it returns the original table. The result
pairs the table and the path for the caller.
-/

namespace DirectedFlowCutGap.ResidualFlowStepProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open ResidualRowProgram (Entry)
open ResidualMatrixProgram (StoredTable ValueTable)
open ResidualSearchProgram (Endpoints endpoints_extend)
open ResidualTableUpdateProgram (table_extend)
open GraphDiscoveryProgram (Vertices vertices_extend)
open BinarySigned (Canonical)

def searchLabel (pc : Fin 388) : Fin 884 := ⟨16+pc.val,by omega⟩
def updateLabel (pc : Fin 480) : Fin 884 := ⟨404+pc.val,by omega⟩

def program : Program 884 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (searchLabel 0) 1 .r3
    | 1 => .branch .r3 4 5 5 2
    | 2 => .make .r2 (.pair .r3 .r1) 3
    | 3 => .call (updateLabel 26) 4 .r0
    | 4 => .make .r3 (.pair .r0 .r3) 5
    | _ => .halt
  else if h : pc.val<404 then
    if pc.val=21 then .ret .r3
    else ReferenceProgramLabels.instruction searchLabel
      (ResidualSearchProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=431 then .ret .r3
  else ReferenceProgramLabels.instruction updateLabel
    (ResidualTableUpdateProgram.program ⟨pc.val-404,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 884))
    (tape : Bits) (pc : Fin 884) : NaturalState 884 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def path (xs : List (List Entry)) (vs : List Bits) (allEdges : List (Bits×Bits)) (source target : Bits) :
    List (Bits×Bits) :=
  SupportRecoveryProgram.search vs (ResidualMatrixProgram.flags xs) allEdges source target

def outputTable (xs : List (List Entry)) (vs : List Bits) (es : List (Bits×Bits)) : List (List Entry) :=
  if es=[] then xs else ResidualTableUpdateProgram.updateTable es vs xs vs

def steps (xs : List (List Entry)) (vs : List Bits) (allEdges : List (Bits×Bits)) (source target : Bits) : ℕ :=
  let es := path xs vs allEdges source target
  ResidualSearchProgram.steps xs vs allEdges source target+
    (if es=[] then 4 else ResidualTableUpdateProgram.steps es vs xs vs+8)

def Output (heap : NaturalHeap) (root : ℕ) (xs : List (List Entry)) (es : List (Bits×Bits)) : Prop :=
  ∃ table pathRoot,heap[root]?=some (.pair table pathRoot) ∧ StoredTable heap table xs ∧ EdgeList heap pathRoot es

private theorem search_slots (pc : Fin 388) (h : ResidualSearchProgram.program pc≠.halt) :
    program (searchLabel pc) = ReferenceProgramLabels.instruction searchLabel (ResidualSearchProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,searchLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<404 by omega,
      show 16+pc.val≠21 by omega]

private theorem update_slots (pc : Fin 480) (h : ResidualTableUpdateProgram.program pc≠.halt) :
    program (updateLabel pc) =
      ReferenceProgramLabels.instruction updateLabel (ResidualTableUpdateProgram.program pc) := by
  by_cases hp : pc.val=27
  · have eq : pc=27 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,updateLabel,show ¬404+pc.val<16 by omega,show ¬404+pc.val<404 by omega,
      show 404+pc.val≠431 by omega]

private theorem join {s u v : NaturalState 884} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem search_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {vs : List Bits} {allEdges : List (Bits×Bits)} {source target : Bits} (N : ℕ)
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (hv : Vertices heap r.b vs) (hs : BoolList heap r.c source)
    (ends : Endpoints heap r.d target allEdges) (rows : N ≤ (ResidualMatrixProgram.flags xs).length)
    (cols : ∀ i (hi : i<N),N ≤ ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    ∃ ext root,EdgeList (heap++ext) root (path xs vs allEdges source target) ∧
      NaturalRun program (ResidualSearchProgram.steps xs vs allEdges source target+2)
        (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  obtain ⟨ext,regs,root,rep,body⟩ := ResidualSearchProgram.natural_path N input canonical hv hs ends
    rows cols labels endLabel tape
  let frame : Frame ℕ 884 := ⟨1,.r3,r⟩
  let before := state (heap++ext) (regs.set .r3 root) [frame] tape (searchLabel 5)
  have call : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape (searchLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run searchLabel ResidualSearchProgram.program program search_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualSearchProgram.steps xs vs allEdges source target)
      (state heap r [frame] tape (searchLabel 0)) [] before := by
    simpa [before,state,ResidualSearchProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [before,frame,state,program,searchLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem update_call {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {vs : List Bits} {es : List (Bits×Bits)} (input : StoredTable heap r.a xs)
    (hv : Vertices heap r.b vs) (hlen : xs.length=vs.length) (rect : ∀ row ∈ xs,row.length=vs.length)
    (context : ResidualTableUpdateProgram.Context heap r.c es vs) (tape : Bits) :
    ∃ ext root,StoredTable (heap++ext) root (ResidualTableUpdateProgram.updateTable es vs xs vs) ∧
      NaturalRun program (ResidualTableUpdateProgram.steps es vs xs vs+3)
        (state heap r [] tape 3) [] (state (heap++ext) (r.set .r0 root) [] tape 4) := by
  obtain ⟨ext,root,rep,body⟩ := ResidualTableUpdateProgram.natural_table input hv hlen rect context tape
  let frame : Frame ℕ 884 := ⟨4,.r0,r⟩
  let before := state (heap++ext) (r.set .r3 root) [frame] tape (updateLabel 27)
  have call : tickNatural program (state heap r [] tape 3)=
      some ⟨state heap r [frame] tape (updateLabel 26),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run updateLabel ResidualTableUpdateProgram.program program update_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualTableUpdateProgram.steps es vs xs vs+1)
      (state heap r [frame] tape (updateLabel 26)) [] before := by
    simpa [before,state,ResidualTableUpdateProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r0 root) [] tape 4,[],0⟩ := by
    simp [before,frame,state,program,updateLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem pack_result {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {es : List (Bits×Bits)} (table : StoredTable heap r.a xs) (path : EdgeList heap r.d es) (tape : Bits) :
    ∃ ext root,Output (heap++ext) root xs es ∧
      NaturalRun program 1 (state heap r [] tape 4) [] (state (heap++ext) (r.set .r3 root) [] tape 5) := by
  let cell : Cell ℕ := .pair r.a r.d
  let ext : NaturalHeap := [cell]
  let root := heap.length
  have alloc : tickNatural program (state heap r [] tape 4)=
      some ⟨state (heap++ext) (r.set .r3 root) [] tape 5,[],0⟩ := by
    simp [cell,ext,root,state,program,tickNatural,Registers.get,allocateNatural,Recipe.cell]
  exact ⟨ext,root,⟨r.a,r.d,by simp [ext,cell,root],table_extend table ext,edgeList_extend path ext⟩,
    .step alloc (.done _)⟩

theorem natural_step {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)}
    {vs : List Bits} {allEdges : List (Bits×Bits)} {source target : Bits} (N : ℕ)
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (hv : Vertices heap r.b vs) (hs : BoolList heap r.c source)
    (ends : Endpoints heap r.d target allEdges) (hlt : xs.length=vs.length)
    (rect : ∀ row ∈ xs,row.length=vs.length)
    (rows : N ≤ (ResidualMatrixProgram.flags xs).length)
    (cols : ∀ i (hi : i<N),N ≤ ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    let es := path xs vs allEdges source target
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Output (heap++ext) root (outputTable xs vs es) es ∧
      NaturalRun program (steps xs vs allEdges source target) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 5) := by
  let es := path xs vs allEdges source target
  obtain ⟨ext,edges,hpath,body⟩ := search_call N input canonical hv hs ends rows cols labels endLabel tape
  let mid := heap++ext
  let received := r.set .r3 edges
  have inputRep : StoredTable mid received.a xs := table_extend input ext
  have pathRep : EdgeList mid received.d es := hpath
  by_cases empty : es=[]
  · have lookup : mid[received.d]?=some .nil := by
      rw [empty] at pathRep
      cases pathRep with | nil h => exact h
    have branch : tickNatural program (state mid received [] tape 1)=
        some ⟨state mid received [] tape 4,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,tagBranch,lookup]
    obtain ⟨pack,root,hout,tail⟩ := pack_result inputRep pathRep tape
    refine ⟨ext++pack,received,root,?_,?_⟩
    · change Output _ root (outputTable xs vs es) es
      simpa only [outputTable,ite_eq_left empty,mid,List.append_assoc] using hout
    · have run := join body (.step branch tail)
      simp only [steps,show path xs vs allEdges source target=[] from empty,ite_true]
      convert run using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]
  · have present : ∃ h t,mid[received.d]?=some (.pair h t) := by
      cases hs : es with
      | nil => exact (empty hs).elim
      | cons e rest =>
        rw [hs] at pathRep
        cases pathRep with | cons h _ _ => exact ⟨_,_,h⟩
    obtain ⟨head,rest,lookup⟩ := present
    let ctx : Cell ℕ := .pair received.d received.b
    let grown := mid++[ctx]
    let args := received.set .r2 mid.length
    have branch : tickNatural program (state mid received [] tape 1)=
        some ⟨state mid received [] tape 2,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,tagBranch,lookup]
    have build : tickNatural program (state mid received [] tape 2)=
        some ⟨state grown args [] tape 3,[],0⟩ := by
      simp [grown,args,ctx,state,program,tickNatural,Registers.get,allocateNatural,Recipe.cell]
    have vertex : Vertices mid received.b vs := vertices_extend hv ext
    have packed : ResidualTableUpdateProgram.Context grown args.c es vs :=
      ⟨received.d,received.b,by simp [grown,args,ctx,Registers.set],
        edgeList_extend pathRep _,vertices_extend vertex _⟩
    obtain ⟨eu,table,hnew,update⟩ := update_call (r:=args)
      (table_extend inputRep [ctx]) (vertices_extend vertex [ctx]) hlt rect packed tape
    let finalHeap := grown++eu
    let ready := args.set .r0 table
    have newRep : StoredTable finalHeap ready.a (ResidualTableUpdateProgram.updateTable es vs xs vs) := hnew
    have ep : EdgeList finalHeap ready.d es := edgeList_extend (edgeList_extend pathRep [ctx]) eu
    obtain ⟨pack,root,hout,finish⟩ := pack_result newRep ep tape
    refine ⟨ext++[ctx]++eu++pack,ready,root,?_,?_⟩
    · change Output _ root (outputTable xs vs es) es
      simpa only [outputTable,ite_eq_right empty,finalHeap,grown,mid,List.append_assoc] using hout
    · have run := join body (.step branch (.step build (join update finish)))
      simp only [steps,ite_eq_right (show path xs vs allEdges source target≠[] from empty)]
      change NaturalRun program
        (ResidualSearchProgram.steps xs vs allEdges source target+(ResidualTableUpdateProgram.steps es vs xs vs+8)) _ _ _
      convert run using 1 <;> first | rfl | omega | simp only [finalHeap,grown,mid,List.append_assoc]

open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ResidualSearchData (PathResult pairs)
open SupportSearchEncoding (encodeEdge complete_mono)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

def wordTable (label : Fin n → Bits) : List Bits := (List.finRange n).map label

def pairTable (label : Fin n → Bits) : List (Bits×Bits) := (pairs n).map (encodeEdge label)

def stepPath (xs : List (List Entry)) (label : Fin n → Bits) (source target : Bits) : List (Bits×Bits) :=
  path xs (wordTable label) (pairTable label) source target

def Advance (f g : Flow c s t) (label : Fin n → Bits) (es : List (Bits×Bits)) : Prop :=
  (es=[] ∧ g=f ∧ ¬Nonempty (SimplePath f.residual s t)) ∨
    ∃ p : SimplePath f.residual s t,es=(FlowTable.edgeList p).map (encodeEdge label) ∧ es≠[] ∧ g=f.augment p

theorem advance_value (f g : Flow c s t) (label : Fin n → Bits) (es : List (Bits×Bits))
    (h : Advance f g label es) (different : s≠t) :
    g.value=f.value+(if es=[] then 0 else 1) := by
  rcases h with ⟨rfl,rfl,_⟩ | ⟨p,_,nonempty,rfl⟩
  · simp
  · simpa only [nonempty,ite_false] using f.augment_value p different

def instructionBound (n B W : ℕ) : ℕ :=
  ResidualSearchProgram.instructionBound n B W+ResidualTableUpdateProgram.instructionBound n n n W B+7

theorem amount_widths (f : Flow c s t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n)) (B : ℕ)
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B) :
    ∀ row ∈ xs,row.length=n ∧ ∀ e ∈ row,Canonical e.1 ∧ e.1.magnitude.length≤B := by
  intro row hrow
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hrow
  have hu : i < (List.finRange n).length := by rwa [← values.length_eq]
  have rel := values.get hi hu
  refine ⟨rel.length_eq.trans List.length_finRange,?_⟩
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
  have hv : j < (List.finRange n).length := by rwa [← rel.length_eq]
  have slot := rel.get hj hv
  have canonical := (fields _ hrow _ he).1
  exact ⟨canonical,(ResidualCapacityProgram.amount_width f _ _ _ slot.1 canonical).trans (capacities _ _)⟩

theorem values_square (f : Flow c s t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n)) :
    ∃ hrows : n ≤ (ResidualMatrixProgram.flags xs).length,
      ∀ i (hi : i<n),n ≤ ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi hrows)).length := by
  let matrix := ResidualSearchData.adjacency f
  have adj : ResidualMatrixProgram.flags xs=GraphRelaxationRefinement.matrix matrix :=
    (ResidualMatrixProgram.flags_eq f values).trans (ResidualSearchData.matrix_eq f).symm
  have rows : n ≤ (ResidualMatrixProgram.flags xs).length := by
    rw [adj,GraphRelaxationRefinement.matrix_length]
  refine ⟨rows,?_⟩
  intro i hi
  have row : ((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)) =
      ((GraphRelaxationRefinement.matrix matrix)[i]'(by simp [GraphRelaxationRefinement.matrix_length,hi])) :=
    List.getElem_of_eq adj _
  rw [row]
  exact (GraphRelaxationRefinement.matrix_row_length matrix ⟨i,hi⟩).ge

private theorem path_certificate (f : Flow c s t) (different : s≠t)
    (xs : List (List Entry)) (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (source : Bits) (hsource : value source=s.val) :
    PathResult f label (stepPath xs label source (label t)) := by
  have cert := ResidualSearchData.result_exact f different (ResidualSearch.Enumeration.fin n) label hlabel source hsource
  have order : (ResidualSearch.Enumeration.fin n).vertices=List.finRange n := by
    simp [ResidualSearch.Enumeration.fin,ResidualSearch.Enumeration.ofEquiv,List.finRange]
    rfl
  simpa only [order,stepPath,path,wordTable,pairTable,ResidualMatrixProgram.flags_eq f values] using cert

theorem certified_step {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (f : Flow c s t) (different : s≠t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (input : StoredTable heap r.a xs) (vertices : Vertices heap r.b (wordTable label))
    (sourceRep : BoolList heap r.c source) (ends : Endpoints heap r.d (label t) (pairTable label)) (tape : Bits) :
    let es := stepPath xs label source (label t)
    let ys := outputTable xs (wordTable label) es
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ) (g : Flow c s t),
      Output (heap++ext) root ys es ∧ ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧ Advance f g label es ∧
      NaturalRun program (steps xs (wordTable label) (pairTable label) source (label t))
        (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 5) ∧
      steps xs (wordTable label) (pairTable label) source (label t) ≤ instructionBound n B W := by
  let vs := wordTable label
  let allEdges := pairTable label
  let es := stepPath xs label source (label t)
  have left : xs.length=n := values.length_eq.trans List.length_finRange
  have right : vs.length=n := by simp [vs,wordTable]
  have hd : xs.length=vs.length := left.trans right.symm
  have dw := amount_widths f xs values B fields capacities
  have rect : ∀ row ∈ xs,row.length=vs.length := fun row h => (dw row h).1.trans right.symm
  have huv : ∀ u ∈ vs,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t)<n := by rw [hlabel]; exact t.isLt
  have words : ∀ u ∈ vs,u.length≤W := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    exact labels i
  have pairWidths (qs : List (Fin n×Fin n)) :
      ∀ e ∈ qs.map (encodeEdge label),SupportRecoveryProgram.EdgeWidths W e := by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    exact ⟨labels a.1,labels a.2⟩
  have canonical (row : List Entry) (hrow : row ∈ xs) (e : Entry) (he : e ∈ row) : Canonical e.1 :=
    (fields row hrow e he).1
  obtain ⟨rows,cols⟩ := values_square f xs values
  obtain ⟨ext,args,root,hout,trace⟩ := natural_step n input canonical vertices sourceRep ends hd rect rows cols huv ht tape
  have matchPath := path_certificate f different xs values label hlabel source hsource
  change PathResult f label es at matchPath
  have capMat := ResidualMatrixProgram.steps_le xs n B
    (fun row hr => ⟨(dw row hr).1,fun x hx => ⟨((dw row hr).2 x hx).2,(fields row hr x hx).2⟩⟩)
  rw [left] at capMat
  have supportSteps := SupportRecoveryProgram.search_steps_le W n vs (ResidualMatrixProgram.flags xs) allEdges
    source (label t) (fun u hu => ⟨words u hu,(huv u hu).le⟩) ⟨labels t,ht.le⟩ sourceWidth (pairWidths (pairs n))
  have alls : allEdges.length=n*n := by simp [allEdges,pairTable,ResidualSearchData.pair_count]
  rw [right,alls] at supportSteps
  have searchBudget : ResidualSearchProgram.steps xs vs allEdges source (label t) ≤
      ResidualSearchProgram.instructionBound n B W := by
    unfold ResidualSearchProgram.steps ResidualSearchProgram.instructionBound
    omega
  rcases matchPath with ⟨empty,stop⟩ | ⟨p,edges,nonempty⟩
  · refine ⟨ext,args,root,f,hout,?_,?_,Or.inl ⟨empty,rfl,stop⟩,trace,?_⟩
    · change ValueTable f (outputTable xs vs es) (List.finRange n) (List.finRange n)
      simpa only [outputTable,ite_eq_left empty] using values
    · change ∀ row ∈ outputTable xs vs es,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B
      simpa only [outputTable,ite_eq_left empty] using fields
    · change ResidualSearchProgram.steps xs vs allEdges source (label t)+
        (if es=[] then 4 else ResidualTableUpdateProgram.steps es vs xs vs+8) ≤ _
      rw [ite_eq_left empty]
      unfold instructionBound
      omega
  · have moved := ResidualTableUpdateProgram.table_matches f p xs (List.finRange n) (List.finRange n)
      values canonical label hlabel
    have same : outputTable xs vs es=ResidualTableUpdateProgram.updateTable es vs xs vs := by
      simp [outputTable,nonempty]
    have invariant := ResidualTableUpdateProgram.invariant es vs xs vs B fields
    refine ⟨ext,args,root,f.augment p,hout,?_,?_,Or.inr ⟨p,edges,nonempty,rfl⟩,trace,?_⟩
    · change ValueTable (f.augment p) (outputTable xs vs es) (List.finRange n) (List.finRange n)
      rw [same,edges]
      exact moved
    · change ∀ row ∈ outputTable xs vs es,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B
      simpa only [same] using invariant
    · have len : es.length≤n := by
        simpa only [edges,List.length_map,FlowTable.edgeList_length,Fintype.card_fin] using p.edgeLength_lt_card.le
      have wc : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e := by
        rw [edges]
        exact pairWidths (FlowTable.edgeList p)
      have edits := ResidualTableUpdateProgram.steps_le es vs xs vs W B words words
        (fun row h => ⟨rect row h,(dw row h).2⟩) wc
      rw [left,right] at edits
      have editBudget : ResidualTableUpdateProgram.instructionBound n n es.length W B ≤
          ResidualTableUpdateProgram.instructionBound n n n W B := by
        unfold ResidualTableUpdateProgram.instructionBound ResidualRowUpdateProgram.instructionBound
          ResidualCellUpdateProgram.instructionBound
        gcongr
      have edits := edits.trans editBudget
      change ResidualSearchProgram.steps xs vs allEdges source (label t)+
        (if es=[] then 4 else ResidualTableUpdateProgram.steps es vs xs vs+8) ≤ _
      rw [ite_eq_right nonempty]
      unfold instructionBound
      omega

private theorem at_entry (s : NaturalState 884) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_step {H A B W : ℕ} (f : Flow c s t) (different : s≠t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (initial : BitState 884) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (vertices : Vertices (eraseState initial).heap (eraseState initial).registers.b (wordTable label))
    (sourceRep : BoolList (eraseState initial).heap (eraseState initial).registers.c source)
    (ends : Endpoints (eraseState initial).heap (eraseState initial).registers.d (label t) (pairTable label)) :
    let es := stepPath xs label source (label t)
    let ys := outputTable xs (wordTable label) es
    ∃ (charge : ℕ) (out : BitState 884) (g : Flow c s t),
      Run program (steps xs (wordTable label) (pairTable label) source (label t)) charge initial [] out ∧
      Output (eraseState out).heap (eraseState out).registers.d ys es ∧
      ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧ Advance f g label es ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=5 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 884 H A (instructionBound n B W) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,g,hrep,relation,canonical,hadvance,body,hsteps⟩ :=
    certified_step f different xs values fields capacities label hlabel labels source hsource sourceWidth
      input vertices sourceRep ends old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 5
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps xs (wordTable label) (pairTable label) source (label t)) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,out,g,hr,?_,relation,canonical,hadvance,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (complete_mono _ _ _ _ _ hsteps)⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.ResidualFlowStepProgram
