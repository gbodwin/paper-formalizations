import DirectedFlowCutGap.ResidualCutData

/-!
# Physical residual sink-complement cut

The program builds the residual matrix, executes complete backward search
from the sink, and passes the returned search table to the flag scanner.
The result is the cut in the supplied numerical vertex order.
-/

namespace DirectedFlowCutGap.ResidualCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open GraphDiscoveryProgram (Vertices vertices_extend)
open SupportRecoveryProgram (StoredGlobalContext SupportContext Code Codes rounds roundSteps)
open ResidualRowProgram (Entry)
open ResidualMatrixProgram (StoredTable ValueTable)
open ResidualSearchProgram (Endpoints endpoints_extend)
open ResidualFlowStepProgram (wordTable pairTable)
open BinarySigned (Canonical)

def matrixLabel (pc : Fin 92) : Fin 700 := ⟨24+pc.val,by omega⟩
def roundsLabel (pc : Fin 280) : Fin 700 := if pc.val=279 then 5 else ⟨116+pc.val,by omega⟩
def flagsLabel (pc : Fin 304) : Fin 700 := ⟨396+pc.val,by omega⟩

def program : Program 700 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .call (matrixLabel 14) 1 .r0
    | 1 => .call 8 2 .r3
    | 2 => .move .r0 .r1 3
    | 3 => .move .r1 .r3 4
    | 4 => .call (roundsLabel 240) 5 .r3
    | 5 => .move .r1 .r3 6
    | 6 => .call (flagsLabel 22) 7 .r3
    | 8 => .field .r2 .r3 true 9
    | 9 => .make .r0 (.pair .r0 .r2) 10
    | 10 => .make .r0 (.pair .r1 .r0) 11
    | 11 => .field .r2 .r3 false 12
    | 12 => .make .r3 (.pair .r2 .r0) 13
    | 13 => .ret .r3
    | _ => .halt
  else if h : pc.val<116 then
    if pc.val=39 then .ret .r3
    else ReferenceProgramLabels.instruction matrixLabel
      (ResidualMatrixProgram.program ⟨pc.val-24,by omega⟩)
  else if h : pc.val<396 then
    ReferenceProgramLabels.instruction roundsLabel (SupportRecoveryProgram.program ⟨pc.val-116,by omega⟩)
  else if pc.val=419 then .ret .r3
  else ReferenceProgramLabels.instruction flagsLabel
    (ResidualCutFlagsProgram.program ⟨pc.val-396,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 700))
    (tape : Bits) (pc : Fin 700) : NaturalState 700 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

private theorem matrix_slots (pc : Fin 92) (h : ResidualMatrixProgram.program pc≠.halt) :
    program (matrixLabel pc) =
      ReferenceProgramLabels.instruction matrixLabel (ResidualMatrixProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,matrixLabel,show ¬24+pc.val<24 by omega,show 24+pc.val<116 by omega,
      show 24+pc.val≠39 by omega]

private theorem rounds_slots (pc : Fin 280) (h : SupportRecoveryProgram.program pc≠.halt) :
    program (roundsLabel pc) =
      ReferenceProgramLabels.instruction roundsLabel (SupportRecoveryProgram.program pc) := by
  by_cases hp : pc.val=279
  · have eq : pc=279 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,roundsLabel,hp,show ¬116+pc.val<24 by omega,show ¬116+pc.val<116 by omega,
      show 116+pc.val<396 by omega]

private theorem flags_slots (pc : Fin 304) (h : ResidualCutFlagsProgram.program pc≠.halt) :
    program (flagsLabel pc) =
      ReferenceProgramLabels.instruction flagsLabel (ResidualCutFlagsProgram.program pc) := by
  by_cases hp : pc.val=23
  · have eq : pc=23 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,flagsLabel,show ¬396+pc.val<24 by omega,show ¬396+pc.val<116 by omega,
      show ¬396+pc.val<396 by omega,show 396+pc.val≠419 by omega]

private theorem join {s u v : NaturalState 700} {k l : ℕ} {e f : List Event}
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
  let frame : Frame ℕ 700 := ⟨1,.r0,r⟩
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
  let saved : List (Frame ℕ 700) := [⟨2,.r3,r⟩]
  let re := r.set .r2 edgeList
  let rm := re.set .r0 p
  let rb := rm.set .r0 (p+1)
  let rt := rb.set .r2 word
  let rg := rt.set .r3 (p+2)
  let hm' := heap++[m]
  let hb' := heap++[m,b]
  let hg' := heap++[m,b,g]
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r saved tape 8,[],0⟩ := rfl
  have edge : tickNatural program (state heap r saved tape 8)=some ⟨state heap re saved tape 9,[],0⟩ := by
    simp [re,state,program,tickNatural,Registers.get,hpair]
  have matrix : tickNatural program (state heap re saved tape 9)=some ⟨state hm' rm saved tape 10,[],0⟩ := by
    cases r
    simp [re,rm,hm',m,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have bundle : tickNatural program (state hm' rm saved tape 10)=some ⟨state hb' rb saved tape 11,[],0⟩ := by
    cases r
    simp [re,rm,rb,hm',hb',b,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have target : tickNatural program (state hb' rb saved tape 11)=some ⟨state hb' rt saved tape 12,[],0⟩ := by
    have hp := lookup_extend hpair [m,b]
    cases r
    simp [hp,re,rm,rb,rt,hb',state,program,tickNatural,Registers.get,Registers.set]
  have whole : tickNatural program (state hb' rt saved tape 12)=some ⟨state hg' rg saved tape 13,[],0⟩ := by
    cases r
    simp [re,rm,rb,rt,rg,hb',hg',g,p,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have ret : tickNatural program (state hg' rg saved tape 13)=
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

private theorem rounds_call {heap : NaturalHeap} {r : Registers ℕ} {vs adj : List Bits}
    {es : List (Bits×Bits)} {target : Bits} (N : ℕ)
    (hv : Vertices heap r.a vs) (ctx : StoredGlobalContext heap r.b vs adj es target)
    (rows : N≤adj.length) (cols : ∀ i (hi : i<N),N≤(adj[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    ∃ ext root,Codes (heap++ext) root (rounds vs adj es target vs) ∧
      NaturalRun program (roundSteps vs adj es target vs+1) (state heap r [] tape 4) []
        (state (heap++ext) (r.set .r3 root) [] tape 5) := by
  obtain ⟨ext,root,_,body,rep⟩ := SupportRecoveryProgram.rounds_return N hv ctx
    rows cols labels endLabel heap.length r.c r.d rfl r 279 [] tape
  let frame : Frame ℕ 700 := ⟨5,.r3,r⟩
  have call : tickNatural program (state heap r [] tape 4)=
      some ⟨state heap r [frame] tape (roundsLabel 240),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run roundsLabel SupportRecoveryProgram.program program rounds_slots body
  have run : NaturalRun program (roundSteps vs adj es target vs)
      (state heap r [frame] tape (roundsLabel 240)) []
        (state (heap++ext) (r.set .r3 root) [] tape 5) := by
    cases r
    simpa [frame,state,SupportRecoveryProgram.state,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      roundsLabel,Registers.set] using lift
  exact ⟨ext,root,rep,.step call run⟩

private theorem flags_call {heap : NaturalHeap} {r : Registers ℕ} {vs : List Bits} {cs : List Code}
    (hv : Vertices heap r.a vs) (codes : Codes heap r.b cs) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (vs.map (ResidualCutFlagsProgram.mark cs)) ∧
      NaturalRun program (ResidualCutFlagsProgram.steps cs vs+3) (state heap r [] tape 6) []
        (state (heap++ext) (r.set .r3 root) [] tape 7) := by
  obtain ⟨ext,root,rep,body⟩ := ResidualCutFlagsProgram.natural_flags hv codes tape
  let frame : Frame ℕ 700 := ⟨7,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) [frame] tape (flagsLabel 23)
  have call : tickNatural program (state heap r [] tape 6)=
      some ⟨state heap r [frame] tape (flagsLabel 22),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run flagsLabel ResidualCutFlagsProgram.program program flags_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualCutFlagsProgram.steps cs vs+1)
      (state heap r [frame] tape (flagsLabel 22)) [] before := by
    simpa [before,state,ResidualCutFlagsProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) [] tape 7,[],0⟩ := by
    simp [before,frame,state,program,flagsLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

def steps (xs : List (List Entry)) (vs : List Bits) (es : List (Bits×Bits)) (target : Bits) : ℕ :=
  let adj := ResidualMatrixProgram.flags xs
  ResidualMatrixProgram.steps xs + roundSteps vs adj es target vs +
    ResidualCutFlagsProgram.steps (rounds vs adj es target vs) vs +17

theorem natural_cut {heap : NaturalHeap} {r : Registers ℕ} {xs : List (List Entry)} {vs : List Bits}
    {es : List (Bits×Bits)} {target : Bits} (N : ℕ)
    (input : StoredTable heap r.a xs) (canonical : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1)
    (hv : Vertices heap r.b vs) (ends : Endpoints heap r.d target es)
    (rows : N≤(ResidualMatrixProgram.flags xs).length)
    (cols : ∀ i (hi : i<N),N≤((ResidualMatrixProgram.flags xs)[i]'(lt_of_lt_of_le hi rows)).length)
    (labels : ∀ u ∈ vs,value u<N) (endLabel : value target<N) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (root : ℕ),
      BoolList (heap++ext) root (vs.map
        (ResidualCutFlagsProgram.mark (rounds vs (ResidualMatrixProgram.flags xs) es target vs))) ∧
      NaturalRun program (steps xs vs es target) (state heap r [] tape 0) []
        (state (heap++ext) (out.set .r3 root) [] tape 7) := by
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
  obtain ⟨er,codes,rep,search⟩ := rounds_call N vertex ctx rows cols labels endLabel tape
  let gathered := grown++er
  let stage := args.set .r3 codes
  let readArgs := stage.set .r1 codes
  have carry : tickNatural program (state gathered stage [] tape 5)=
      some ⟨state gathered readArgs [] tape 6,[],0⟩ := rfl
  obtain ⟨ef,root,hrep,scan⟩ := flags_call (r:=readArgs) (vertices_extend vertex er) rep tape
  refine ⟨em++ec++er++ef,readArgs,root,?_,?_⟩
  · simpa only [gathered,grown,mid,List.append_assoc] using hrep
  · have suffix := join search (.step carry scan)
    have trace := join mt (join ct (.step m0 (.step m1 suffix)))
    simp only [steps]
    convert trace using 1 <;> first | rfl | omega | simp only [grown,mid,List.append_assoc]

open IntegralNetworkFlow
open ResidualSearchData (pairs)
open SupportSearchEncoding (encodeEdge complete_mono)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

def instructionBound (n B W : ℕ) : ℕ :=
  ResidualMatrixProgram.instructionBound n n B + SupportRecoveryProgram.searchCap n (n*n) W n +
    ResidualCutFlagsProgram.instructionBound n (1+n*n) W +15

def cut (f : Flow c s t) : Bits :=
  (List.finRange n).map fun v => decide (v ∈ finiteResidualCut (ResidualSearch.Enumeration.fin n) f)

theorem certified_cut {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (f : Flow c s t) (xs : List (List Entry)) (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (width : ∀ i,(label i).length≤W)
    (input : StoredTable heap r.a xs) (hv : Vertices heap r.b (wordTable label))
    (ends : Endpoints heap r.d (label t) (pairTable label)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (root : ℕ),
      BoolList (heap++ext) root (cut f) ∧
      NaturalRun program (steps xs (wordTable label) (pairTable label) (label t)) (state heap r [] tape 0) []
        (state (heap++ext) (out.set .r3 root) [] tape 7) ∧
      steps xs (wordTable label) (pairTable label) (label t) ≤ instructionBound n B W := by
  let vs := wordTable label
  let es := pairTable label
  let adj := ResidualMatrixProgram.flags xs
  let cs := rounds vs adj es (label t) vs
  have nvs : vs.length=n := by simp [vs,wordTable]
  have nes : es.length=n*n := by simp [es,pairTable,ResidualSearchData.pair_count]
  have hvs : ∀ u ∈ vs,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t)<n := by rw [hlabel]; exact t.isLt
  have wvs : ∀ u ∈ vs,u.length≤W := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    exact width i
  have hes : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e := by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    exact ⟨width a.1,width a.2⟩
  have canonical (row : List Entry) (hr : row ∈ xs) (x : Entry) (hx : x ∈ row) : Canonical x.1 :=
    (fields row hr x hx).1
  obtain ⟨rows,cols⟩ := ResidualFlowStepProgram.values_square f xs values
  obtain ⟨ext,regs,root,rep,body⟩ := natural_cut n input canonical hv ends rows cols hvs ht tape
  change BoolList (heap++ext) root (ResidualCutData.flags xs label t) at rep
  rw [ResidualCutData.flags_exact f xs values label hlabel] at rep
  refine ⟨ext,regs,root,rep,body,?_⟩
  have hw := ResidualFlowStepProgram.amount_widths f xs values B fields capacities
  have matrix := ResidualMatrixProgram.steps_le xs n B
    (fun row hr => ⟨(hw row hr).1,fun x hx => ⟨((hw row hr).2 x hx).2,(fields row hr x hx).2⟩⟩)
  have nxs : xs.length=n := values.length_eq.trans List.length_finRange
  rw [nxs] at matrix
  have search := SupportRecoveryProgram.search_steps_le W n vs adj es (label t) (label t)
    (fun u hu => ⟨wvs u hu,(hvs u hu).le⟩) ⟨width t,ht.le⟩ (width t) hes
  rw [nvs,nes] at search
  have roundsBound : roundSteps vs adj es (label t) vs ≤ SupportRecoveryProgram.searchCap n (n*n) W n := by
    unfold SupportRecoveryProgram.searchSteps at search
    omega
  have okCodes : ∀ x ∈ cs,x.1.length≤W :=
    SupportRecoveryProgram.rounds_all (fun u => u.length≤W) vs adj es (label t) vs wvs (width t)
  have count : cs.length≤1+n*n := by
    have h := SupportRecoveryProgram.rounds_length vs adj es (label t) vs
    simpa only [cs,nvs] using h
  have scan := ResidualCutFlagsProgram.steps_le cs vs W wvs okCodes
  rw [nvs] at scan
  have capScan : ResidualCutFlagsProgram.instructionBound n cs.length W ≤
      ResidualCutFlagsProgram.instructionBound n (1+n*n) W := by
    unfold ResidualCutFlagsProgram.instructionBound
    gcongr
  have finalScan := scan.trans capScan
  change ResidualMatrixProgram.steps xs + roundSteps vs adj es (label t) vs +
    ResidualCutFlagsProgram.steps cs vs +17 ≤ _
  unfold instructionBound
  omega

private theorem at_entry (s : NaturalState 700) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_cut {H A B W : ℕ} (f : Flow c s t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (width : ∀ i,(label i).length≤W)
    (initial : BitState 700) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (vertices : Vertices (eraseState initial).heap (eraseState initial).registers.b (wordTable label))
    (ends : Endpoints (eraseState initial).heap (eraseState initial).registers.d (label t) (pairTable label)) :
    ∃ charge out,Run program (steps xs (wordTable label) (pairTable label) (label t)) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (cut f) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=7 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 700 H A (instructionBound n B W) := by
  let old := eraseState initial
  obtain ⟨ext,regs,root,rep,body,bound⟩ :=
    certified_cut f xs values fields capacities label hlabel width input vertices ends old.source
  let final := state (old.heap++ext) (regs.set .r3 root) [] old.source 7
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps xs (wordTable label) (pairTable label) (label t)) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans (complete_mono _ _ _ _ _ bound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.ResidualCutProgram
