import DirectedFlowCutGap.ResidualFlowLoopProgram
import DirectedFlowCutGap.ResidualCutProgram

/-!
# Maximum flow through the returned minimum-cut mask

A single fixed program calls the residual-flow loop and passes the
returned terminal table to the sink-complement scanner. It returns the
exact cut of the reference solver from any prepared feasible starting
flow with a sufficient represented cut budget.
-/

namespace DirectedFlowCutGap.ResidualMaxFlowCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open ResidualRowProgram (Entry)
open ResidualMatrixProgram (StoredTable ValueTable)
open ResidualFlowLoopProgram (Configuration configuration_extend)
open ResidualFlowStepProgram (wordTable pairTable)
open ResidualSearchProgram (Endpoints)
open BinarySigned (Canonical)

def loopLabel (pc : Fin 908) : Fin 1624 := ⟨16+pc.val,by omega⟩
def cutLabel (pc : Fin 700) : Fin 1624 := ⟨924+pc.val,by omega⟩

def program : Program 1624 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (loopLabel 20) 1 .r0
    | 1 => .field .r3 .r1 true 2
    | 2 => .field .r1 .r1 false 3
    | 3 => .field .r3 .r3 true 4
    | 4 => .call (cutLabel 0) 5 .r3
    | _ => .halt
  else if h : pc.val<924 then
    if pc.val=37 then .ret .r3
    else ReferenceProgramLabels.instruction loopLabel
      (ResidualFlowLoopProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=931 then .ret .r3
  else ReferenceProgramLabels.instruction cutLabel
    (ResidualCutProgram.program ⟨pc.val-924,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 1624))
    (tape : Bits) (pc : Fin 1624) : NaturalState 1624 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

private theorem loop_slots (pc : Fin 908) (h : ResidualFlowLoopProgram.program pc≠.halt) :
    program (loopLabel pc) =
      ReferenceProgramLabels.instruction loopLabel (ResidualFlowLoopProgram.program pc) := by
  by_cases hp : pc.val=21
  · have eq : pc=21 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,loopLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<924 by omega,
      show 16+pc.val≠37 by omega]

private theorem cut_slots (pc : Fin 700) (h : ResidualCutProgram.program pc≠.halt) :
    program (cutLabel pc) =
      ReferenceProgramLabels.instruction cutLabel (ResidualCutProgram.program pc) := by
  by_cases hp : pc.val=7
  · have eq : pc=7 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬924+pc.val<16 by omega,show ¬924+pc.val<924 by omega,
      show 924+pc.val≠931 by omega]

private theorem join {s u v : NaturalState 1624} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

private theorem loop_call {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (fuel : ℕ) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (f : Flow c s t) (xs : List (List Entry)) (fits : (cutCapacity c X : ℤ) ≤ f.value+fuel)
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (input : StoredTable heap r.a xs)
    (configuration : Configuration heap r.b (wordTable label) source (label t) (pairTable label))
    (budget : IndexSpine heap r.c fuel) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (ys : List (List Entry)) (g : Flow c s t) (steps : ℕ),
      StoredTable (heap++ext) root ys ∧ ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧ ¬Nonempty (SimplePath g.residual s t) ∧
      NaturalRun program steps (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) ∧
      steps ≤ ResidualFlowLoopProgram.instructionBound n B W fuel+2 := by
  let localFrame : Frame ℕ 908 := ⟨21,.r3,r⟩
  obtain ⟨ext,root,ys,g,k,rep,relation,norm,terminal,body,bound⟩ :=
    ResidualFlowLoopProgram.loop_return fuel X hs ht capacities label hlabel labels source hsource sourceWidth
      f xs fits values fields input configuration budget localFrame [] tape
  have begin : tickNatural ResidualFlowLoopProgram.program (ResidualFlowLoopProgram.state heap r [] tape 20)=
      some ⟨ResidualFlowLoopProgram.state heap r [localFrame] tape 0,[],0⟩ := rfl
  have whole := NaturalRun.step begin body
  let frame : Frame ℕ 1624 := ⟨1,.r0,r⟩
  let stop := state (heap++ext) (r.set .r3 root) [frame] tape (loopLabel 21)
  have enter : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape (loopLabel 20),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run loopLabel ResidualFlowLoopProgram.program program loop_slots whole
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (k+1) (state heap r [frame] tape (loopLabel 20)) [] stop := by
    simpa [stop,state,ResidualFlowLoopProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [stop,frame,state,program,loopLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,ys,g,k+3,rep,relation,norm,terminal,.step enter (join trace (.step ret (.done _))),?_⟩
  unfold ResidualFlowLoopProgram.instructionBound
  omega

private theorem cut_call {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (g : Flow c s t) (ys : List (List Entry)) (values : ValueTable g ys (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (input : StoredTable heap r.a ys)
    (words : GraphDiscoveryProgram.Vertices heap r.b (wordTable label))
    (ends : Endpoints heap r.d (label t) (pairTable label)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (ResidualCutProgram.cut g) ∧
      NaturalRun program (ResidualCutProgram.steps ys (wordTable label) (pairTable label) (label t)+2)
        (state heap r [] tape 4) [] (state (heap++ext) (r.set .r3 root) [] tape 5) ∧
      ResidualCutProgram.steps ys (wordTable label) (pairTable label) (label t) ≤ ResidualCutProgram.instructionBound n B W := by
  obtain ⟨ext,regs,root,rep,body,bound⟩ := ResidualCutProgram.certified_cut g ys values fields capacities
    label hlabel labels input words ends tape
  let frame : Frame ℕ 1624 := ⟨5,.r3,r⟩
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (cutLabel 7)
  have enter : tickNatural program (state heap r [] tape 4)=
      some ⟨state heap r [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cutLabel ResidualCutProgram.program program cut_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualCutProgram.steps ys (wordTable label) (pairTable label) (label t))
      (state heap r [frame] tape (cutLabel 0)) [] stop := by
    simpa [stop,state,ResidualCutProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 5,[],0⟩ := by
    simp [stop,frame,state,program,cutLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (join trace (.step ret (.done _))),bound⟩

def instructionBound (n B W fuel : ℕ) : ℕ :=
  ResidualFlowLoopProgram.instructionBound n B W fuel+ResidualCutProgram.instructionBound n B W+7

def referenceCut (D : ResidualSearch.Enumeration (Fin n)) (X : Finset (Fin n)) : Bits :=
  let final := IntegralNetworkFlow.run (finiteResidualSearch D c s t)
    (Flow.zero c s t) (cutCapacity c X)
  (List.finRange n).map fun v => decide (v ∈ finiteResidualCut D final)

theorem natural_min_cut {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (fuel : ℕ) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (D : ResidualSearch.Enumeration (Fin n))
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (f : Flow c s t) (xs : List (List Entry)) (fits : (cutCapacity c X : ℤ) ≤ f.value+fuel)
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (input : StoredTable heap r.a xs)
    (configuration : Configuration heap r.b (wordTable label) source (label t) (pairTable label))
    (budget : IndexSpine heap r.c fuel) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (referenceCut (c:=c) (s:=s) (t:=t) D X) ∧
      NaturalRun program k (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 5) ∧ k ≤ instructionBound n B W fuel := by
  obtain ⟨eLoop,table,ys,g,k,rep,rel,norm,terminal,trace,loopBound⟩ :=
    loop_call fuel X hs ht capacities label hlabel labels source hsource sourceWidth f xs fits values fields
      input configuration budget tape
  let mid := heap++eLoop
  let returned := r.set .r0 table
  have config : Configuration mid returned.b (wordTable label) source (label t) (pairTable label) :=
    configuration_extend configuration eLoop
  obtain ⟨words,rest,sRoot,tRoot,hconfig,hrest,vs,_,he⟩ := config
  let first := returned.set .r3 rest
  let vertices := first.set .r1 words
  let args := vertices.set .r3 tRoot
  have getRest : tickNatural program (state mid returned [] tape 1)=some ⟨state mid first [] tape 2,[],0⟩ := by
    simp [first,state,program,tickNatural,Registers.get,hconfig]
  have getVertices : tickNatural program (state mid first [] tape 2)=
      some ⟨state mid vertices [] tape 3,[],0⟩ := by
    simp [first,vertices,state,program,tickNatural,Registers.get,Registers.set,hconfig]
  have getTarget : tickNatural program (state mid vertices [] tape 3)=some ⟨state mid args [] tape 4,[],0⟩ := by
    simp [first,vertices,args,state,program,tickNatural,Registers.get,Registers.set,hrest]
  obtain ⟨eCut,root,mask,scan,cutBound⟩ :=
    cut_call (r:=args) g ys rel norm capacities label hlabel labels rep vs he tape
  have equal : ResidualCutProgram.cut g=referenceCut (c:=c) (s:=s) (t:=t) D X := by
    unfold ResidualCutProgram.cut referenceCut
    rw [ResidualFlowLoopProgram.terminal_cut_agrees (ResidualSearch.Enumeration.fin n) D g terminal X hs ht]
  rw [equal] at mask
  refine ⟨eLoop++eCut,args,root,k+(ResidualCutProgram.steps ys (wordTable label) (pairTable label) (label t)+5),
    ?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using mask
  · have run := join trace (.step getRest (.step getVertices (.step getTarget scan)))
    convert run using 1 <;> first | rfl | omega | simp only [List.append_assoc]
  · unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 1624) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_min_cut {H A B W : ℕ}
    (fuel : ℕ) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (D : ResidualSearch.Enumeration (Fin n))
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (f : Flow c s t) (xs : List (List Entry)) (fits : (cutCapacity c X : ℤ) ≤ f.value+fuel)
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (initial : BitState 1624) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (configuration : Configuration (eraseState initial).heap (eraseState initial).registers.b
      (wordTable label) source (label t) (pairTable label))
    (budget : IndexSpine (eraseState initial).heap (eraseState initial).registers.c fuel) :
    ∃ (charge steps : ℕ) (out : BitState 1624),
      Run program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (referenceCut (c:=c) (s:=s) (t:=t) D X) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=5 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 1624 H A (instructionBound n B W fuel) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,hrep,body,hsteps⟩ :=
    natural_min_cut fuel X hs ht D capacities label hlabel labels source hsource sourceWidth
      f xs fits values fields input configuration budget old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 5
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,k,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ hsteps)⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.ResidualMaxFlowCutProgram
