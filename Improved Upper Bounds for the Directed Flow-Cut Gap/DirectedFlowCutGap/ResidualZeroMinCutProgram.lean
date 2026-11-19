import DirectedFlowCutGap.ResidualZeroTableProgram
import DirectedFlowCutGap.ResidualMaxFlowCutProgram
import DirectedFlowCutGap.BinaryCounterProgram

/-!
# From binary capacities and budget to the minimum cut

The program constructs the starting zero flow, materializes the binary
budget as a unary spine without using the tape, and executes the fixed
minimum-cut program in the same heap.
-/

namespace DirectedFlowCutGap.ResidualZeroMinCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open ResidualZeroTableProgram (CapacityRows CapacityValues)
open ResidualMatrixProgram (StoredTable)
open ResidualFlowLoopProgram (Configuration configuration_extend)
open ResidualFlowStepProgram (wordTable pairTable)

def zeroLabel (pc : Fin 32) : Fin 1689 := ⟨16+pc.val,by omega⟩
def counterLabel (pc : Fin 17) : Fin 1689 := if pc.val=16 then 10 else ⟨48+pc.val,by omega⟩
def cutLabel (pc : Fin 1624) : Fin 1689 := ⟨65+pc.val,by omega⟩

def program : Program 1689 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (zeroLabel 0) 1 .r0
    | 1 => .call 8 2 .r2
    | 2 => .call (cutLabel 0) 3 .r3
    | 8 => .move .r0 .r2 9
    | 9 => .call (counterLabel 0) 10 .r3
    | 10 => .ret .r3
    | _ => .halt
  else if h : pc.val<48 then
    if pc.val=20 then .ret .r3
    else ReferenceProgramLabels.instruction zeroLabel
      (ResidualZeroTableProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<65 then
    ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program ⟨pc.val-48,by omega⟩)
  else if pc.val=70 then .ret .r3
  else ReferenceProgramLabels.instruction cutLabel
    (ResidualMaxFlowCutProgram.program ⟨pc.val-65,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 1689))
    (tape : Bits) (pc : Fin 1689) : NaturalState 1689 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

private theorem zero_slots (pc : Fin 32) (h : ResidualZeroTableProgram.program pc≠.halt) :
    program (zeroLabel pc) = ReferenceProgramLabels.instruction zeroLabel (ResidualZeroTableProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,zeroLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<48 by omega,show 16+pc.val≠20 by omega]

private theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc) = ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,counterLabel,hp,show ¬48+pc.val<16 by omega,show ¬48+pc.val<48 by omega,show 48+pc.val<65 by omega]

private theorem cut_slots (pc : Fin 1624) (h : ResidualMaxFlowCutProgram.program pc≠.halt) :
    program (cutLabel pc) = ReferenceProgramLabels.instruction cutLabel (ResidualMaxFlowCutProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬65+pc.val<16 by omega,show ¬65+pc.val<48 by omega,
      show ¬65+pc.val<65 by omega,show 65+pc.val≠70 by omega]

private theorem join {s u v : NaturalState 1689} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem zero_call {heap : NaturalHeap} {r : Registers ℕ} {cs : List (List Bits)}
    (input : CapacityRows heap r.a cs) (tape : Bits) :
    ∃ ext root,StoredTable (heap++ext) root (ResidualZeroTableProgram.table cs) ∧
      NaturalRun program (ResidualZeroTableProgram.tableSteps cs+6) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  obtain ⟨ext,regs,root,rep,body⟩ := ResidualZeroTableProgram.natural_zero input tape
  let frame : Frame ℕ 1689 := ⟨1,.r0,r⟩
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (zeroLabel 4)
  have call : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape (zeroLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run zeroLabel ResidualZeroTableProgram.program program zero_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (ResidualZeroTableProgram.tableSteps cs+4)
      (state heap r [frame] tape (zeroLabel 0)) [] stop := by
    simpa [stop,state,ResidualZeroTableProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [stop,frame,state,program,zeroLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem budget_call {heap : NaturalHeap} {r : Registers ℕ} {word : Bits}
    (input : BoolList heap r.c word) (tape : Bits) :
    ∃ ext root,IndexSpine (heap++ext) root (value word) ∧
      NaturalRun program (BinaryCounterProgram.steps word+4) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  let args := r.set .r0 r.c
  obtain ⟨ext,root,len,body,rep⟩ := BinaryCounterProgram.convert_return (a:=args.a) input heap.length
    args.b args.c args.d rfl args 16 [] tape
  let outer : Frame ℕ 1689 := ⟨2,.r2,r⟩
  let inner : Frame ℕ 1689 := ⟨10,.r3,args⟩
  have call : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [outer] tape 8,[],0⟩ := rfl
  have move : tickNatural program (state heap r [outer] tape 8)=
      some ⟨state heap args [outer] tape 9,[],0⟩ := rfl
  have enter : tickNatural program (state heap args [outer] tape 9)=
      some ⟨state heap args [inner,outer] tape (counterLabel 0),[],0⟩ := rfl
  let before := state (heap++ext) (args.set .r3 root) [outer] tape 10
  have lift := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots body
  have lift := ReferenceProgramStack.run program [outer] lift
  have trace : NaturalRun program (BinaryCounterProgram.steps word)
      (state heap args [inner,outer] tape (counterLabel 0)) [] before := by
    cases r
    simpa [before,state,inner,BinaryCounterProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,counterLabel,args,Registers.set,len] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r2 root) [] tape 2,[],0⟩ := by
    simp [before,outer,state,program,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (.step move (.step enter (join trace (.step ret (.done _)))))⟩

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

def instructionBound (n B W fuel P : ℕ) : ℕ :=
  ResidualZeroTableProgram.instructionBound n n + (3*fuel+10*P+3) +
    ResidualMaxFlowCutProgram.instructionBound n B W fuel +8

theorem natural_zero_cut {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (word : Bits) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (D : ResidualSearch.Enumeration (Fin n)) (fits : cutCapacity c X≤value word)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (cs : List (List Bits)) (values : CapacityValues c cs (List.finRange n) (List.finRange n))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤B)
    (input : CapacityRows heap r.a cs)
    (configuration : Configuration heap r.b (wordTable label) source (label t) (pairTable label))
    (budget : BoolList heap r.c word) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (ResidualMaxFlowCutProgram.referenceCut (c:=c) (s:=s) (t:=t) D X) ∧
      NaturalRun program k (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 3) ∧
      k ≤ instructionBound n B W (value word) word.length := by
  obtain ⟨ez,table,flowRep,init⟩ := zero_call input tape
  let mid := heap++ez
  let withTable := r.set .r0 table
  have wordRep : BoolList mid withTable.c word := boolList_extend budget ez
  obtain ⟨eb,fuel,budgetRep,convert⟩ := budget_call wordRep tape
  let ready := mid++eb
  let args := withTable.set .r2 fuel
  let f := Flow.zero c s t
  have room : (cutCapacity c X : ℤ) ≤ f.value+value word := by
    simp only [f,Flow.zero_value,zero_add]
    exact_mod_cast fits
  have capRep : StoredTable ready args.a (ResidualZeroTableProgram.table cs) :=
    ResidualTableUpdateProgram.table_extend flowRep eb
  have config : Configuration ready args.b (wordTable label) source (label t) (pairTable label) :=
    configuration_extend (configuration_extend configuration ez) eb
  have unary : IndexSpine ready args.c (value word) := budgetRep
  obtain ⟨ec,regs,root,k,mask,trace,bound⟩ := ResidualMaxFlowCutProgram.natural_min_cut (r:=args)
    (value word) X hs ht D capacities label hlabel labels source hsource sourceWidth
    f (ResidualZeroTableProgram.table cs) room (ResidualZeroTableProgram.zero_values c cs _ _ values)
    (ResidualZeroTableProgram.zero_fields cs B widths) capRep config unary tape
  let frame : Frame ℕ 1689 := ⟨3,.r3,args⟩
  let stop := state (ready++ec) (regs.set .r3 root) [frame] tape (cutLabel 5)
  have call : tickNatural program (state ready args [] tape 2)=
      some ⟨state ready args [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cutLabel ResidualMaxFlowCutProgram.program program cut_slots trace
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program k (state ready args [frame] tape (cutLabel 0)) [] stop := by
    simpa [stop,state,ResidualMaxFlowCutProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (ready++ec) (args.set .r3 root) [] tape 3,[],0⟩ := by
    simp [stop,frame,state,program,cutLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ez++eb++ec,args,root,ResidualZeroTableProgram.tableSteps cs+
    BinaryCounterProgram.steps word+k+12,?_,?_,?_⟩
  · simpa only [ready,mid,List.append_assoc] using mask
  · have last := NaturalRun.step call (join run (.step ret (.done _)))
    have whole := join init (join convert last)
    convert whole using 1 <;> first | rfl | omega | simp only [ready,mid,List.append_assoc]
  · have rows : cs.length=n := values.length_eq.trans List.length_finRange
    have rect (xs : List Bits) (hx : xs ∈ cs) : xs.length=n := by
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
      have other : i < (List.finRange n).length := by rwa [← values.length_eq]
      exact (values.get hi other).length_eq.trans List.length_finRange
    have setup := ResidualZeroTableProgram.steps_le cs n rect
    rw [rows] at setup
    have counter := BinaryCounterProgram.steps_bound word
    unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 1689) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_zero_cut {H A B W : ℕ} (word : Bits) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (D : ResidualSearch.Enumeration (Fin n)) (fits : cutCapacity c X≤value word)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (cs : List (List Bits)) (values : CapacityValues c cs (List.finRange n) (List.finRange n))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤B)
    (initial : BitState 1689) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs)
    (configuration : Configuration (eraseState initial).heap (eraseState initial).registers.b
      (wordTable label) source (label t) (pairTable label))
    (budget : BoolList (eraseState initial).heap (eraseState initial).registers.c word) :
    ∃ (charge steps : ℕ) (out : BitState 1689),
      Run program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (ResidualMaxFlowCutProgram.referenceCut
        (c:=c) (s:=s) (t:=t) D X) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=3 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 1689 H A (instructionBound n B W (value word) word.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,hrep,body,hsteps⟩ :=
    natural_zero_cut word X hs ht D fits capacities label hlabel labels source hsource sourceWidth
      cs values widths input configuration budget old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 3
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

end DirectedFlowCutGap.ResidualZeroMinCutProgram
