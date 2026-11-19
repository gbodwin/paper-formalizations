import DirectedFlowCutGap.ResidualFlowStepProgram
import DirectedFlowCutGap.ResidualCutUniqueness

/-!
# Finite charged residual-flow loop

One stored configuration is shared by every step. The program returns
when the actual search result is empty. An augmentation consumes one
cell of the stored iteration budget and passes its returned flow table
to the next iteration.
-/

namespace DirectedFlowCutGap.ResidualFlowLoopProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open ResidualRowProgram (Entry)
open ResidualMatrixProgram (StoredTable ValueTable)
open ResidualSearchProgram (Endpoints endpoints_extend)
open ResidualTableUpdateProgram (table_extend)
open ResidualFlowStepProgram (wordTable pairTable stepPath outputTable Advance)
open GraphDiscoveryProgram (Vertices vertices_extend)
open BinarySigned (Canonical)
open IntegralNetworkFlow

def stepLabel (pc : Fin 884) : Fin 908 := ⟨24+pc.val,by omega⟩

def program : Program 908 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .call 12 1 .r3
    | 1 => .field .r0 .r3 false 2
    | 2 => .field .r3 .r3 true 3
    | 3 => .branch .r3 4 23 23 5
    | 4 => .ret .r0
    | 5 => .branch .r2 23 23 23 6
    | 6 => .field .r2 .r2 true 0
    | 12 => .field .r3 .r1 true 13
    | 13 => .field .r1 .r1 false 14
    | 14 => .field .r2 .r3 false 15
    | 15 => .field .r3 .r3 true 16
    | 16 => .call (stepLabel 0) 17 .r3
    | 17 => .ret .r3
    | 20 => .call 0 21 .r3
    | _ => .halt
  else if pc.val=29 then .ret .r3
  else ReferenceProgramLabels.instruction stepLabel
    (ResidualFlowStepProgram.program ⟨pc.val-24,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 908))
    (tape : Bits) (pc : Fin 908) : NaturalState 908 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def Configuration (heap : NaturalHeap) (root : ℕ) (vs : List Bits) (source target : Bits)
    (pairs : List (Bits×Bits)) : Prop :=
  ∃ vertices rest sRoot tRoot,heap[root]?=some (.pair vertices rest) ∧ heap[rest]?=some (.pair sRoot tRoot) ∧
    Vertices heap vertices vs ∧ BoolList heap sRoot source ∧ Endpoints heap tRoot target pairs

theorem configuration_extend {heap : NaturalHeap} {root : ℕ} {vs : List Bits} {s t : Bits}
    {pairs : List (Bits×Bits)} (h : Configuration heap root vs s t pairs) (extra : NaturalHeap) :
    Configuration (heap++extra) root vs s t pairs := by
  obtain ⟨v,rest,sRoot,tRoot,hv,hr,words,source,fin⟩ := h
  exact ⟨v,rest,sRoot,tRoot,lookup_extend hv extra,lookup_extend hr extra,
    vertices_extend words extra,boolList_extend source extra,endpoints_extend fin extra⟩

private theorem step_slots (pc : Fin 884) (h : ResidualFlowStepProgram.program pc≠.halt) :
    program (stepLabel pc) = ReferenceProgramLabels.instruction stepLabel (ResidualFlowStepProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,stepLabel,show ¬24+pc.val<24 by omega,show 24+pc.val≠29 by omega]

private theorem join {s u v : NaturalState 908} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

variable {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}

private theorem run_step {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ}
    (f : Flow c s t) (different : s≠t) (xs : List (List Entry))
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (input : StoredTable heap r.a xs)
    (configuration : Configuration heap r.b (wordTable label) source (label t) (pairTable label))
    (stack : List (Frame ℕ 908)) (tape : Bits) :
    let es := stepPath xs label source (label t)
    let ys := outputTable xs (wordTable label) es
    ∃ (ext : NaturalHeap) (root : ℕ) (g : Flow c s t) (k : ℕ),
      ResidualFlowStepProgram.Output (heap++ext) root ys es ∧
      ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧ Advance f g label es ∧
      NaturalRun program k (state heap r stack tape 0) []
        (state (heap++ext) (r.set .r3 root) stack tape 1) ∧
      k ≤ ResidualFlowStepProgram.instructionBound n B W+8 := by
  obtain ⟨vertices,rest,sRoot,tRoot,hconfig,hrest,hw,hs,he⟩ := configuration
  let outer : Frame ℕ 908 := ⟨1,.r3,r⟩
  let saved := outer::stack
  let first := r.set .r3 rest
  let withVertices := first.set .r1 vertices
  let withSource := withVertices.set .r2 sRoot
  let args := withSource.set .r3 tRoot
  have call : tickNatural program (state heap r stack tape 0)=some ⟨state heap r saved tape 12,[],0⟩ := rfl
  have getRest : tickNatural program (state heap r saved tape 12)=some ⟨state heap first saved tape 13,[],0⟩ := by
    simp [first,state,program,tickNatural,Registers.get,hconfig]
  have getVertices : tickNatural program (state heap first saved tape 13)=
      some ⟨state heap withVertices saved tape 14,[],0⟩ := by
    simp [first,withVertices,state,program,tickNatural,Registers.get,Registers.set,hconfig]
  have getSource : tickNatural program (state heap withVertices saved tape 14)=
      some ⟨state heap withSource saved tape 15,[],0⟩ := by
    simp [first,withVertices,withSource,state,program,tickNatural,Registers.get,Registers.set,hrest]
  have getTarget : tickNatural program (state heap withSource saved tape 15)=
      some ⟨state heap args saved tape 16,[],0⟩ := by
    simp [first,withVertices,withSource,args,state,program,tickNatural,Registers.get,Registers.set,hrest]
  obtain ⟨ext,regs,root,g,hout,hvalues,hfields,hadvance,body,bound⟩ :=
    ResidualFlowStepProgram.certified_step (r:=args) f different xs values fields capacities
      label hlabel labels source hsource sourceWidth input hw hs he tape
  let inner : Frame ℕ 908 := ⟨17,.r3,args⟩
  let stop := state (heap++ext) (regs.set .r3 root) (inner::saved) tape (stepLabel 5)
  let before := state (heap++ext) (args.set .r3 root) saved tape 17
  have enter : tickNatural program (state heap args saved tape 16)=
      some ⟨state heap args (inner::saved) tape (stepLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run stepLabel ResidualFlowStepProgram.program program step_slots body
  have lift := ReferenceProgramStack.run program (inner::saved) lift
  have trace : NaturalRun program (ResidualFlowStepProgram.steps xs (wordTable label) (pairTable label) source (label t))
      (state heap args (inner::saved) tape (stepLabel 0)) [] stop := by
    simpa [stop,state,ResidualFlowStepProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have unwind : tickNatural program stop=some ⟨before,[],0⟩ := by
    simp [stop,before,inner,state,program,stepLabel,tickNatural,Registers.get,Registers.set]
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 1,[],0⟩ := by
    simp [before,outer,saved,state,program,tickNatural,Registers.get,Registers.set]
  have restTrace := NaturalRun.step enter (join trace (.step unwind (.step ret (.done _))))
  have run := NaturalRun.step call (.step getRest (.step getVertices (.step getSource (.step getTarget restTrace))))
  exact ⟨ext,root,g,_,hout,hvalues,hfields,hadvance,run,by omega⟩

def iterationBound (n B W : ℕ) : ℕ := ResidualFlowStepProgram.instructionBound n B W+13

theorem loop_return {heap : NaturalHeap} {r : Registers ℕ} {B W : ℕ} (fuel : ℕ)
    (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (f : Flow c s t) (xs : List (List Entry)) (fits : (cutCapacity c X : ℤ) ≤ f.value+fuel)
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (input : StoredTable heap r.a xs)
    (configuration : Configuration heap r.b (wordTable label) source (label t) (pairTable label))
    (budget : IndexSpine heap r.c fuel)
    (caller : Frame ℕ 908) (stack : List (Frame ℕ 908)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (ys : List (List Entry)) (g : Flow c s t) (k : ℕ),
      StoredTable (heap++ext) root ys ∧ ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧
      ¬Nonempty (SimplePath g.residual s t) ∧
      NaturalRun program k (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) ∧
      k ≤ (fuel+1)*iterationBound n B W := by
  induction fuel using Nat.strong_induction_on generalizing heap r f xs with
  | h fuel ih =>
    have different : s≠t := fun eq => ht (eq ▸ hs)
    let saved := caller::stack
    let es := stepPath xs label source (label t)
    let next := outputTable xs (wordTable label) es
    obtain ⟨ext,result,g,used,hout,hvalues,hfields,hadvance,body,charged⟩ :=
      run_step f different xs values fields capacities label hlabel labels source hsource sourceWidth
        input configuration saved tape
    change ResidualFlowStepProgram.Output (heap++ext) result next es at hout
    change Advance f g label es at hadvance
    obtain ⟨table,edges,hpair,hstored,hedges⟩ := hout
    let mid := heap++ext
    let returned := r.set .r3 result
    let withTable := returned.set .r0 table
    let inspected := withTable.set .r3 edges
    have readTable : tickNatural program (state mid returned saved tape 1)=
        some ⟨state mid withTable saved tape 2,[],0⟩ := by
      simp [mid,returned,withTable,state,program,tickNatural,Registers.get,Registers.set,hpair]
    have readPath : tickNatural program (state mid withTable saved tape 2)=
        some ⟨state mid inspected saved tape 3,[],0⟩ := by
      simp [mid,returned,withTable,inspected,state,program,tickNatural,Registers.get,Registers.set,hpair]
    have pathRep : EdgeList mid inspected.d es := hedges
    have tableRep : StoredTable mid inspected.a next := hstored
    rcases hadvance with ⟨hnil,same,stop⟩ | ⟨p,edgeData,nonempty,augmented⟩
    · have nilTag : mid[inspected.d]?=some .nil := by
        rw [hnil] at pathRep
        cases pathRep with | nil h => exact h
      have selectPath : tickNatural program (state mid inspected saved tape 3)=
          some ⟨state mid inspected saved tape 4,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,nilTag]
      have ret : tickNatural program (state mid inspected saved tape 4)=
          some ⟨state mid (caller.saved.set caller.destination table) stack tape caller.continuation,[],0⟩ := by
        simp [inspected,withTable,returned,saved,state,program,tickNatural,Registers.get,Registers.set]
      have trace := join body (.step readTable (.step readPath (.step selectPath (.step ret (.done _)))))
      have limit : iterationBound n B W ≤ (fuel+1)*iterationBound n B W := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (iterationBound n B W) (Nat.succ_pos fuel)
      refine ⟨ext,table,next,g,used+4,hstored,hvalues,hfields,?_,trace,?_⟩
      · rw [same]
        exact stop
      · have this : used+4 ≤ iterationBound n B W := by unfold iterationBound; omega
        exact this.trans limit
    · have nextValue : g.value=f.value+1 := by
        rw [augmented,Flow.augment_value f p different]
      have pathTag : ∃ head tail,mid[inspected.d]?=some (.pair head tail) := by
        cases he : es with
        | nil => exact (nonempty he).elim
        | cons e rest =>
          rw [he] at pathRep
          cases pathRep with | cons h _ _ => exact ⟨_,_,h⟩
      obtain ⟨head,tail,pathLT⟩ := pathTag
      have selectPath : tickNatural program (state mid inspected saved tape 3)=
          some ⟨state mid inspected saved tape 5,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,pathLT]
      cases budget with
      | nil budgetNil =>
        have limit := weak_duality g X hs ht
        omega
      | @cons _ item remaining m budgetPair budgetTail =>
        let args := inspected.set .r2 remaining
        have budgetTag : mid[inspected.c]?=some (.pair item remaining) := lookup_extend budgetPair ext
        have selectBudget : tickNatural program (state mid inspected saved tape 5)=
            some ⟨state mid inspected saved tape 6,[],0⟩ := by
          simp [state,program,tickNatural,Registers.get,tagBranch,budgetTag]
        have trim : tickNatural program (state mid inspected saved tape 6)=
            some ⟨state mid args saved tape 0,[],0⟩ := by
          simp [args,state,program,tickNatural,Registers.get,budgetTag]
        have hfit : (cutCapacity c X : ℤ) ≤ g.value+m := by omega
        have cfg : Configuration mid args.b (wordTable label) source (label t) (pairTable label) :=
          configuration_extend configuration ext
        have lower : StoredTable mid args.a next := tableRep
        have smaller : IndexSpine mid args.c m := indexSpine_extend budgetTail ext
        obtain ⟨extra,root,ys,out,left,rep,relation,norm,terminal,rest,bound⟩ :=
          ih m (Nat.lt_succ_self m) (heap:=mid) (r:=args) g next hfit hvalues hfields lower cfg smaller
        refine ⟨ext++extra,root,ys,out,used+5+left,?_,relation,norm,terminal,?_,?_⟩
        · simpa only [mid,List.append_assoc] using rep
        · have branch := NaturalRun.step readTable (.step readPath (.step selectPath (.step selectBudget (.step trim rest))))
          have trace := join body branch
          convert trace using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]
        · simp only [Nat.add_mul,Nat.one_mul] at bound ⊢
          unfold iterationBound at bound ⊢
          omega

def instructionBound (n B W fuel : ℕ) : ℕ := (fuel+1)*iterationBound n B W+1

private theorem at_entry (s : NaturalState 908) (hp : s.pc=20) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 20 := by
  cases s
  simp_all [state]

theorem physical_loop {H A B W : ℕ} (fuel : ℕ) (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X)
    (capacities : ∀ u v,(max (c u v) (c v u)).size≤B)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (labels : ∀ i,(label i).length≤W)
    (source : Bits) (hsource : value source=s.val) (sourceWidth : source.length≤W)
    (f : Flow c s t) (xs : List (List Entry)) (fits : (cutCapacity c X : ℤ) ≤ f.value+fuel)
    (values : ValueTable f xs (List.finRange n) (List.finRange n))
    (fields : ∀ row ∈ xs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B)
    (initial : BitState 908) (bounded : initial.Bounded H A) (hp : initial.pc=20) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredTable (eraseState initial).heap (eraseState initial).registers.a xs)
    (configuration : Configuration (eraseState initial).heap (eraseState initial).registers.b
      (wordTable label) source (label t) (pairTable label))
    (budget : IndexSpine (eraseState initial).heap (eraseState initial).registers.c fuel) :
    ∃ (charge k : ℕ) (out : BitState 908) (ys : List (List Entry)) (g : Flow c s t),
      Run program k charge initial [] out ∧ StoredTable (eraseState out).heap (eraseState out).registers.d ys ∧
      ValueTable g ys (List.finRange n) (List.finRange n) ∧
      (∀ row ∈ ys,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧
      ¬Nonempty (SimplePath g.residual s t) ∧ (∀ f' : Flow c s t,f'.value≤g.value) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=21 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 908 H A (instructionBound n B W fuel) := by
  let old := eraseState initial
  let frame : Frame ℕ 908 := ⟨21,.r3,old.registers⟩
  obtain ⟨ext,root,ys,g,k,hrep,hvalues,hfields,terminal,body,hsteps⟩ :=
    loop_return fuel X hs ht capacities label hlabel labels source hsource sourceWidth
      f xs fits values fields input configuration budget frame [] old.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 21
  have call : tickNatural program (state old.heap old.registers [] old.source 20)=
      some ⟨state old.heap old.registers [frame] old.source 0,[],0⟩ := rfl
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (k+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact .step call body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  have optimal := (finiteResidualCut_certificate (ResidualSearch.Enumeration.fin n) g terminal).2.2.2.1
  refine ⟨charge,k+1,out,ys,g,hr,?_,hvalues,hfields,terminal,optimal,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ (Nat.add_le_add_right hsteps 1))⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

theorem terminal_cut_agrees (E D : ResidualSearch.Enumeration (Fin n))
    (g : Flow c s t) (terminal : ¬Nonempty (SimplePath g.residual s t))
    (X : Finset (Fin n)) (hs : s ∈ X) (ht : t ∉ X) :
    finiteResidualCut E g =
      finiteResidualCut D (IntegralNetworkFlow.run (finiteResidualSearch D c s t) (Flow.zero c s t)
        (cutCapacity c X)) := by
  exact finiteResidualCut_eq_of_terminal E D g _ terminal
    (run_stopped_at_cut_budget (finiteResidualSearch D c s t) X hs ht)

end DirectedFlowCutGap.ResidualFlowLoopProgram
