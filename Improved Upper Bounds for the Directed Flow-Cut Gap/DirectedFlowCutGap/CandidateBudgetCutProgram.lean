import DirectedFlowCutGap.CandidateBudgetProgram

/-!
# Candidate cut with a budget computed from the removal mask

The outer frame preserves the prepared capacity table and search
configuration. The minimum-cut call receives the exact budget pointer
returned by the budget program in the same heap.
-/

namespace DirectedFlowCutGap.CandidateBudgetCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor CandidatePortDifferenceSystem CandidateClosureProvider IntegralNetworkFlow
open EncodedCandidateCapacity (Input)
open CandidatePhysicalCut (networkSize capacityWidth capacities label numberEquiv fuelWord outputMask)
open ResidualZeroTableProgram (CapacityRows CapacityValues capacityRows_extend)
open ResidualFlowLoopProgram (Configuration configuration_extend)
open ResidualFlowStepProgram (wordTable pairTable)
open MinimumClosureCut (source sink)

def budgetLabel (pc : Fin 157) : Fin 1862 := ⟨16+pc.val,by omega⟩
def cutLabel (pc : Fin 1689) : Fin 1862 := ⟨173+pc.val,by omega⟩

def program : Program 1862 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r2
    | 1 => .call (cutLabel 0) 2 .r3
    | 8 => .field .r0 .r2 false 9
    | 9 => .field .r1 .r2 true (budgetLabel 0)
    | _ => .halt
  else if h : pc.val<173 then
    if pc.val=21 then .ret .r3
    else ReferenceProgramLabels.instruction budgetLabel (CandidateBudgetProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=176 then .ret .r3
  else ReferenceProgramLabels.instruction cutLabel
    (ResidualZeroMinCutProgram.program ⟨pc.val-173,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 1862))
    (tape : Bits) (pc : Fin 1862) : NaturalState 1862 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L P : ℕ) : ℕ :=
  CandidateBudgetProgram.instructionBound n P+CandidatePhysicalCut.instructionBound n L+6

private theorem budget_slots (pc : Fin 157) (h : CandidateBudgetProgram.program pc≠.halt) :
    program (budgetLabel pc) = ReferenceProgramLabels.instruction budgetLabel (CandidateBudgetProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,budgetLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<173 by omega,
      show 16+pc.val≠21 by omega]

private theorem cut_slots (pc : Fin 1689) (h : ResidualZeroMinCutProgram.program pc≠.halt) :
    program (cutLabel pc) = ReferenceProgramLabels.instruction cutLabel (ResidualZeroMinCutProgram.program pc) := by
  by_cases hp : pc.val=3
  · have eq : pc=3 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬173+pc.val<16 by omega,show ¬173+pc.val<173 by omega,
      show 173+pc.val≠176 by omega]

private theorem join {s u v : NaturalState 1862} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem budget_call {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ} {flags grid : Bits}
    (pair : heap[r.c]?=some (.pair left right)) (mask : BoolList heap left flags)
    (size : BoolList heap right grid) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (CandidateBudgetProgram.result flags grid) ∧
      NaturalRun program (CandidateBudgetProgram.steps flags grid+4) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 root) [] tape 1) := by
  let withMask := r.set .r0 left
  let args := withMask.set .r1 right
  let frame : Frame ℕ 1862 := ⟨1,.r2,r⟩
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateBudgetProgram.natural_budget (r:=args) mask size tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (budgetLabel 5)
  have enter : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape 8,[],0⟩ := rfl
  have getMask : tickNatural program (state heap r [frame] tape 8)=
      some ⟨state heap withMask [frame] tape 9,[],0⟩ := by
    simp [tickNatural,state,program,withMask,Registers.get,pair]
  have getGrid : tickNatural program (state heap withMask [frame] tape 9)=
      some ⟨state heap args [frame] tape (budgetLabel 0),[],0⟩ := by
    simp [tickNatural,state,program,args,withMask,Registers.get,Registers.set,pair]
  have lift := ReferenceProgramLabels.run budgetLabel CandidateBudgetProgram.program program budget_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (CandidateBudgetProgram.steps flags grid)
      (state heap args [frame] tape (budgetLabel 0)) [] stop := by
    simpa [stop,state,CandidateBudgetProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [stop,frame,state,program,budgetLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (.step getMask (.step getGrid (join trace (.step ret (.done _)))))⟩

variable {n : ℕ}

theorem natural_budget_cut {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits))
    (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (input : CapacityRows heap r.a cs)
    (configuration : Configuration heap r.b (wordTable (label (n:=n) (L:=L)))
      (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink))
      (pairTable (label (n:=n) (L:=L))))
    (pair : heap[r.c]?=some (.pair left right)) (mask : BoolList heap left D.removed.toList)
    (grid : Bits) (size : BoolList heap right grid) (exactGrid : value grid=L) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (outputMask D s t L B EN E) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) ∧
      k ≤ instructionBound n L grid.length := by
  obtain ⟨eb,budget,budgetRep,compute⟩ := budget_call pair mask size tape
  let mid := heap++eb
  let args := r.set .r2 budget
  have exactWord : CandidateBudgetProgram.result D.removed.toList grid=fuelWord D s t L B := by
    rw [CandidateBudgetProgram.result_eq,exactGrid,CandidatePhysicalCut.fuelWord,CandidateBudgetData.budget_exact]
  have stored : BoolList mid args.c (fuelWord D s t L B) := by
    change BoolList (heap++eb) budget (fuelWord D s t L B)
    rw [← exactWord]
    exact budgetRep
  obtain ⟨ec,regs,root,k,rep,body,bound⟩ := CandidatePhysicalCut.natural_candidate_cut (r:=args)
    D s t L B positive feasible EN E cs values widths (capacityRows_extend input eb)
    (configuration_extend configuration eb) stored tape
  let frame : Frame ℕ 1862 := ⟨2,.r3,args⟩
  let stop := state (mid++ec) (regs.set .r3 root) [frame] tape (cutLabel 3)
  have enter : tickNatural program (state mid args [] tape 1)=some ⟨state mid args [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cutLabel ResidualZeroMinCutProgram.program program cut_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program k (state mid args [frame] tape (cutLabel 0)) [] stop := by
    simpa [stop,mid,state,ResidualZeroMinCutProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,List.append_assoc] using lift
  have ret : tickNatural program stop=some ⟨state (mid++ec) (args.set .r3 root) [] tape 2,[],0⟩ := by
    simp [stop,frame,state,program,cutLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨eb++ec,args,root,CandidateBudgetProgram.steps D.removed.toList grid+k+6,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have cut := NaturalRun.step enter (join trace (.step ret (.done _)))
    have run := join compute cut
    convert run using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]
  · have budgetBound := CandidateBudgetProgram.steps_le D.removed.toList grid
    rw [Vector.length_toList] at budgetBound
    unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 1862) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_budget_cut {H A left right : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits))
    (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (initial : BitState 1862) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs)
    (configuration : Configuration (eraseState initial).heap (eraseState initial).registers.b
      (wordTable (label (n:=n) (L:=L))) (label ((numberEquiv n L) source))
      (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))))
    (pair : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair left right))
    (mask : BoolList (eraseState initial).heap left D.removed.toList)
    (grid : Bits) (size : BoolList (eraseState initial).heap right grid) (exactGrid : value grid=L) :
    ∃ (charge steps : ℕ) (out : BitState 1862),
      Run program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (outputMask D s t L B EN E) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=2 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 1862 H A (instructionBound n L grid.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,bound⟩ := natural_budget_cut D s t L B positive feasible
    EN E cs values widths input configuration pair mask grid size exactGrid old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 2
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,k,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ bound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateBudgetCutProgram
