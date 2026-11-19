import DirectedFlowCutGap.ClosureMaxFlowRefinement
import DirectedFlowCutGap.ResidualZeroMinCutProgram
import DirectedFlowCutGap.RetainedCandidateSolver

/-!
# Candidate closure cuts via fixed instructions

The numerical labels are the existing candidate network indices. A
prepared capacity table for the candidate and its stored binary budget
produce exactly the vertex set of the retained optimizer's cut. The
numeric budget and stored capacity widths have explicit bounds in the
original vertex count and grid size.
-/

namespace DirectedFlowCutGap.CandidatePhysicalCut

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated MinimumClosureCut
open CandidatePortDifferenceSystem CandidateClosureProvider
open EncodedCandidateCapacity (Input)
open ResidualZeroTableProgram (CapacityRows CapacityValues)

abbrev networkSize (n L : ℕ) : ℕ := 6*n*(L+1)+2
abbrev budgetCap (n L : ℕ) : ℕ := 6*n*(L+1)
def capacityWidth (n L : ℕ) : ℕ := (2*budgetCap n L+1).size

def number {n L : ℕ} (p : CandidateEnumeration.Network n L) : Fin (networkSize n L) :=
  ⟨CandidateEnumeration.networkIndex p,CandidateEnumeration.networkIndex_lt p⟩

noncomputable def numberEquiv (n L : ℕ) :
    CandidateEnumeration.Network n L ≃ Fin (networkSize n L) :=
  Equiv.ofBijective number ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨fun _ _ h => CandidateEnumeration.networkIndex_injective (congrArg Fin.val h),
      by rw [Input.network_card,Fintype.card_fin]⟩)

@[simp] theorem numberEquiv_value {n L : ℕ} (p : CandidateEnumeration.Network n L) :
    ((numberEquiv n L) p).val=CandidateEnumeration.networkIndex p := rfl

def label {n L : ℕ} (p : Fin (networkSize n L)) : Bits := p.val.bits

theorem label_width {n L : ℕ} (p : Fin (networkSize n L)) :
    (label p).length≤CandidateEnumeration.labelBits n L := by
  rw [label,Nat.size_eq_bits_len]
  exact (Nat.size_le_size p.isLt.le).trans (CandidateEnumeration.network_size_bound n L)

variable {n : ℕ}

abbrev problem (D : Input n) (s t : Fin n) (L B : ℕ) :=
  candidateClosure D.graph s t D.cut L B

noncomputable abbrev capacities (D : Input n) (s t : Fin n) (L B : ℕ) : Capacity (Fin (networkSize n L)) :=
  ClosureMaxFlowRefinement.renamedCapacity (problem D s t L B) (numberEquiv n L)

def fuelWord (D : Input n) (s t : Fin n) (L B : ℕ) : Bits :=
  (budget (problem D s t L B)).bits

def instructionBound (n L : ℕ) : ℕ :=
  ResidualZeroMinCutProgram.instructionBound (networkSize n L) (capacityWidth n L)
    (CandidateEnumeration.labelBits n L) (budgetCap n L) (budgetCap n L).size

noncomputable def outputMask (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L)) : Bits :=
  let old := CountedFlow.solve (D.construct s t L B EN E).cells E source sink
    (D.construct s t L B EN E).budget
  (List.finRange (networkSize n L)).map fun v => decide ((numberEquiv n L).symm v ∈ old.asSet)

private theorem mask_eq (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L)) :
    ClosureMaxFlowRefinement.mask (problem D s t L B) (numberEquiv n L) E = outputMask D s t L B EN E := by
  exact congrArg (fun X : Finset (CandidateEnumeration.Network n L) =>
    (List.finRange (networkSize n L)).map fun v => decide ((numberEquiv n L).symm v ∈ X))
    (EncodedCandidateOutput.solved_cut_value D s t L B EN E).symm

theorem natural_candidate_cut {heap : NaturalHeap} {r : Registers ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits))
    (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (input : CapacityRows heap r.a cs)
    (configuration : ResidualFlowLoopProgram.Configuration heap r.b
      (ResidualFlowStepProgram.wordTable (label (n:=n) (L:=L)))
      (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink))
      (ResidualFlowStepProgram.pairTable (label (n:=n) (L:=L))))
    (storedBudget : BoolList heap r.c (fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (outputMask D s t L B EN E) ∧
      NaturalRun ResidualZeroMinCutProgram.program k (ResidualZeroMinCutProgram.state heap r [] tape 0) []
        (ResidualZeroMinCutProgram.state (heap++ext) (args.set .r3 root) [] tape 3) ∧
      k ≤ instructionBound n L := by
  let P := problem D s t L B
  let e := numberEquiv n L
  let order := ResidualSearch.Enumeration.fin (networkSize n L)
  have hfeas : ∃ T,P.IsClosed T :=
    closure_nonempty (system D.graph s t D.cut L B) (integerCosts D.cut)
      (system_nonempty D.graph s t D.cut L B positive feasible)
  obtain ⟨T,closed⟩ := hfeas
  have numeric : value (fuelWord D s t L B)=budget P := value_bits _
  have fuel : budget P≤budgetCap n L := by
    simpa only [P,Fintype.card_fin] using candidate_budget_le D.graph s t D.cut L B
  have hbound : (2*budget P+1).size≤capacityWidth n L := by
    unfold capacityWidth
    apply Nat.size_le_size
    omega
  have budgetFits := ClosureMaxFlowRefinement.renamed_budget P T closed e
  rw [← numeric] at budgetFits
  obtain ⟨ext,args,root,k,mask,run,paid⟩ := ResidualZeroMinCutProgram.natural_zero_cut
    (fuelWord D s t L B) (ClosureMaxFlowRefinement.separatingSet T e)
    (ClosureMaxFlowRefinement.source_mem T e) (ClosureMaxFlowRefinement.sink_not_mem T e)
    order budgetFits (ClosureMaxFlowRefinement.renamed_widths P e _ hbound)
    (label (n:=n) (L:=L)) (fun i => value_bits i.val) label_width
    (label (e source)) (value_bits _) (label_width (e source))
    cs values widths input configuration storedBudget tape
  have exactMask := (ClosureMaxFlowRefinement.reference_mask P T closed e E order).trans (mask_eq D s t L B EN E)
  refine ⟨ext,args,root,k,?_,run,paid.trans ?_⟩
  · simpa only [exactMask] using mask
  · have wordWidth : (fuelWord D s t L B).length≤(budgetCap n L).size := by
      simpa only [fuelWord,Nat.size_eq_bits_len] using Nat.size_le_size fuel
    rw [numeric]
    unfold instructionBound ResidualZeroMinCutProgram.instructionBound
      ResidualMaxFlowCutProgram.instructionBound ResidualFlowLoopProgram.instructionBound
    gcongr

private theorem at_entry (s : NaturalState 1689) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=ResidualZeroMinCutProgram.state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ResidualZeroMinCutProgram.state]

theorem physical_candidate_cut {H A : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits))
    (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (initial : BitState 1689) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs)
    (configuration : ResidualFlowLoopProgram.Configuration (eraseState initial).heap (eraseState initial).registers.b
      (ResidualFlowStepProgram.wordTable (label (n:=n) (L:=L)))
      (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink))
      (ResidualFlowStepProgram.pairTable (label (n:=n) (L:=L))))
    (storedBudget : BoolList (eraseState initial).heap (eraseState initial).registers.c (fuelWord D s t L B)) :
    ∃ (charge steps : ℕ) (out : BitState 1689),
      Run ResidualZeroMinCutProgram.program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (outputMask D s t L B EN E) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=3 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt ResidualZeroMinCutProgram.program out).result=none ∧
      charge+(attempt ResidualZeroMinCutProgram.program out).operations ≤
        completeBound 1689 H A (instructionBound n L) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,bound⟩ := natural_candidate_cut D s t L B positive feasible
    EN E cs values widths input configuration storedBudget old.source
  let final := ResidualZeroMinCutProgram.state (old.heap++ext) (args.set .r3 root) [] old.source 3
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun ResidualZeroMinCutProgram.program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural ResidualZeroMinCutProgram.program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,k,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ bound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidatePhysicalCut
