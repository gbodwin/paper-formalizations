import DirectedFlowCutGap.CandidatePortDifferenceSystem
import DirectedFlowCutGap.MinimumClosureOptimizer
import DirectedFlowCutGap.ResidualPathSearch

/-!
# The actual closure-recursion candidate provider

This module composes the finite integer constraint network, bounded integral
augmentation, computed cut, threshold decoder, and actual candidate weights.
The returned vector is a definition with a theorem about that exact vector.
Feasibility witnesses are used only in proofs, not as optimization oracles.

The solver hooks expose both path search and computed cut extraction. Their
finite implementation uses ResidualPathSearch, including its backward-table
cut; it does not use the classical forward residualReachable set. A complete
operation/encoding bound and schedule integration remain separate obligations.
-/
namespace DirectedFlowCutGap.CandidateClosureProvider

noncomputable section
open scoped BigOperators NNReal
open CandidateGridRounding CandidateGridRounding.DifferenceSystem
open CandidateGridOptimizer CandidatePotentialSoundness
open CandidatePortDifferenceSystem CandidateThresholdClosure
open MinimumClosureProblem MinimumClosureCut MinimumClosureOptimizer IntegralNetworkFlow

section Closure
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Search and cut data are supplied by algorithms. The cut certificate checks
separation and equality with an actual feasible flow, not an assumed optimum. -/
structure SolverHooks (P : Problem A) where
  search : PathSearch (capacity P) source sink
  cut : Flow (capacity P) source sink → Finset (MinimumClosureCut.Vertex A)
  cut_spec : ∀ f : Flow (capacity P) source sink, ¬Nonempty (SimplePath f.residual source sink) →
    source ∈ cut f ∧ sink ∉ cut f ∧ f.value = (cutCapacity (capacity P) (cut f) : ℤ)

/-- Both hooks have actual finite implementations. -/
def finiteHooks (P : Problem A) (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex A)) :
    SolverHooks P where
  search := finiteResidualSearch E (capacity P) source sink
  cut := finiteResidualCut E
  cut_spec := by
    intro f h
    have hc := finiteResidualCut_certificate E f h
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-- The exact closure set extracted from the computed cut of the budgeted run. -/
def closureSet (P : Problem A) (H : SolverHooks P) : Finset A :=
  cores (H.cut (runFlow P H.search))

theorem closureSet_optimal (P : Problem A) (H : SolverHooks P)
    (hfeas : ∃ T, P.IsClosed T) :
    P.IsClosed (closureSet P H) ∧
      ∀ T, P.IsClosed T → P.objective (closureSet P H) ≤ P.objective T := by
  obtain ⟨T₀, hT₀⟩ := hfeas
  have hc := H.cut_spec (runFlow P H.search) (runFlow_no_path P H.search T₀ hT₀)
  apply closure_of_minimum_cut P T₀ hT₀ _ hc.1 hc.2.1
  intro Y hs ht
  have h := weak_duality (runFlow P H.search) Y hs ht
  rw [hc.2.2] at h
  exact_mod_cast h

end Closure

section DifferenceSystem
variable {I : Type*} [Fintype I] [DecidableEq I] {L : ℕ}

theorem closure_nonempty (S : DifferenceSystem I L) (c : I → ℤ)
    (hfeas : ∃ p : I → ℝ, S.Feasible p) : ∃ T, (problem S c).IsClosed T := by
  obtain ⟨p, hp⟩ := hfeas
  obtain ⟨q, _, hq⟩ := S.exists_grid_shiftFloor hp (le_refl 0) zero_lt_one
  exact ⟨encode q, encode_closed S c ((intFeasible_iff S q).mpr hq)⟩

/-- The decoded grid point is data produced by the closure recursion. The real
feasibility certificate is proof-only and does not select the output point. -/
def gridPoint (S : DifferenceSystem I L) (c : I → ℤ) (H : SolverHooks (problem S c))
    (hfeas : ∃ p : I → ℝ, S.Feasible p) : GridPoint I L :=
  decode S c (closureSet (problem S c) H)
    (closureSet_optimal (problem S c) H (closure_nonempty S c hfeas)).1

theorem gridPoint_feasible (S : DifferenceSystem I L) (c : I → ℤ)
    (H : SolverHooks (problem S c)) (hfeas : ∃ p : I → ℝ, S.Feasible p) :
    IntFeasible S (gridPoint S c H hfeas) :=
  decode_feasible S c (closureSet (problem S c) H)
    (closureSet_optimal (problem S c) H (closure_nonempty S c hfeas)).1

/-- The actual decoded output minimizes the linear objective against every
real feasible point; no optimizer is supplied as a premise. -/
theorem gridPoint_minimal (S : DifferenceSystem I L) (c : I → ℤ)
    (H : SolverHooks (problem S c)) (hfeas : ∃ p : I → ℝ, S.Feasible p)
    (p : I → ℝ) (hp : S.Feasible p) :
    CandidateGridRounding.DifferenceSystem.objective (fun i => (c i : ℝ))
      (gridValue (gridPoint S c H hfeas)) ≤
      CandidateGridRounding.DifferenceSystem.objective (fun i => (c i : ℝ)) p := by
  apply S.grid_minimum_le_real (fun i => (c i : ℝ)) (gridPoint S c H hfeas) ?_ hp
  intro q hq
  have hc := closureSet_optimal (problem S c) H (closure_nonempty S c hfeas)
  have hi : integerObjective c (gridPoint S c H hfeas) ≤ integerObjective c q :=
    transfer_minimality S c _ hc.1 hc.2 q ((intFeasible_iff S q).mpr hq)
  rw [← integerObjective_coe, ← integerObjective_coe]
  exact_mod_cast hi

end DifferenceSystem

section Candidates
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Feasibility is a proposition; a real candidate is never read by the solver. -/
def CandidateFeasible (G : Digraph V) (s t : V) (X : Finset V) (L B : ℕ) : Prop :=
  ∃ w : V → ℝ≥0, CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) w

theorem system_nonempty (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (hfeas : CandidateFeasible G s t X L B) :
    ∃ p : Point V → ℝ, (system G s t X L B).Feasible p := by
  obtain ⟨w, hw⟩ := hfeas
  exact ⟨distancePoint G w s L, system_feasible_of_ports G s t X L B
    (distancePoint_feasible G w s t X L B hL hw)⟩

/-- Concrete numerator potentials generated by the candidate's closure network. -/
def candidateGrid (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) : GridPoint (Point V) L :=
  gridPoint (system G s t X L B) (integerCosts X) H (system_nonempty G s t X L B hL hfeas)

theorem candidateGrid_feasible (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) :
    CandidateGridOptimizer.Feasible G s t X L B
      (gridValue (candidateGrid G s t X L B hL H hfeas)) := by
  apply ports_feasible_of_system G s t X L B
  apply (intFeasible_iff (system G s t X L B) _).mp
  exact gridPoint_feasible (system G s t X L B) (integerCosts X) H
    (system_nonempty G s t X L B hL hfeas)

/-- The exact returned weight vector. It sets X to one and uses decoded gap/L
outside X. Its choice is the computed closure output, not a compact minimizer. -/
def candidateWeights (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) : V → ℝ≥0 :=
  let p := gridValue (candidateGrid G s t X L B hL H hfeas)
  candidateWeight X L (before p) (after p)
    (candidateGrid_feasible G s t X L B hL H hfeas).ordered

/-- An explicit integer numerator accompanies the returned weights; callers do
not need classical choice to obtain numerator data from an existential proof. -/
def candidateNumerator (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) (v : V) : ℤ :=
  let q := candidateGrid G s t X L B hL H hfeas
  if v ∈ X then (L : ℤ) else
    ((q (TerminalPorts.core v, true) : ℕ) : ℤ) - (q (TerminalPorts.core v, false) : ℕ)

theorem candidateNumerator_nonneg (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) (v : V) :
    0 ≤ candidateNumerator G s t X L B hL H hfeas v := by
  by_cases hv : v ∈ X
  · simp [candidateNumerator, hv]
  · have h := (candidateGrid_feasible G s t X L B hL H hfeas).ordered (TerminalPorts.core v)
    dsimp only [before, after, gridValue] at h
    simp only [candidateNumerator, ite_eq_right hv]
    apply sub_nonneg.mpr
    exact_mod_cast h

theorem candidateWeights_numerator (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) (v : V) :
    (candidateWeights G s t X L B hL H hfeas v : ℝ) =
      (candidateNumerator G s t X L B hL H hfeas v : ℝ) / L := by
  by_cases hv : v ∈ X
  · simp [candidateWeights, candidateWeight,
      candidateNumerator, hv, Nat.ne_of_gt hL]
  · simp [candidateWeights, candidateWeight,
      candidateNumerator, hv, before, after, gridValue]

theorem candidateNumerator_le (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) (v : V) :
    candidateNumerator G s t X L B hL H hfeas v ≤ L := by
  by_cases hv : v ∈ X
  · simp [candidateNumerator, hv]
  · let q := candidateGrid G s t X L B hL H hfeas
    have hu : ((q (TerminalPorts.core v, true) : ℕ) : ℤ) ≤ L := by
      exact_mod_cast Nat.le_of_lt_succ (q (TerminalPorts.core v, true)).isLt
    have hl : (0 : ℤ) ≤ (q (TerminalPorts.core v, false) : ℕ) := Int.natCast_nonneg _
    simp only [candidateNumerator, ite_eq_right hv]
    exact (sub_le_self _ hl).trans hu

/-- Exact feasibility, integer numerators, and attained real optimality of the
specific weight vector produced by the closure recursion and computed cut. -/
theorem candidateWeights_spec (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : SolverHooks (candidateClosure G s t X L B))
    (hfeas : CandidateFeasible G s t X L B) :
    CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L)
      (candidateWeights G s t X L B hL H hfeas) ∧
    (∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧
      (candidateWeights G s t X L B hL H hfeas v : ℝ) = (k : ℝ) / L) ∧
    ∀ z : V → ℝ≥0, CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) z →
      CandidateOptimization.outsideMass X (candidateWeights G s t X L B hL H hfeas) ≤
        CandidateOptimization.outsideMass X z := by
  let q := candidateGrid G s t X L B hL H hfeas
  let p := gridValue q
  have hp := candidateGrid_feasible G s t X L B hL H hfeas
  refine ⟨hp.candidate hL, ?_, ?_⟩
  · intro v _
    exact ⟨candidateNumerator G s t X L B hL H hfeas v,
      candidateNumerator_nonneg G s t X L B hL H hfeas v,
      candidateWeights_numerator G s t X L B hL H hfeas v⟩
  · intro z hz
    have hzp := system_feasible_of_ports G s t X L B
      (distancePoint_feasible G z s t X L B hL hz)
    have hmin := gridPoint_minimal (system G s t X L B) (integerCosts X) H
      (system_nonempty G s t X L B hL hfeas) (distancePoint G z s L) hzp
    rw [integerCosts_coe] at hmin
    have hcost := hmin.trans (distancePoint_objective_le G z s X L)
    have hmass : (CandidateOptimization.outsideMass X
        (candidateWeights G s t X L B hL H hfeas) : ℝ) =
        CandidateGridRounding.DifferenceSystem.objective (costs X) p / (L : ℝ) := hp.candidate_mass
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hR : (CandidateOptimization.outsideMass X
        (candidateWeights G s t X L B hL H hfeas) : ℝ) ≤
        (CandidateOptimization.outsideMass X z : ℝ) := by
      rw [hmass]
      apply (div_le_iff₀ hLR).mpr
      simpa only [p, q, candidateGrid, mul_comm] using hcost
    exact_mod_cast hR

/-- One enumeration works for every label at a fixed threshold; the graph and
capacities may differ, while the finite vertex type is unchanged. -/
def finiteFamilyHooks (G : Digraph V) [DecidableRel G.Adj]
    (X : Finset V) (L B : ℕ)
    (E : ResidualSearch.Enumeration (MinimumClosureCut.Vertex (Node (Point V) L))) :
    ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B) :=
  fun p => finiteHooks (candidateClosure G p.1 p.2 X L B) E

/-- Exact family data for a schedule provider. Inactive labels have zero weights. -/
def familyWeights (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) : (V × V) → V → ℝ≥0 :=
  fun p => if hp : p ∈ A then candidateWeights G p.1 p.2 X L B hL (H p) (hfeas p hp)
    else fun _ => 0

/-- Explicit numerator arrays for the exact returned family, including zero
codes on inactive labels. -/
def familyNumerator (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) : (V × V) → V → ℤ :=
  fun p => if hp : p ∈ A then candidateNumerator G p.1 p.2 X L B hL (H p) (hfeas p hp)
    else fun _ => 0

theorem familyNumerator_nonneg (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) (p : V × V) (v : V) :
    0 ≤ familyNumerator G A X L B hL H hfeas p v := by
  by_cases hp : p ∈ A
  · simpa only [familyNumerator, dite_eq_left hp] using
      candidateNumerator_nonneg G p.1 p.2 X L B hL (H p) (hfeas p hp) v
  · simp [familyNumerator, hp]

theorem familyWeights_numerator (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) (p : V × V) (v : V) :
    (familyWeights G A X L B hL H hfeas p v : ℝ) =
      (familyNumerator G A X L B hL H hfeas p v : ℝ) / L := by
  by_cases hp : p ∈ A
  · simpa only [familyWeights, familyNumerator, dite_eq_left hp] using
      candidateWeights_numerator G p.1 p.2 X L B hL (H p) (hfeas p hp) v
  · simp [familyWeights, familyNumerator, hp]

theorem familyNumerator_le (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) (p : V × V) (v : V) :
    familyNumerator G A X L B hL H hfeas p v ≤ L := by
  by_cases hp : p ∈ A
  · simpa only [familyNumerator, dite_eq_left hp] using
      candidateNumerator_le G p.1 p.2 X L B hL (H p) (hfeas p hp) v
  · simp [familyNumerator, hp]

/-- Per-label minimality and numerator certificates belong to the exact family
returned above, allowing a schedule to install that very vector. -/
theorem familyWeights_spec (G : Digraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (H : ∀ p : V × V, SolverHooks (candidateClosure G p.1 p.2 X L B))
    (hfeas : ∀ p ∈ A, CandidateFeasible G p.1 p.2 X L B) :
    ∀ p ∈ A,
      CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L)
        (familyWeights G A X L B hL H hfeas p) ∧
      (∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧ (familyWeights G A X L B hL H hfeas p v : ℝ) = (k : ℝ) / L) ∧
      ∀ z : V → ℝ≥0, CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) z →
        CandidateOptimization.outsideMass X (familyWeights G A X L B hL H hfeas p) ≤
          CandidateOptimization.outsideMass X z := by
  intro p hp
  simpa only [familyWeights, dite_eq_left hp] using
    candidateWeights_spec G p.1 p.2 X L B hL (H p) (hfeas p hp)

/-- The actual number of augmentation-recursion steps uses only n and L. -/
theorem candidate_budget_le (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) (X : Finset V) (L B : ℕ) :
    budget (candidateClosure G s t X L B) ≤ 6 * Fintype.card V * (L + 1) :=
  candidateClosure_cost_budget G s t X L B

omit [DecidableEq V] in
/-- Explicit size of the flow network instantiated by this provider. -/
theorem candidate_network_card (L : ℕ) :
    Fintype.card (MinimumClosureCut.Vertex (Node (Point V) L)) =
      6 * Fintype.card V * (L + 1) + 2 := by
  rw [MinimumClosureCut.card_vertex, card_node, card_point]

end Candidates
end
end DirectedFlowCutGap.CandidateClosureProvider
