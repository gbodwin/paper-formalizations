import DirectedFlowCutGap.FlexibleGridProvider
import DirectedFlowCutGap.CandidateClosureProvider

/-!
# Installing the computed closure output in the independently analyzed law

The grid-only adapter below uses the actual finite residual-path search and
computed residual cut. Every reachable integer-scale restart installs that
specific closure-produced family. The outer PMF obtains its own validity and
expected-cost bounds from FlexibleAdaptiveRounding. This theorem does not
identify the law with the earlier compact-selector law, and does not claim
a complete arithmetic or bit-complexity bound.
-/
namespace DirectedFlowCutGap.FlexibleClosureRounding
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State CandidateOptimization
open FlexibleCandidateSchedule FlexibleGridProvider CandidateClosureProvider
open CandidateGridOptimizer CandidateThresholdClosure MinimumClosureCut IntegralNetworkFlow
open AdaptiveCost FiniteAmplification
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} [DecidableRel G.Adj] {D : Finset (V × V)} {L : ℕ}

omit [Fintype V] [DecidableRel G.Adj] in
/-- Current weights prove nonemptiness at the enlarged cap. They are used
only in this proposition, and are not passed as solver data. -/
theorem current_feasible (S : State G D (L : ℝ≥0)) (B : ℕ)
    (hB : S.scale = (B : ℝ≥0)) :
    ∀ p ∈ S.remaining, CandidateFeasible G p.1 p.2 S.cut L (4 * B) := by
  intro p hp
  have hcap : ((4 * B : ℕ) : ℝ≥0) = 4 * S.scale := by simp [hB]
  refine ⟨installCut S.cut (S.weight p), ?_⟩
  simpa only [hcap] using installCut_candidate G {p} S.cut
    ((4 * S.scale) / (L : ℝ≥0)) (S.weight p) (S.feasible p hp)
      (fun _ hv => S.next_cap hp hv)

/-- The actual finite closure family is the adapter's output data. -/
def closureGridOptimizer (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L))) : GridOptimizer G D L := by
  intro S B hB
  let H := finiteFamilyHooks G S.cut L (4 * B) E
  let hw := current_feasible S B hB
  let w := familyWeights G S.remaining S.cut L (4 * B) hL H hw
  have hc := familyWeights_spec G S.remaining S.cut L (4 * B) hL H hw
  have hcap : ((4 * B : ℕ) : ℝ≥0) = 4 * S.scale := by simp [hB]
  exact ⟨w, fun p hp => by simpa only [hcap] using (hc p hp).1,
    fun p hp => by simpa only [hcap] using (hc p hp).2.2,
    fun p hp => (hc p hp).2.1⟩

/-- At a natural scale the actual installed vector is exactly the computed
closure family. No equality with the compact candidate is used. -/
theorem installed_weight_eq (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (S : State G D (L : ℝ≥0)) (B : ℕ) (hB : S.scale = (B : ℝ≥0)) :
    (S.selectedInstall (provider (closureGridOptimizer hL E))).weight =
      familyWeights G S.remaining S.cut L (4 * B) hL
        (finiteFamilyHooks G S.cut L (4 * B) E) (current_feasible S B hB) := by
  change (provider (closureGridOptimizer hL E)).family S = _
  rw [selected_eq_of_scale _ S B hB]
  rfl

/-- The optimal-mass numerator is computed by summing the actual integer
potential gaps returned by the closure procedure. -/
def optimalNumerator (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (S : State G D (L : ℝ≥0)) (B : ℕ) (hB : S.scale = (B : ℝ≥0)) : ℕ :=
  ∑ p ∈ S.remaining, ∑ v ∈ Finset.univ.filter (fun v => v ∉ S.cut),
    (familyNumerator G S.remaining S.cut L (4 * B) hL
      (finiteFamilyHooks G S.cut L (4 * B) E) (current_feasible S B hB) p v).toNat

theorem optimalNumerator_eq (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (S : State G D (L : ℝ≥0)) (B : ℕ) (hB : S.scale = (B : ℝ≥0)) :
    S.optimum = (optimalNumerator hL E S B hB : ℝ≥0) / L := by
  rw [← (provider (closureGridOptimizer hL E)).objective_eq S,
    selected_eq_of_scale _ S B hB]
  change EpochAccounting.familyMass S.remaining S.cut
    (familyWeights G S.remaining S.cut L (4 * B) hL
      (finiteFamilyHooks G S.cut L (4 * B) E) (current_feasible S B hB)) = _
  apply NNReal.coe_injective
  simp only [EpochAccounting.familyMass, outsideMass, optimalNumerator,
    NNReal.coe_sum, NNReal.coe_div, NNReal.coe_natCast, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro v hv
  rw [familyWeights_numerator]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg
    (familyNumerator_nonneg G S.remaining S.cut L (4 * B) hL
      (finiteFamilyHooks G S.cut L (4 * B) E) (current_feasible S B hB) p v)).symm

/-- Retaining the current integer mass code suffices to obtain both control
codes directly; the optimal code comes from the actual closure output. -/
def directMassCode (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (S : State G D (L : ℝ≥0)) (B current : ℕ) (hB : S.scale = (B : ℝ≥0))
    (hcurrent : S.mass = (current : ℝ≥0) / L) : MassCode S :=
  ⟨current, optimalNumerator hL E S B hB, hcurrent, optimalNumerator_eq hL E S B hB⟩

/-- A natural restart parameter is used with the existing finite epoch law.
For natural-scale initial states all installations use the closure family;
on other states the hybrid fallback remains part of this mathematical law. -/
def law (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (R : ℕ) (hR : 1 < (R : ℝ≥0)) (fuel : ℕ) (S : State G D (L : ℝ≥0)) :
    PMF (Finset V) :=
  FlexibleAdaptiveRounding.boundedOutput (provider (closureGridOptimizer hL E)) R hR fuel S

theorem law_valid (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (R : ℕ) (hR : 1 < (R : ℝ≥0)) (fuel : ℕ) (S : State G D (L : ℝ≥0))
    (hfuel : S.mass < (R : ℝ≥0) ^ fuel) {X : Finset V}
    (hX : X ∈ (law hL E R hR fuel S).support) :
    IsIntegralCut G X (D : Set (V × V)) :=
  FlexibleAdaptiveRounding.boundedOutput_valid _ R hR fuel S hfuel hX

/-- Direct expected-cost guarantee for this closure-selected outer law. The
one-epoch probability/charging proof is used unchanged at its actual states. -/
theorem law_expected [Nonempty V] (hL : 0 < L)
    (E : ResidualSearch.Enumeration (Vertex (Node (Point V) L)))
    (R : ℕ) (hR : 1 < (R : ℝ≥0)) (S : State G D (L : ℝ≥0))
    (J : ℕ) (B H : ℝ) (h₀ : 1 ≤ S.scale)
    (hJ : S.mass < (R : ℝ≥0) ^ (J + 1))
    (hB : ((4 ^ J * S.scale : ℝ≥0) : ℝ) ≤ B)
    (hlarge : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1) :
    expectedCost (law hL E R hR (J + 1) S) (fun X => (X.card : ℝ)) ≤
      (S.cut.card : ℝ) + ((J : ℝ) + 1) * epochCostBound R V (L : ℝ≥0) B H := by
  exact FlexibleAdaptiveRounding.boundedOutput_expected _ R hR S J B H
    h₀ hJ hB (by exact_mod_cast hlarge) (by exact_mod_cast hLn)
    (by exact_mod_cast hnL) hH hfailure

end
end DirectedFlowCutGap.FlexibleClosureRounding
