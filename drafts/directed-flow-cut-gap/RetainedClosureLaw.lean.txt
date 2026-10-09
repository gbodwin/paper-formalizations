import DirectedFlowCutGap.RetainedExecutionLaw
import DirectedFlowCutGap.RetainedDemandMask

/-!
# The actual masked closure entry realizes the integer core law

The optimizer is identified by equality to the specific closure provider.
Demand-set transport changes only erased mathematical indexing: the executed
entry retains the caller's computable original-demand mask. Both the exact
law and its validity and expected-size bounds therefore apply to actual
retained output, without identifying distinct minimizing vectors.
-/
namespace DirectedFlowCutGap.RetainedClosureLaw
noncomputable section

open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State RetainedGridState
open FlexibleGridProvider RetainedExecutionLaw
open IntegerEpochParameters

variable {n L : ℕ} {G : Digraph (Fin n)} [DecidableRel G.Adj]
variable {D : Finset (Pair n)}

/-- Equality, rather than equality of objective values, fixes the provider. -/
theorem closure_output_law (hL : 0 < L) [NeZero L]
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (Q : Optimizer (providerWitness
      (provider (FlexibleClosureRounding.closureGridOptimizer (G := G) (D := D) hL E))))
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hfuel : (interpret s).mass < (R : ℝ≥0) ^ restartFuel) :
    outputLaw Q hL C R restartFuel epochs s =
      FlexibleClosureRounding.law hL E R hR epochs (interpret s) := by
  rw [RetainedExecutionLaw.output_law Q hL C R restartFuel hR epochs s hfuel,
    selectedProvider_eq]
  rfl

/-- Transporting the original-demand index copies all four state data fields. -/
def castState {D₁ D₂ : Finset (Pair n)} (h : D₁ = D₂)
    (s : State G D₁ (L : ℝ≥0)) : State G D₂ (L : ℝ≥0) where
  remaining := s.remaining
  cut := s.cut
  weight := s.weight
  scale := s.scale
  remaining_subset := by simpa only [← h] using s.remaining_subset
  feasible := s.feasible
  cap := s.cap
  processed := by simpa only [← h] using s.processed

theorem closure_law_cast (hL : 0 < L)
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (R : ℕ) (hR : 1 < (R : ℝ≥0)) (epochs : ℕ)
    {D₁ D₂ : Finset (Pair n)} (h : D₁ = D₂) (s : State G D₁ (L : ℝ≥0)) :
    FlexibleClosureRounding.law hL E R hR epochs s =
      FlexibleClosureRounding.law hL E R hR epochs (castState h s) := by
  cases h
  rfl

omit [DecidableRel G.Adj] in
theorem initialMaskedCode_cast (hL : 1 ≤ (L : ℝ≥0)) (mask : PairFlags n)
    (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0)) :
    castState hmask (interpret (initialMaskedCode G hL mask hmask)) =
      initial G (L : ℝ≥0) hL := by
  calc
    _ = interpret (initialCode G hL mask hmask) := by
      apply state_ext <;> rfl
    _ = _ := interpret_initialCode G hL mask hmask

omit [DecidableRel G.Adj] in
theorem initialMaskedCode_mass (hL : 1 ≤ (L : ℝ≥0)) (mask : PairFlags n)
    (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0)) :
    (interpret (initialMaskedCode G hL mask hmask)).mass =
      (initial G (L : ℝ≥0) hL).mass := by
  rw [← initialMaskedCode_cast hL mask hmask]
  rfl

/-- The public retained entry uses natural arrays, both concrete adapters, and
the supplied computable demand mask. Primitive randomness is supplied by the
exact adaptive finite-tape law. -/
def maskedLaw (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (mask : PairFlags n) (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0)) :
    PMF (Finset (Fin n)) :=
  (sampledRunLaw (tabulatedOptimizer hL EV E) hL (integerCutOracle hL EV)
    (restart n) (fuel n + 1) (fuel n + 1)
    (initialMaskedCode G (by exact_mod_cast (show 1 ≤ L by omega)) mask hmask)).map
      (fun d => cutSet d.result.cache.state.data.cut)

/-- Exact equality to the coordinator's core law at its geometric integer
outer fuel and restart fuel. No minimizer substitution occurs. -/
theorem maskedLaw_eq_coreLaw (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (mask : PairFlags n) (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0)) :
    maskedLaw hL EV E mask hmask = IntegerClosureAsymptotic.coreLaw G L hL E := by
  have hrestart : (interpret (initialMaskedCode G
      (by exact_mod_cast (show 1 ≤ L by omega)) mask hmask)).mass <
        (restart n : ℝ≥0) ^ (fuel n + 1) := by
    rw [initialMaskedCode_mass]
    simpa only [Fintype.card_fin] using IntegerClosureAsymptotic.initial_fuel_bound G L hL
  rw [maskedLaw, sampledRunLaw_output, closure_output_law hL E _ _ _ _
    (IntegerClosureAsymptotic.restart_nnreal_one_lt n) _ _ hrestart,
    closure_law_cast hL E _ _ _ hmask, initialMaskedCode_cast]
  simp only [IntegerClosureAsymptotic.coreLaw, Fintype.card_fin]

theorem maskedLaw_valid (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (mask : PairFlags n) (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0))
    {X : Finset (Fin n)} (hX : X ∈ (maskedLaw hL EV E mask hmask).support) :
    IsIntegralCut G X (unweightedDemands G (L : ℝ≥0) : Set (Pair n)) := by
  rw [maskedLaw_eq_coreLaw hL EV E mask hmask] at hX
  exact IntegerClosureAsymptotic.coreLaw_valid G L hL E hX

theorem maskedLaw_expected (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (mask : PairFlags n) (hmask : remainingSet mask = unweightedDemands G (L : ℝ≥0))
    (hHard : 64 * cap n ≤ L) (hLn : L ≤ n) (hnL : n ≤ L ^ 3) :
    FiniteAmplification.expectedCost (maskedLaw hL EV E mask hmask) (fun X => (X.card : ℝ)) ≤
      IntegerClosureAsymptotic.envelope n * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0) := by
  rw [maskedLaw_eq_coreLaw hL EV E mask hmask]
  simpa only [Fintype.card_fin] using
    IntegerClosureAsymptotic.coreLaw_expected G L hL E
      (by simpa only [Fintype.card_fin] using hHard)
      (by simpa only [Fintype.card_fin] using hLn)
      (by simpa only [Fintype.card_fin] using hnL)

/-- The original-demand mask is itself computed by integer shortest paths. -/
def computedLaw (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L) : PMF (Finset (Fin n)) :=
  maskedLaw hL EV E (RetainedDemandMask.compute G EV L)
    (RetainedDemandMask.compute_correct G EV L)

theorem computedLaw_eq_coreLaw (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L) :
    computedLaw (G := G) hL EV E = IntegerClosureAsymptotic.coreLaw G L hL E :=
  maskedLaw_eq_coreLaw hL EV E _ _

theorem computedLaw_valid (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    {X : Finset (Fin n)} (hX : X ∈ (computedLaw (G := G) hL EV E).support) :
    IsIntegralCut G X (unweightedDemands G (L : ℝ≥0) : Set (Pair n)) := by
  rw [computedLaw_eq_coreLaw hL EV E] at hX
  exact IntegerClosureAsymptotic.coreLaw_valid G L hL E hX

theorem computedLaw_expected (hL : 0 < L) [NeZero L]
    (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L)
    (hHard : 64 * cap n ≤ L) (hLn : L ≤ n) (hnL : n ≤ L ^ 3) :
    FiniteAmplification.expectedCost (computedLaw (G := G) hL EV E) (fun X => (X.card : ℝ)) ≤
      IntegerClosureAsymptotic.envelope n * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0) := by
  exact maskedLaw_expected hL EV E _ _ hHard hLn hnL

/-- Uniform constants are chosen before the concrete graph, threshold,
enumerations, and actual integer execution. -/
theorem computedLaw_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Digraph (Fin n)) [DecidableRel G.Adj]
        (L : ℕ) (hL : 0 < L) [NeZero L]
        (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
        (E : IntegerClosureAsymptotic.NetworkEnumeration (Fin n) L),
        64 * cap n ≤ L → L ≤ n → n ≤ L ^ 3 →
          FiniteAmplification.expectedCost (computedLaw (G := G) hL EV E) (fun X => (X.card : ℝ)) ≤
            C * (n : ℝ) ^ ε * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := IntegerClosureAsymptotic.coreLaw_expected_uniform ε hε
  refine ⟨C, hC, ?_⟩
  intro n G _ L hL _ EV E hHard hLn hnL
  rw [computedLaw_eq_coreLaw hL EV E]
  simpa only [Fintype.card_fin] using hb (Fin n) G L hL E
    (by simpa only [Fintype.card_fin] using hHard)
    (by simpa only [Fintype.card_fin] using hLn)
    (by simpa only [Fintype.card_fin] using hnL)

end
end DirectedFlowCutGap.RetainedClosureLaw
