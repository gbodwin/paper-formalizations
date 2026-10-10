import DirectedFlowCutGap.EncodedRoundingProbability

/-!
# Ideal-law quality of the actual repeated rounding entry

The encoded output record is an infinite type because of its counters. We
project only its duplicate-free vertex list to the finite type of cuts, use
the already proved expected-size bound there, and transfer the tail event
back to the actual first-on-ties repeated selector.

The exact sampler-law premise below remains explicit: this is an ideal-law
quality join, not a proof that a bounded fair-bit sampler has the ideal law.
No new executable body or runtime charge is introduced.
-/
namespace DirectedFlowCutGap.EncodedRoundingQuality
noncomputable section
open scoped ENNReal NNReal
open EncodedRoundingEntry EncodedRoundingRepetition RetainedGridState EncodedIntegerShortestPaths
open FiniteAmplification
variable {n L : ℕ}

theorem single_threshold_law [NeZero L]
    (sample : (a : PairFlags n) → PMF (RetainedTapeInput.Tape L a × ℕ))
    (hsample : ∀ a, (sample a).map Prod.fst = RetainedExecutionLaw.sampleTape a)
    (adjacency : PairFlags n) (hL : 0 < L) (threshold : ℕ) :
    (EncodedAllRegimeRounding.run sample adjacency hL).toOuterMeasure
        {o | threshold < o.vertices.length} =
      (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration).toOuterMeasure
        {X | threshold < X.card} := by
  let draw := EncodedAllRegimeRounding.run sample adjacency hL
  have event : draw.toOuterMeasure {o | threshold < o.vertices.length} =
      draw.toOuterMeasure ((fun o => o.vertices.toFinset) ⁻¹' {X | threshold < X.card}) := by
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext o
    constructor
    · intro ⟨ho,hs⟩
      have hn := (EncodedAllRegimeRounding.output_shape sample adjacency hL hs).1
      exact ⟨by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,List.toFinset_card_of_nodup hn] using ho,hs⟩
    · intro ⟨ho,hs⟩
      have hn := (EncodedAllRegimeRounding.output_shape sample adjacency hL hs).1
      exact ⟨by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,List.toFinset_card_of_nodup hn] using ho,hs⟩
  calc
    _ = _ := event
    _ = (draw.map (fun o => o.vertices.toFinset)).toOuterMeasure
        {X | threshold < X.card} := by rw [PMF.toOuterMeasure_map_apply]
    _ = _ := by rw [EncodedAllRegimeRounding.output_law sample hsample adjacency hL]

/-- A finite-law Markov estimate is applied only after the actual-output
projection, avoiding a false finiteness assumption on output records. -/
theorem repeated_half_bound [NeZero L]
    (sample : (a : PairFlags n) → PMF (RetainedTapeInput.Tape L a × ℕ))
    (hsample : ∀ a, (sample a).map Prod.fst = RetainedExecutionLaw.sampleTape a)
    (adjacency : PairFlags n) (hL : 0 < L) (extra threshold : ℕ)
    (hthreshold : 0 < threshold)
    (hexpected : expectedCost
      (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration)
      (fun X => (X.card : ℝ)) ≤ (threshold : ℝ)/2) :
    ((EncodedRoundingRepetition.run sample adjacency hL extra).toOuterMeasure
        {r | threshold < r.selected.vertices.length}).toReal ≤ ((1 : ℝ)/2)^(extra+1) := by
  let p := IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
    (CandidateEnumeration.make n L).network.enumeration
  have hprob : (p.toOuterMeasure {X | threshold < X.card}).toReal ≤ (1 : ℝ)/2 := by
    have hm := threshold_mul_probability_le_expectedCost p (fun X => (X.card : ℝ))
      (fun X => by positivity) (threshold : ℝ) (by positivity)
    have he : {X : Finset (Fin n) | (threshold : ℝ) < (X.card : ℝ)} =
        {X | threshold < X.card} := by ext X; exact_mod_cast (Iff.rfl : threshold < X.card ↔ threshold < X.card)
    unfold probability at hm
    rw [he] at hm
    have ht : (0 : ℝ) < threshold := by exact_mod_cast hthreshold
    change expectedCost p _ ≤ _ at hexpected
    nlinarith
  rw [EncodedRoundingProbability.run_threshold_probability,ENNReal.toReal_pow,
    single_threshold_law sample hsample adjacency hL]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hprob _

/-- Constants are fixed before the graph, threshold and actual typed sampler.
The remaining sampler-law assumption is exactly the existing ideal marginal
contract, and the count is the concrete program's extra+1 executions. -/
theorem uniform_repeated_quality :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n L : ℕ) [NeZero L]
        (sample : (a : PairFlags n) → PMF (RetainedTapeInput.Tape L a × ℕ))
        (_hsample : ∀ a, (sample a).map Prod.fst = RetainedExecutionLaw.sampleTape a)
        (adjacency : PairFlags n) (hL : 0 < L) (extra : ℕ),
        let threshold := Nat.ceil (2 * max 1
          (C * (n : ℝ)^ε * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)))
        ((EncodedRoundingRepetition.run sample adjacency hL extra).toOuterMeasure
          {r | threshold < r.selected.vertices.length}).toReal ≤ ((1 : ℝ)/2)^(extra+1) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := IntegerClosureAsymptotic.allRegimeLaw_expected_uniform ε hε
  refine ⟨C,hC,?_⟩
  intro n L _ sample hsample adjacency hL extra
  let B := C * (n : ℝ)^ε * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)
  have hb : (2 * max 1 B : ℝ) ≤ Nat.ceil (2 * max 1 B) := Nat.le_ceil _
  have hm : (1 : ℝ) ≤ max 1 B := le_max_left _ _
  apply repeated_half_bound sample hsample adjacency hL extra
  · have ht : (0 : ℝ) < Nat.ceil (2 * max 1 B) := by linarith
    exact_mod_cast ht
  · have he := hbound (Fin n) (graph adjacency) L hL
      (CandidateEnumeration.make n L).network.enumeration
    simp only [Fintype.card_fin] at he
    have hbm : B ≤ max 1 B := le_max_right _ _
    change _ ≤ (Nat.ceil (2 * max 1 B) : ℝ)/2
    change _ ≤ B at he
    linarith

end
end DirectedFlowCutGap.EncodedRoundingQuality
