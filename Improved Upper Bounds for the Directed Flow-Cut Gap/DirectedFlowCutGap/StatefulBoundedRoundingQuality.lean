import DirectedFlowCutGap.AllRegimeBoundedTapeLaw
import DirectedFlowCutGap.StatefulRoundingProbability
import DirectedFlowCutGap.FairBitConfidence

/-!
# Quantitative quality of actual shared-ledger bounded-bit repetition

The concrete callback is bounded rejection driven by fair bits. Its finite-cut
error is paid through the actual guarded entry, then the observed-length law
is amplified by the actual repeated first-on-ties selector while retaining
one physical ledger. Exact ideal marginals are not assumed. The fuel input is
bounded explicitly; producing that input and the whole physical runtime still
require their separate operation/storage joins.
-/
namespace DirectedFlowCutGap.StatefulBoundedRoundingQuality
noncomputable section
open scoped ENNReal NNReal
open RetainedGridState EncodedIntegerShortestPaths BinaryArithmetic BinarySamplerMetadata
open BinaryWeightedSamplingLaw StatefulSamplerProjection FiniteAmplification

variable {n L : ℕ}

private theorem finite_tail_half (p : PMF (Finset (Fin n))) (threshold : ℕ)
    (ht : 0 < threshold)
    (he : expectedCost p (fun X => (X.card : ℝ)) ≤ (threshold : ℝ)/2) :
    probability p (fun X => threshold < X.card) ≤ (1 : ℝ)/2 := by
  have hm := threshold_mul_probability_le_expectedCost p (fun X => (X.card : ℝ))
    (fun X => by positivity) (threshold : ℝ) (by positivity)
  have hevent : {X : Finset (Fin n) | (threshold : ℝ) < (X.card : ℝ)} =
      {X | threshold < X.card} := by
    ext X
    exact_mod_cast (Iff.rfl : threshold < X.card ↔ threshold < X.card)
  unfold probability at hm ⊢
  rw [hevent] at hm
  have ht' : (0 : ℝ)<threshold := by exact_mod_cast ht
  nlinarith

theorem fuel_error_quarter (fuel : Bits)
    (hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 ≤ value fuel) :
    (AllRegimeBoundedTapeLaw.drawBudget n : ℝ)*((1 : ℝ)/2)^(value fuel) ≤ (1 : ℝ)/4 := by
  have hp : ((1 : ℝ)/2)^(value fuel) ≤
      ((1 : ℝ)/2)^(FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hfuel
  have h := (mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (AllRegimeBoundedTapeLaw.drawBudget n))).trans
    (FairBitConfidence.accumulated_failure (AllRegimeBoundedTapeLaw.drawBudget n) 2)
  norm_num at h ⊢
  exact h

/-- The probability refers to the selected record returned by the actual
stateful repeated program. All entering ledgers satisfy the same bound. -/
theorem repeated_three_quarter_bound [NeZero L]
    (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0 < L) (extra threshold : ℕ) (state : Ledger)
    (ht : 0 < threshold)
    (hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 ≤ value fuel)
    (he : expectedCost
      (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration)
      (fun X => (X.card : ℝ)) ≤ (threshold : ℝ)/2) :
    ((observe (EncodedRoundingRepetition.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL extra) state).toOuterMeasure
       {r | threshold < r.selected.vertices.length}).toReal ≤
        ((3 : ℝ)/4)^(extra+1) := by
  let p := FiniteDrawTrees.actual (value fuel) (AllRegimeBoundedTapeLaw.tree adjacency hL)
  let law := p.map Finset.card
  have hm := finite_tail_half _ threshold ht he
  have herr := FiniteDrawTrees.event_le
    (AllRegimeBoundedTapeLaw.tree_within adjacency hL) (value fuel)
    (fun X => threshold < X.card)
  rw [AllRegimeBoundedTapeLaw.tree_ideal] at herr
  have hf := fuel_error_quarter (n := n) fuel hfuel
  have hprob : (law.toOuterMeasure {k | threshold < k}).toReal ≤ (3 : ℝ)/4 := by
    change ((p.map Finset.card).toOuterMeasure _).toReal ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    change probability p (fun X => threshold < X.card) ≤ _
    change probability p _ ≤ _ at herr
    linarith
  rw [EncodedRoundingRepetition.run,
    StatefulRoundingProbability.repeat_threshold_probability _ law
      (fun state => AllRegimeBoundedTapeLaw.length_law fuel cutoff hcut adjacency hL state),
    ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hprob _

/-- A logarithmic numerical trial budget is specified as an actual binary
input word. Its construction cost is not silently included in later runtime claims. -/
def canonicalFuel (n : ℕ) : Bits :=
  (FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2).bits

theorem canonicalFuel_value (n : ℕ) :
    value (canonicalFuel n) = FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 :=
  value_bits _

/-- The graph-size constant is selected before all graph, binary-input,
physical-ledger and repetition parameters. -/
theorem uniform_repeated_quality :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n L : ℕ) [NeZero L] (fuel cutoff : Bits) (_hcut : value cutoff=L)
        (adjacency : PairFlags n) (hL : 0 < L) (extra : ℕ) (state : Ledger)
        (_hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 ≤ value fuel),
        let threshold := Nat.ceil (2*max 1
          (C*(n : ℝ)^ε*AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)))
        ((observe (EncodedRoundingRepetition.run
          (BinaryRetainedTape.callback fairBit fuel cutoff _hcut hL) adjacency hL extra) state).toOuterMeasure
           {r | threshold < r.selected.vertices.length}).toReal ≤
            ((3 : ℝ)/4)^(extra+1) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := IntegerClosureAsymptotic.allRegimeLaw_expected_uniform ε hε
  refine ⟨C,hC,?_⟩
  intro n L _ fuel cutoff hcut adjacency hL extra state hfuel
  let B := C*(n : ℝ)^ε*AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)
  have hb : (2*max 1 B : ℝ) ≤ Nat.ceil (2*max 1 B) := Nat.le_ceil _
  have hm : (1 : ℝ) ≤ max 1 B := le_max_left _ _
  refine repeated_three_quarter_bound fuel cutoff hcut adjacency hL extra _ state ?_ hfuel ?_
  · have ht : (0 : ℝ) < Nat.ceil (2*max 1 B) := by linarith
    exact_mod_cast ht
  · have he := hbound (Fin n) (graph adjacency) L hL
      (CandidateEnumeration.make n L).network.enumeration
    simp only [Fintype.card_fin] at he
    have hbm : B ≤ max 1 B := le_max_right _ _
    change _ ≤ (Nat.ceil (2*max 1 B) : ℝ)/2
    change _ ≤ B at he
    linarith

end
end DirectedFlowCutGap.StatefulBoundedRoundingQuality
