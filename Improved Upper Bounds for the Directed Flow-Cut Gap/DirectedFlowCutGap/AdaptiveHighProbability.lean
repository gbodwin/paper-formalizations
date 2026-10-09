import DirectedFlowCutGap.AdaptiveCost

/-!
# Actual valid rounding with expected and high-probability size bounds

All parameters below are explicit functions of the graph size. The underlying
law is the bounded adaptive algorithm, starting from its genuine uniform
fractional cuts. Independent repetition returns the smallest sampled valid
cut. This establishes mathematical probability guarantees, not implementation
or polynomial running time of the noncomputable optimization choices.
-/
namespace DirectedFlowCutGap.AdaptiveHighProbability
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule AdaptiveCost FiniteAmplification EpochParameterBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The proved restart parameter as a nonnegative real. -/
def restartFactor (n : ℕ) : ℝ≥0 := ⟨SubpolynomialBounds.r n, (SubpolynomialBounds.r_pos n).le⟩

@[simp] theorem coe_restartFactor (n : ℕ) : (restartFactor n : ℝ) = SubpolynomialBounds.r n := rfl

theorem restartFactor_one_lt (n : ℕ) : 1 < restartFactor n := by
  exact_mod_cast SubpolynomialBounds.one_lt_r n

/-- A fixed epoch failure budget; its logarithm depends only on the input size. -/
def confidenceHeight (n : ℕ) : ℝ :=
  Real.log (((SubpolynomialBounds.J n : ℝ) + 1) * ((n : ℝ) + 2) ^ (3 : ℕ))

theorem confidenceHeight_nonneg (n : ℕ) : 0 ≤ confidenceHeight n :=
  confidence_log_nonneg 3 n

/-- The actual worst-case failure cost is at most one per epoch. -/
theorem confidenceHeight_failure (n : ℕ) :
    (n : ℝ) ^ (3 : ℕ) * Real.exp (-confidenceHeight n) ≤ 1 := by
  have hx : 0 < ((SubpolynomialBounds.J n : ℝ) + 1) * ((n : ℝ) + 2) ^ (3 : ℕ) := by positivity
  rw [confidenceHeight, Real.exp_neg, Real.exp_log hx, ← div_eq_mul_inv]
  apply (div_le_iff₀ hx).mpr
  simp only [one_mul]
  have hn : (n : ℝ) ^ (3 : ℕ) ≤ ((n : ℝ) + 2) ^ (3 : ℕ) := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 3
  have hJ : (1 : ℝ) ≤ (SubpolynomialBounds.J n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (SubpolynomialBounds.J n)
    linarith
  exact hn.trans (le_mul_of_one_le_left (by positivity) hJ)

/-- The genuine uniform initial mass satisfies the geometric fuel budget. -/
theorem initial_fuel_bound (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    (initial G L hL).mass <
      restartFactor (Fintype.card V) ^ (SubpolynomialBounds.J (Fintype.card V) + 1) := by
  apply (initial_mass_le_cube G L hL).trans_lt
  exact_mod_cast SubpolynomialBounds.cubic_lt_next_restart_power (Fintype.card V)

/-- The actual adaptive cut law with a proved geometric number of epochs. -/
def roundingLaw (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) : PMF (Finset V) :=
  boundedOutput (restartFactor (Fintype.card V)) (restartFactor_one_lt _)
    (SubpolynomialBounds.J (Fintype.card V) + 1) (initial G L hL)

/-- Every supported run internally cuts all original distance-threshold demands. -/
theorem roundingLaw_valid (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L)
    {X : Finset V} (hX : X ∈ (roundingLaw G L hL).support) :
    IsIntegralCut G X (unweightedDemands G L : Set (V × V)) :=
  boundedOutput_valid _ _ _ _ (initial_fuel_bound G L hL) hX

/-- The explicit hard-regime expected bound, for the actual output of the algorithm. -/
theorem roundingLaw_expected (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L)
    (hHard : 64 * SubpolynomialBounds.B (Fintype.card V) ≤ (L : ℝ))
    (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ (3 : ℕ)) :
    expectedCost (roundingLaw G L hL) (fun X => (X.card : ℝ)) ≤
      expectedCostEnvelope 3 (Fintype.card V) * sizeFactor V L := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn : 0 < Fintype.card V := by exact_mod_cast lt_of_lt_of_le zero_lt_one (hLreal.trans hLn)
  let : Nonempty V := Fintype.card_pos_iff.mp hn
  have hB : ((4 ^ SubpolynomialBounds.J (Fintype.card V) * (initial G L hL).scale : ℝ≥0) : ℝ) ≤
      SubpolynomialBounds.B (Fintype.card V) := by
    simp [initial, SubpolynomialBounds.B]
  have he := boundedOutput_expected (restartFactor (Fintype.card V)) (restartFactor_one_lt _)
    (initial G L hL) (SubpolynomialBounds.J (Fintype.card V))
    (SubpolynomialBounds.B (Fintype.card V)) (confidenceHeight (Fintype.card V))
    (by exact le_rfl) (initial_fuel_bound G L hL) hB hHard hLn hnL
    (confidenceHeight_nonneg _) (confidenceHeight_failure _)
  simpa only [roundingLaw, initial, Finset.card_empty, Nat.cast_zero, zero_add,
    epochCostBound, coe_restartFactor, expectedCostEnvelope, K, confidenceHeight, mul_assoc] using he

/-- Independently repeat the actual algorithm and retain a smallest returned cut. -/
def amplifiedLaw (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) (κ : ℝ) : PMF (Finset V) :=
  outputLaw (roundingLaw G L hL) (fun X => (X.card : ℝ))
    (sampleCount_pos (Fintype.card V : ℝ) κ)

theorem amplifiedLaw_valid (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) (κ : ℝ)
    {X : Finset V} (hX : X ∈ (amplifiedLaw G L hL κ).support) :
    IsIntegralCut G X (unweightedDemands G L : Set (V × V)) := by
  exact roundingLaw_valid G L hL (support_outputLaw_subset _ _ _ hX)

/-- A proved finite independent experiment gives polynomially small size failure. -/
theorem amplifiedLaw_failure (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L)
    (hHard : 64 * SubpolynomialBounds.B (Fintype.card V) ≤ (L : ℝ))
    (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ (3 : ℕ))
    (κ : ℝ) (hκ : 0 ≤ κ) :
    probability (amplifiedLaw G L hL κ)
      (fun X => 2 * (expectedCostEnvelope 3 (Fintype.card V) * sizeFactor V L) < (X.card : ℝ)) ≤
      (Fintype.card V : ℝ) ^ (-κ) := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn : (1 : ℝ) ≤ Fintype.card V := hLreal.trans hLn
  have hpositive : 0 < expectedCostEnvelope 3 (Fintype.card V) * sizeFactor V L := by
    apply mul_pos (expectedCostEnvelope_pos 3 _)
    unfold sizeFactor
    exact Real.rpow_pos_of_pos (div_pos (lt_of_lt_of_le zero_lt_one hn)
      (lt_of_lt_of_le zero_lt_one hLreal)) _
  exact probability_output_cost_gt_twice_le_polynomial (roundingLaw G L hL) (fun X => (X.card : ℝ))
    (fun X => Nat.cast_nonneg X.card) hpositive (roundingLaw_expected G L hL hHard hLn hnL)
    (Fintype.card V : ℝ) κ hn hκ

/-- The prefactor for actual hard-regime rounding is uniformly subpolynomial,
with a single constant chosen before the input size and the distance threshold. -/
theorem expected_prefactor_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → 2 * expectedCostEnvelope 3 n ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := expectedCostEnvelope_uniform_bound 3 ε hε
  refine ⟨2 * C, by positivity, fun n hn => ?_⟩
  calc
    _ ≤ 2 * (C * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hbound n hn) (by norm_num)
    _ = _ := by ring

end
end DirectedFlowCutGap.AdaptiveHighProbability
