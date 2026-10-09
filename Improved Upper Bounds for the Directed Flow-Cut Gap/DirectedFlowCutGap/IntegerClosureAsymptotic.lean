import DirectedFlowCutGap.FlexibleClosureRounding
import DirectedFlowCutGap.IntegerEpochParameters
import DirectedFlowCutGap.AdaptiveAsymptotic

/-!
# Integer parameter bounds for the closure-selected law

The restart factor, fuel and cap below are actual natural-number parameters.
The confidence height is used only in the proof. This module analyzes the
closure-selected law directly; it does not identify it with a different
compact-selector law or assert a whole-program runtime bound.
-/
namespace DirectedFlowCutGap.IntegerClosureAsymptotic
noncomputable section
open scoped BigOperators NNReal ENNReal
open SubpolynomialBounds IntegerEpochParameters EpochParameterBridge
open CandidateSchedule AdaptiveCost FiniteAmplification
open CandidateGridOptimizer CandidateThresholdClosure MinimumClosureCut IntegralNetworkFlow

def height (n : ℕ) : ℝ :=
  Real.log (((fuel n : ℝ) + 1) * ((n : ℝ) + 2) ^ (3 : ℕ))

theorem height_nonneg (n : ℕ) : 0 ≤ height n := by
  apply Real.log_nonneg
  have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hf : (1 : ℝ) ≤ (fuel n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (fuel n); linarith
  exact one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hn)

theorem height_failure (n : ℕ) :
    (n : ℝ) ^ (3 : ℕ) * Real.exp (-height n) ≤ 1 := by
  have hp : 0 < ((fuel n : ℝ) + 1) * ((n : ℝ) + 2) ^ (3 : ℕ) := by positivity
  rw [height, Real.exp_neg, Real.exp_log hp, ← div_eq_mul_inv]
  apply (div_le_iff₀ hp).mpr
  simp only [one_mul]
  have hn : (n : ℝ) ^ (3 : ℕ) ≤ ((n : ℝ) + 2) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
  have hf : (1 : ℝ) ≤ (fuel n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (fuel n); linarith
  exact hn.trans (le_mul_of_one_le_left (by positivity) hf)

theorem height_subpolynomial : Subpolynomial height := by
  apply (fuel_add_one_subpolynomial.add
    ((Subpolynomial.const 3).mul log_size_subpolynomial)).mono
  intro n _
  have hlog := (log_size_pos n).le
  rw [abs_of_nonneg (height_nonneg n), abs_of_nonneg (by positivity)]
  have hf : (0 : ℝ) < (fuel n : ℝ) + 1 := by positivity
  have hb := Real.log_le_sub_one_of_pos hf
  rw [height, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- An integer confidence bound avoids any real logarithm comparison in a
future cost-threshold implementation. -/
def confidence (n : ℕ) : ℕ := fuel n + 3 * restart n + 1

theorem height_le_confidence (n : ℕ) : height n ≤ (confidence n : ℝ) := by
  have hf : (0 : ℝ) < (fuel n : ℝ) + 1 := by positivity
  have hb := Real.log_le_sub_one_of_pos hf
  have hr := IntegerEpochParameters.log_size_le_restart n
  rw [height, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  simp only [confidence, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem confidence_subpolynomial : Subpolynomial (fun n => (confidence n : ℝ)) := by
  have h := fuel_add_one_subpolynomial.add ((Subpolynomial.const 3).mul restart_subpolynomial)
  simpa only [confidence, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    add_assoc, add_comm, add_left_comm] using h

theorem confidence_failure (n : ℕ) :
    (n : ℝ) ^ (3 : ℕ) * Real.exp (-(confidence n : ℝ)) ≤ 1 := by
  apply le_trans _ (height_failure n)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (neg_le_neg (height_le_confidence n))

def denominator (n : ℕ) : ℝ := graphDenominator n (cap n) (restart n)

theorem denominator_subpolynomial : Subpolynomial denominator := by
  exact ((((Subpolynomial.const 2048).mul cap_subpolynomial).mul restart_subpolynomial).mul
    (((Subpolynomial.const 256).mul cap_subpolynomial).pow 4)).mul
      log2_add_two_subpolynomial

def envelope (n : ℕ) : ℝ :=
  ((fuel n : ℝ) + 1) *
    ((restart n : ℝ) * denominator n * (confidence n : ℝ) + (cap n : ℝ) + 1)

theorem envelope_subpolynomial : Subpolynomial envelope := by
  exact fuel_add_one_subpolynomial.mul
    ((((restart_subpolynomial.mul denominator_subpolynomial).mul confidence_subpolynomial).add
      cap_subpolynomial).add (Subpolynomial.const 1))

def denominatorCode (n : ℕ) : ℕ :=
  2048 * cap n * restart n * (256 * cap n) ^ 4 * (Nat.log2 n + 2)

def envelopeCode (n : ℕ) : ℕ :=
  (fuel n + 1) * (restart n * denominatorCode n * confidence n + cap n + 1)

theorem denominatorCode_eq (n : ℕ) : (denominatorCode n : ℝ) = denominator n := by
  simp [denominatorCode, denominator, graphDenominator]

theorem envelopeCode_eq (n : ℕ) : (envelopeCode n : ℝ) = envelope n := by
  simp [envelopeCode, envelope, denominatorCode_eq]

theorem envelope_uniform_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → envelope n ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := envelope_subpolynomial ε hε
  exact ⟨C, hC, fun n hn => (le_abs_self _).trans (hb n hn)⟩

theorem restart_nnreal_one_lt (n : ℕ) : 1 < (restart n : ℝ≥0) := by
  exact_mod_cast IntegerEpochParameters.one_lt_restart n

abbrev NetworkEnumeration (V : Type*) (L : ℕ) :=
  ResidualSearch.Enumeration (Vertex (Node (Point V) L))

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem initial_fuel_bound (G : Digraph V) (L : ℕ) (hL : 0 < L) :
    (initial G (L : ℝ≥0) (by exact_mod_cast (show 1 ≤ L by omega))).mass <
      (restart (Fintype.card V) : ℝ≥0) ^ (fuel (Fintype.card V) + 1) := by
  apply (initial_mass_le_cube G (L : ℝ≥0) (by exact_mod_cast (show 1 ≤ L by omega))).trans_lt
  have hp : (Fintype.card V : ℝ≥0) ^ (3 : ℕ) <
      (restart (Fintype.card V) : ℝ≥0) ^ fuel (Fintype.card V) := by
    exact_mod_cast IntegerEpochParameters.cubic_lt_restart_power (Fintype.card V)
  exact hp.trans_le (pow_le_pow_right₀ (restart_nnreal_one_lt _).le (Nat.le_succ _))

/-- This is the actual closure-selected law at fully specified integer parameters. -/
def coreLaw (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L) : PMF (Finset V) :=
  FlexibleClosureRounding.law hL E (restart (Fintype.card V))
    (restart_nnreal_one_lt _) (fuel (Fintype.card V) + 1)
      (initial G (L : ℝ≥0) (by exact_mod_cast (show 1 ≤ L by omega)))

theorem coreLaw_valid (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L) {X : Finset V} (hX : X ∈ (coreLaw G L hL E).support) :
    IsIntegralCut G X (unweightedDemands G (L : ℝ≥0) : Set (V × V)) :=
  FlexibleClosureRounding.law_valid hL E _ _ _ _ (initial_fuel_bound G L hL) hX

theorem coreLaw_expected (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L)
    (hHard : 64 * cap (Fintype.card V) ≤ L) (hLn : L ≤ Fintype.card V)
    (hnL : Fintype.card V ≤ L ^ 3) :
    expectedCost (coreLaw G L hL E) (fun X => (X.card : ℝ)) ≤
      envelope (Fintype.card V) * sizeFactor V (L : ℝ≥0) := by
  let : Nonempty V := Fintype.card_pos_iff.mp (hL.trans_le hLn)
  have hB : ((4 ^ fuel (Fintype.card V) *
      (initial G (L : ℝ≥0) (by exact_mod_cast (show 1 ≤ L by omega))).scale : ℝ≥0) : ℝ) ≤
      (cap (Fintype.card V) : ℝ) := by
    simp [initial, cap]
  have he := FlexibleClosureRounding.law_expected hL E (restart (Fintype.card V))
    (restart_nnreal_one_lt _) (initial G (L : ℝ≥0) (by exact_mod_cast (show 1 ≤ L by omega)))
    (fuel (Fintype.card V)) (cap (Fintype.card V)) (confidence (Fintype.card V))
    (by simp [initial]) (initial_fuel_bound G L hL) hB
    (by exact_mod_cast hHard) (by exact_mod_cast hLn) (by exact_mod_cast hnL)
    (Nat.cast_nonneg _) (confidence_failure _)
  simpa only [coreLaw, initial, Finset.card_empty, Nat.cast_zero, zero_add,
    epochCostBound, envelope, denominator, NNReal.coe_natCast, mul_assoc] using he

/-- Constants are fixed before the graph, threshold, and concrete enumeration. -/
theorem coreLaw_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
        (L : ℕ) (hL : 0 < L) (E : NetworkEnumeration V L),
        64 * cap (Fintype.card V) ≤ L → L ≤ Fintype.card V → Fintype.card V ≤ L ^ 3 →
          expectedCost (coreLaw G L hL E) (fun X => (X.card : ℝ)) ≤
            C * (Fintype.card V : ℝ) ^ ε * sizeFactor V (L : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := envelope_uniform_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ L hL E hHard hLn hnL
  apply (coreLaw_expected G L hL E hHard hLn hnL).trans
  apply mul_le_mul_of_nonneg_right (hb _ (by omega))
  exact Real.rpow_nonneg (by positivity) _

/-- The dispatcher tests natural-number inequalities. The supplied enumeration
is used only in the hard branch; constructing it efficiently is a separate
implementation obligation. -/
def allRegimeLaw (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L) : PMF (Finset V) :=
  if L ≤ Fintype.card V then
    if 64 * cap (Fintype.card V) ≤ L ∧ Fintype.card V ≤ L ^ 3 then
      coreLaw G L hL E
    else PMF.pure Finset.univ
  else PMF.pure ∅

theorem allRegimeLaw_valid (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L) {X : Finset V}
    (hX : X ∈ (allRegimeLaw G L hL E).support) :
    IsIntegralCut G X (unweightedDemands G (L : ℝ≥0) : Set (V × V)) := by
  unfold allRegimeLaw at hX
  split_ifs at hX with hLn hHard
  · exact coreLaw_valid G L hL E hX
  · have he : X = Finset.univ := by simpa using hX
    rw [he]
    exact AdaptiveAsymptotic.univ_valid G (L : ℝ≥0)
      (by exact_mod_cast (show 1 ≤ L by omega))
  · have he : X = ∅ := by simpa using hX
    rw [he]
    apply AdaptiveAsymptotic.empty_valid_of_card_lt
    exact_mod_cast (lt_of_not_ge hLn)

theorem exists_hard_threshold :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      64 * (cap n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have h := ((Subpolynomial.const 64).mul cap_subpolynomial).eventually_le_rpow
    (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
  have hh := hN n ((le_max_left _ _).trans hn)
  simpa only [abs_of_nonneg (by positivity : 0 ≤ (64 : ℝ) * (cap n : ℝ))] using hh

omit [DecidableEq V] in
theorem fallback_cube_le (L : ℕ)
    (hthreshold : 64 * (cap (Fintype.card V) : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3))
    (hHard : ¬(64 * cap (Fintype.card V) ≤ L ∧ Fintype.card V ≤ L ^ 3)) :
    (L : ℝ) ^ (3 : ℕ) ≤ (Fintype.card V : ℝ) := by
  by_cases hc : Fintype.card V ≤ L ^ 3
  · have hl : L < 64 * cap (Fintype.card V) := by omega
    have hlR : (L : ℝ) ≤ 64 * (cap (Fintype.card V) : ℝ) := by exact_mod_cast hl.le
    have hroot : ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) =
        (Fintype.card V : ℝ) := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.rpow_inv_natCast_pow (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
          (by norm_num : (3 : ℕ) ≠ 0)
    rw [← hroot]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hlR.trans hthreshold) _
  · exact_mod_cast (lt_of_not_ge hc).le

theorem allRegimeLaw_expected_envelope (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 < C)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (henvelope : ∀ n : ℕ, 1 ≤ n → envelope n ≤ C * (n : ℝ) ^ ε)
    (hthreshold : ∀ n : ℕ, n₀ ≤ n → 64 * (cap n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3))
    (G : Digraph V) [DecidableRel G.Adj] (L : ℕ) (hL : 0 < L)
    (E : NetworkEnumeration V L) :
    expectedCost (allRegimeLaw G L hL E) (fun X => (X.card : ℝ)) ≤
      max C (n₀ : ℝ) * (Fintype.card V : ℝ) ^ ε * sizeFactor V (L : ℝ≥0) := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hK : 1 ≤ max C (n₀ : ℝ) :=
    (by exact_mod_cast hn₀ : (1 : ℝ) ≤ n₀).trans (le_max_right _ _)
  have hsf : 0 ≤ sizeFactor V (L : ℝ≥0) := Real.rpow_nonneg (by positivity) _
  unfold allRegimeLaw
  split_ifs with hLn hHard
  · apply (coreLaw_expected G L hL E hHard.1 hLn hHard.2).trans
    apply mul_le_mul_of_nonneg_right _ hsf
    exact (henvelope _ (by omega)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · simp only [expectedCost_pure, Finset.card_univ]
    have hLnR : (L : ℝ) ≤ Fintype.card V := by exact_mod_cast hLn
    have hn : (1 : ℝ) ≤ Fintype.card V := hLreal.trans hLnR
    have hp : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ ε := Real.one_le_rpow hn hε
    have hone : 1 ≤ sizeFactor V (L : ℝ≥0) := one_le_sizeFactor hLp hLnR
    by_cases hlarge : n₀ ≤ Fintype.card V
    · have hsmall := fallback_cube_le (V := V) L (hthreshold _ hlarge) hHard
      apply (AdaptiveAsymptotic.card_le_sizeFactor_of_cube_le (L : ℝ≥0) hLp hsmall).trans
      exact le_mul_of_one_le_left hsf (one_le_mul_of_one_le_of_one_le hK hp)
    · have hsmall : (Fintype.card V : ℝ) ≤ max C (n₀ : ℝ) :=
        (by exact_mod_cast (lt_of_not_ge hlarge).le : (Fintype.card V : ℝ) ≤ n₀).trans
          (le_max_right _ _)
      apply hsmall.trans
      exact (le_mul_of_one_le_right (zero_le_one.trans hK) hp).trans
        (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hp)) hone)
  · simp only [expectedCost_pure, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The computed closure-selected law has the full uniform all-regime size
bound with constants fixed before every graph and threshold instance. -/
theorem allRegimeLaw_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
        (L : ℕ) (hL : 0 < L) (E : NetworkEnumeration V L),
          expectedCost (allRegimeLaw G L hL E) (fun X => (X.card : ℝ)) ≤
            C * (Fintype.card V : ℝ) ^ ε * sizeFactor V (L : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC, he⟩ := envelope_uniform_bound ε hε
  obtain ⟨n₀, hn₀, ht⟩ := exists_hard_threshold
  refine ⟨max C (n₀ : ℝ), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro V _ _ G _ L hL E
  exact allRegimeLaw_expected_envelope ε C hε.le hC n₀ hn₀ he ht G L hL E

end
end DirectedFlowCutGap.IntegerClosureAsymptotic
