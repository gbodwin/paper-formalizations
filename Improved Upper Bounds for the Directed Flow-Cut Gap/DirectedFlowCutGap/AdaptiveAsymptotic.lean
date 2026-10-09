import DirectedFlowCutGap.AdaptiveHighProbability

/-!
# Uniform all-regime unweighted rounding

The actual law uses the adaptive algorithm in its hard regime, the whole
vertex set in the easy or finite-small-size regime, and the empty cut when
all threshold demands are unreachable. Constants are chosen before the
vertex type, graph, and threshold. All conclusions are mathematical; no
computational complexity is claimed for noncomputable choices.
-/
namespace DirectedFlowCutGap.AdaptiveAsymptotic
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule AdaptiveCost AdaptiveHighProbability FiniteAmplification EpochParameterBridge
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every positive-length demanded path is cut by the whole vertex set. -/
theorem univ_valid (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    IsIntegralCut G Finset.univ (unweightedDemands G L : Set (V × V)) := by
  intro s t hp
  exact cutsPair_mono (Finset.subset_univ _)
    ((uniform_fractional G L hL hp).levelCut_cuts_selected_unit (Set.mem_singleton _) 0 zero_le)

/-- Above the graph-size threshold every demand has no path, so the empty cut is valid. -/
theorem empty_valid_of_card_lt (G : Digraph V) (L : ℝ≥0)
    (hL : (Fintype.card V : ℝ) < L) :
    IsIntegralCut G ∅ (unweightedDemands G L : Set (V × V)) := by
  intro s t hp path
  have hd := (Finset.mem_filter.mp hp).2
  have hc : L ≤ (path.internalVertices.card : ℝ≥0) := by
    simpa using (coe_le_vertexDistance_iff G (fun _ => 1) s t L).mp hd path
  have hcard : (path.internalVertices.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_univ path.internalVertices
  have hcr : (L : ℝ) ≤ (path.internalVertices.card : ℝ) := by exact_mod_cast hc
  exact (not_le_of_gt hL (hcr.trans hcard)).elim

/-- A concrete finite law covering all thresholds at least one. -/
def allRegimeLaw (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) : PMF (Finset V) :=
  if (L : ℝ) ≤ Fintype.card V then
    if 64 * SubpolynomialBounds.B (Fintype.card V) ≤ (L : ℝ) ∧
        (Fintype.card V : ℝ) ≤ (L : ℝ) ^ (3 : ℕ) then roundingLaw G L hL
    else PMF.pure Finset.univ
  else PMF.pure ∅

theorem allRegimeLaw_valid (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L)
    {X : Finset V} (hX : X ∈ (allRegimeLaw G L hL).support) :
    IsIntegralCut G X (unweightedDemands G L : Set (V × V)) := by
  unfold allRegimeLaw at hX
  split_ifs at hX with hLn hHard
  · exact roundingLaw_valid G L hL hX
  · have he : X = Finset.univ := by simpa using hX
    rw [he]
    exact univ_valid G L hL
  · have he : X = ∅ := by simpa using hX
    rw [he]
    exact empty_valid_of_card_lt G L (lt_of_not_ge hLn)

omit [DecidableEq V] in
/-- The easy regime's whole-vertex cut fits the target size scale. -/
theorem card_le_sizeFactor_of_cube_le (L : ℝ≥0) (hL : (0 : ℝ) < L)
    (hsmall : (L : ℝ) ^ (3 : ℕ) ≤ (Fintype.card V : ℝ)) :
    (Fintype.card V : ℝ) ≤ sizeFactor V L := by
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hf : 0 ≤ sizeFactor V L := Real.rpow_nonneg (div_nonneg hn hL.le) _
  have hsquare : (sizeFactor V L) ^ (2 : ℕ) = (n / L) ^ (3 : ℕ) := by
    unfold sizeFactor
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hn hL.le)]
    norm_num
  have hpow : n ^ (2 : ℕ) ≤ (n / L) ^ (3 : ℕ) := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hL 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg n)
    dsimp [n] at *
    nlinarith
  rw [← hsquare] at hpow
  nlinarith

omit [DecidableEq V] in
/-- In the large-size fallback branch, failure of the hard tests forces the easy regime. -/
theorem fallback_cube_le (L : ℝ≥0)
    (hthreshold : 64 * SubpolynomialBounds.B (Fintype.card V) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3))
    (hHard : ¬(64 * SubpolynomialBounds.B (Fintype.card V) ≤ (L : ℝ) ∧
      (Fintype.card V : ℝ) ≤ (L : ℝ) ^ (3 : ℕ))) :
    (L : ℝ) ^ (3 : ℕ) ≤ (Fintype.card V : ℝ) := by
  by_cases hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ (3 : ℕ)
  · have hcap : (L : ℝ) < 64 * SubpolynomialBounds.B (Fintype.card V) :=
      lt_of_not_ge (fun h => hHard ⟨h, hnL⟩)
    have hroot : ((Fintype.card V : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (Fintype.card V : ℝ) := by
      simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
        (by norm_num : (3 : ℕ) ≠ 0)
    rw [← hroot]
    exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (hcap.le.trans hthreshold) 3
  · exact (lt_of_not_ge hnL).le

/-- One explicit prefactor handles hard instances, easy instances, small sizes,
and unreachable demands. Its hypotheses are purely numerical envelopes. -/
theorem allRegimeLaw_expected_envelope (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 < C)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (henvelope : ∀ n : ℕ, 1 ≤ n → expectedCostEnvelope 3 n ≤ C * (n : ℝ) ^ ε)
    (hthreshold : ∀ n : ℕ, n₀ ≤ n → 64 * SubpolynomialBounds.B n ≤ (n : ℝ) ^ ((1 : ℝ) / 3))
    (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    expectedCost (allRegimeLaw G L hL) (fun X => (X.card : ℝ)) ≤
      max C (n₀ : ℝ) * (Fintype.card V : ℝ) ^ ε * sizeFactor V L := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hLreal
  have hK : 1 ≤ max C (n₀ : ℝ) :=
    (by exact_mod_cast hn₀ : (1 : ℝ) ≤ n₀).trans (le_max_right _ _)
  have hsf : 0 ≤ sizeFactor V L := Real.rpow_nonneg (by positivity) _
  unfold allRegimeLaw
  split_ifs with hLn hHard
  · have hn : 1 ≤ Fintype.card V := by exact_mod_cast hLreal.trans hLn
    apply (roundingLaw_expected G L hL hHard.1 hLn hHard.2).trans
    apply mul_le_mul_of_nonneg_right _ hsf
    exact (henvelope _ hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · simp only [expectedCost_pure, Finset.card_univ]
    have hn : (1 : ℝ) ≤ Fintype.card V := hLreal.trans hLn
    have hp : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ ε := Real.one_le_rpow hn hε
    have hone : 1 ≤ sizeFactor V L := one_le_sizeFactor hLp hLn
    by_cases hlarge : n₀ ≤ Fintype.card V
    · have hsmall := fallback_cube_le L (hthreshold _ hlarge) hHard
      apply (card_le_sizeFactor_of_cube_le L hLp hsmall).trans
      exact le_mul_of_one_le_left hsf (one_le_mul_of_one_le_of_one_le hK hp)
    · have hsmall : (Fintype.card V : ℝ) ≤ max C (n₀ : ℝ) :=
        (by exact_mod_cast (lt_of_not_ge hlarge).le : (Fintype.card V : ℝ) ≤ n₀).trans (le_max_right _ _)
      apply hsmall.trans
      exact (le_mul_of_one_le_right (zero_le_one.trans hK) hp).trans
        (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hp)) hone)
  · simp only [expectedCost_pure, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The approximation constant is fixed before `n`, the graph, or `L`. -/
theorem allRegimeLaw_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L),
        expectedCost (allRegimeLaw G L hL) (fun X => (X.card : ℝ)) ≤
          C * (Fintype.card V : ℝ) ^ ε * sizeFactor V L := by
  intro ε hε
  obtain ⟨C, hC, henvelope⟩ := expectedCostEnvelope_uniform_bound 3 ε hε
  obtain ⟨n₀, hn₀, hthreshold⟩ := exists_uniform_hard_regime_threshold
  refine ⟨max C (n₀ : ℝ), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro V _ _ G L hL
  exact allRegimeLaw_expected_envelope ε C hε.le hC n₀ hn₀ henvelope
    (fun n hn => hthreshold n hn (SubpolynomialBounds.B n) le_rfl) G L hL

/-- A finite normalized expectation bound yields a real supported outcome. -/
theorem exists_supported_cost_le {A : Type*} [Fintype A] (p : PMF A) (cost : A → ℝ)
    (B : ℝ) (hB : expectedCost p cost ≤ B) : ∃ a ∈ p.support, cost a ≤ B := by
  by_contra h
  have hbad : ∀ a ∈ p.support, B < cost a := by
    intro a ha
    exact lt_of_not_ge (fun hc => h ⟨a, ha, hc⟩)
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  have hsum : (∑ a, (p a).toReal * B) < expectedCost p cost := by
    apply Finset.sum_lt_sum
    · intro a ha
      by_cases hz : p a = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hbad a hz).le ENNReal.toReal_nonneg
    · exact ⟨a₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hbad a₀ ha₀)
        (ENNReal.toReal_pos ha₀ (p.apply_ne_top a₀))⟩
  rw [← Finset.sum_mul, sum_probability_toReal, one_mul] at hsum
  exact not_lt_of_ge hB hsum

/-- The all-regime existential cut bound is extracted from the proved actual law. -/
theorem exists_unweighted_cut_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (L : ℝ≥0) (_hL : 1 ≤ L),
        ∃ X : Finset V, IsIntegralCut G X (unweightedDemands G L : Set (V × V)) ∧
          (X.card : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ε * sizeFactor V L := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := allRegimeLaw_expected_uniform.{u} ε hε
  refine ⟨C, hC, ?_⟩
  intro V _ _ G L hL
  obtain ⟨X, hX, hcost⟩ := exists_supported_cost_le (allRegimeLaw G L hL)
    (fun X => (X.card : ℝ)) _ (hbound V G L hL)
  exact ⟨X, allRegimeLaw_valid G L hL hX, hcost⟩

/-- Independent repetition of the all-regime law, retaining one actual valid sample. -/
def amplifiedAllRegimeLaw (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) (κ : ℝ) : PMF (Finset V) :=
  outputLaw (allRegimeLaw G L hL) (fun X => (X.card : ℝ))
    (sampleCount_pos (Fintype.card V : ℝ) κ)

theorem amplifiedAllRegimeLaw_valid (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) (κ : ℝ)
    {X : Finset V} (hX : X ∈ (amplifiedAllRegimeLaw G L hL κ).support) :
    IsIntegralCut G X (unweightedDemands G L : Set (V × V)) :=
  allRegimeLaw_valid G L hL (support_outputLaw_subset _ _ _ hX)

/-- The actual all-regime algorithm has polynomially small size failure with
a constant fixed before the graph size, threshold, and confidence exponent. -/
theorem amplifiedAllRegimeLaw_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L),
        1 ≤ Fintype.card V → ∀ κ : ℝ, 0 ≤ κ →
          probability (amplifiedAllRegimeLaw G L hL κ)
            (fun X => C * (Fintype.card V : ℝ) ^ ε * sizeFactor V L < (X.card : ℝ)) ≤
              (Fintype.card V : ℝ) ^ (-κ) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := allRegimeLaw_expected_uniform.{u} ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro V _ _ G L hL hn κ hκ
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hLp : (0 : ℝ) < L := by exact_mod_cast lt_of_lt_of_le zero_lt_one hL
  have hBp : 0 < C * (Fintype.card V : ℝ) ^ ε * sizeFactor V L := by
    apply mul_pos (mul_pos hC (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hnR) _))
    exact Real.rpow_pos_of_pos (div_pos (lt_of_lt_of_le zero_lt_one hnR) hLp) _
  have hprob := probability_output_cost_gt_twice_le_polynomial (allRegimeLaw G L hL)
    (fun X => (X.card : ℝ)) (fun X => Nat.cast_nonneg X.card) hBp (hbound V G L hL)
    (Fintype.card V : ℝ) κ hnR hκ
  simpa only [amplifiedAllRegimeLaw, mul_assoc] using hprob

end
end DirectedFlowCutGap.AdaptiveAsymptotic
