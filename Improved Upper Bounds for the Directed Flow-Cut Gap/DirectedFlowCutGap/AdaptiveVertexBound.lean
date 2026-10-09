import DirectedFlowCutGap.AdaptiveAsymptotic
import DirectedFlowCutGap.UniformWeightReduction
import DirectedFlowCutGap.WeightSelfReduction

/-!
# The uniform vertex rounding bound from the actual adaptive core

The core's approximation constant is chosen before any graph, weight, or
cost. Bounded-instance oracles then account explicitly for the uniform-weight
and cost-replication blowups. The final self-reduction uses the concrete
threshold `1/(4 n^(1/3))`. No favorable-outcome or graph-value oracle is
assumed, and no runtime or flow-cut duality statement is claimed here.
-/
namespace DirectedFlowCutGap.AdaptiveVertexBound
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule AdaptiveCost AdaptiveAsymptotic
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A core estimate whose constant is independent of every finite instance. -/
def UniformCoreEstimate (δ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (G : Digraph U) (a : ℝ≥0), a ≤ 1 →
    ∃ X : Finset U, IsIntegralCut G X (thresholdDemands G (fun _ => a)) ∧
      (X.card : ℝ≥0) ≤ C * (Fintype.card U : ℝ≥0) ^ δ *
        (totalWeight (fun _ : U => a)) ^ (3 / 2 : ℝ)

/-- Positive uniform weights translate exactly to the unweighted threshold used
by the actual adaptive algorithm, with threshold `L=1/a`. -/
theorem uniform_threshold_mem (G : Digraph V) (a : ℝ≥0) (ha : 0 < a)
    {s t : V} (hst : (s, t) ∈ thresholdDemands G (fun _ => a)) :
    (s, t) ∈ unweightedDemands G (1 / a) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (coe_le_vertexDistance_iff G (fun _ => 1) s t (1 / a)).mpr
  intro path
  have hw : 1 ≤ path.weight (fun _ => a) :=
    (isFractionalCut_iff G (fun _ => a) (thresholdDemands G (fun _ => a))).mp
      (isFractionalCut_thresholdDemands G _) s t hst path
  have hc : 1 / a ≤ (path.internalVertices.card : ℝ≥0) :=
    (div_le_iff₀ ha).mpr (by simpa [SimplePath.weight] using hw)
  simpa [SimplePath.weight] using hc

/-- The uniform core estimate is obtained from a supported outcome of the
proved all-regime adaptive law. Zero weights are handled explicitly. -/
theorem exists_uniform_core (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ≥0, 0 < C ∧ UniformCoreEstimate.{u} δ C := by
  obtain ⟨C, hC, hcore⟩ := exists_unweighted_cut_uniform.{u} δ hδ
  refine ⟨⟨C, hC.le⟩, by exact_mod_cast hC, ?_⟩
  intro U _ _ G a ha
  by_cases hzero : a = 0
  · obtain ⟨X, hX, hx⟩ := UnitCostReduction.zero_cost_cut G (fun _ : U => a) (fun _ => 1)
      (by simp [weightedCost, hzero])
    refine ⟨X, hX, ?_⟩
    rw [cutCost_unit] at hx
    rw [hx]
    exact zero_le
  · have hap : 0 < a := pos_iff_ne_zero.mpr hzero
    have hL : (1 : ℝ≥0) ≤ 1 / a := (le_div_iff₀ hap).mpr (by simpa using ha)
    obtain ⟨X, hX, hx⟩ := hcore U G (1 / a) hL
    refine ⟨X, fun s t hst => hX s t (uniform_threshold_mem G a hap hst), ?_⟩
    have he : sizeFactor U (1 / a) = ((totalWeight (fun _ : U => a) : ℝ≥0) : ℝ) ^ (3 / 2 : ℝ) := by
      simp [sizeFactor, totalWeight]
    rw [he] at hx
    exact_mod_cast hx

/-- Factoring a mass power exposes the original fractional objective. -/
theorem mass_three_halves (W : ℝ≥0) :
    W ^ (3 / 2 : ℝ) = W ^ (1 / 2 : ℝ) * W := by
  by_cases hW : W = 0
  · norm_num [hW]
  · rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, NNReal.rpow_add hW, NNReal.rpow_one]

/-- The core theorem supplies an actual uniform-weight oracle on every instance
with bounded size and mass. -/
theorem bounded_uniform_oracle (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0)
    (hcore : UniformCoreEstimate.{u} δ C) (N : ℕ) (B : ℝ≥0) :
    UniformWeightReduction.BoundedUniformRoundingOracle.{u} N B
      (C * (N : ℝ≥0) ^ δ * B ^ (1 / 2 : ℝ)) := by
  intro U _ _ G a ha hn hW
  obtain ⟨X, hX, hx⟩ := hcore U G a ha
  refine ⟨X, hX, hx.trans ?_⟩
  rw [mass_three_halves]
  calc
    _ = (C * (Fintype.card U : ℝ≥0) ^ δ *
        totalWeight (fun _ : U => a) ^ (1 / 2 : ℝ)) * totalWeight (fun _ : U => a) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply mul_le_mul'
      · exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow (by exact_mod_cast hn) hδ) zero_le
      · exact NNReal.rpow_le_rpow hW (by norm_num)

/-- The repaired weight-uniformization reduction is charged at its actual
`6N` vertex and `2B` mass bounds. -/
theorem bounded_unit_oracle (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0)
    (hcore : UniformCoreEstimate.{u} δ C) (N : ℕ) (B : ℝ≥0) :
    UnitCostReduction.BoundedUnitRoundingOracle.{u} N B
      (2 * C * ((6 * N : ℕ) : ℝ≥0) ^ δ * (2 * B) ^ (1 / 2 : ℝ)) := by
  intro U _ _ G w hn hW
  have ho : UniformWeightReduction.BoundedUniformRoundingOracle.{u}
      (6 * Fintype.card U) (2 * totalWeight w)
      (C * ((6 * N : ℕ) : ℝ≥0) ^ δ * (2 * B) ^ (1 / 2 : ℝ)) := by
    intro T _ _ H a ha ht hm
    exact bounded_uniform_oracle δ hδ C hcore (6 * N) (2 * B) T H a ha
      (ht.trans (Nat.mul_le_mul_left 6 hn))
      (hm.trans (mul_le_mul_of_nonneg_left hW zero_le))
  obtain ⟨X, hX, hx⟩ := UniformWeightReduction.threshold_round_of_bounded_uniform_oracle G w _ ho
  exact ⟨X, hX, by simpa only [mul_assoc] using hx⟩

/-- The fixed numerical loss through both graph transformations. -/
def costConstant (δ : ℝ) (C : ℝ≥0) : ℝ≥0 :=
  12 * C * (24 : ℝ≥0) ^ δ * (6 : ℝ≥0) ^ (1 / 2 : ℝ)

theorem cost_factor_identity (δ : ℝ) (C n W : ℝ≥0) :
    6 * (2 * C * (6 * (4 * n ^ 2)) ^ δ * (2 * (3 * W)) ^ (1 / 2 : ℝ)) =
      costConstant δ C * n ^ (2 * δ) * W ^ (1 / 2 : ℝ) := by
  have hn : (n ^ (2 : ℕ)) ^ δ = n ^ (2 * δ) :=
    (NNReal.rpow_natCast_mul n 2 δ).symm
  rw [show (6 : ℝ≥0) * (4 * n ^ 2) = 24 * n ^ 2 by ring,
    show (2 : ℝ≥0) * (3 * W) = 6 * W by ring,
    NNReal.mul_rpow, NNReal.mul_rpow, hn]
  unfold costConstant
  ring

/-- Arbitrary costs are rounded with a size factor depending only on the actual
input size, and mass factor `sqrt(W)`. -/
theorem arbitrary_cost_round (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0)
    (hcore : UniformCoreEstimate.{u} δ C) (G : Digraph V) (w c : V → ℝ≥0) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ (costConstant δ C * (Fintype.card V : ℝ≥0) ^ (2 * δ) *
        totalWeight w ^ (1 / 2 : ℝ)) * weightedCost c w := by
  obtain ⟨X, hX, hx⟩ := UnitCostReduction.threshold_round_of_bounded_unit_oracle G w c _
    (bounded_unit_oracle δ hδ C hcore (4 * (Fintype.card V) ^ 2) (3 * totalWeight w))
  refine ⟨X, hX, ?_⟩
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hx
  rw [cost_factor_identity] at hx
  exact hx

/-- A uniform mass-sensitive vertex bound, with the constant fixed before all
sizes, graphs, weights and costs. Empty instances and zero total mass are included. -/
theorem vertex_weight_rounding_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w c : V → ℝ≥0),
        ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
          cutCost c X ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            totalWeight w ^ (1 / 2 : ℝ)) * weightedCost c w := by
  intro ε hε
  obtain ⟨C, hC, hcore⟩ := exists_uniform_core.{u} (ε / 2) (by positivity)
  refine ⟨costConstant (ε / 2) C, ?_, ?_⟩
  · unfold costConstant
    positivity
  · intro V _ _ G w c
    have he : (2 : ℝ) * (ε / 2) = ε := by ring
    simpa only [he] using arbitrary_cost_round (ε / 2) (by positivity) C hcore G w c

/-- A bounded residual oracle preserves the input-size dependence explicitly. -/
theorem bounded_cost_oracle (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0)
    (hcore : UniformCoreEstimate.{u} δ C) (N : ℕ) (B : ℝ≥0) :
    WeightSelfReduction.BoundedRoundingOracle.{u} N B
      (costConstant δ C * (N : ℝ≥0) ^ (2 * δ) * B ^ (1 / 2 : ℝ)) := by
  intro U _ _ G w c hn hW
  obtain ⟨X, hX, hx⟩ := arbitrary_cost_round δ hδ C hcore G w c
  refine ⟨X, hX, hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply mul_le_mul'
  · exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow (by exact_mod_cast hn) (by positivity)) zero_le
  · exact NNReal.rpow_le_rpow hW (by norm_num)

/-- Concrete self-reduction at exponent one half. Its threshold and residual
budget are the proved actual construction, not an assumed mass reduction. -/
theorem self_reduced_round (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0)
    (hcore : UniformCoreEstimate.{u} δ C) (G : Digraph V) (w c : V → ℝ≥0)
    (hn : 1 ≤ Fintype.card V) :
    ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ ((4 + 2 * costConstant δ C) *
        (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + 2 * δ)) * weightedCost c w := by
  let n := Fintype.card V
  let τ := WeightSelfReduction.powerThreshold n (1 / 2)
  let A := costConstant δ C * (n : ℝ≥0) ^ (2 * δ) *
    (2 * (n : ℝ≥0) * τ) ^ (1 / 2 : ℝ)
  obtain ⟨X, hX, hx⟩ := WeightSelfReduction.round_of_bounded_oracle G w c τ A
    (WeightSelfReduction.powerThreshold_pos n hn (1 / 2))
    (WeightSelfReduction.powerThreshold_le_quarter n hn (1 / 2) (by norm_num))
    (bounded_cost_oracle δ hδ C hcore n (2 * (n : ℝ≥0) * τ))
  refine ⟨X, hX, hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ zero_le
  have hbudget : 2 * (n : ℝ≥0) * τ ≤ (n : ℝ≥0) ^ ((2 : ℝ) / 3) := by
    simpa only [τ, show (1 : ℝ) / (1 + 1 / 2) = 2 / 3 by norm_num] using
      WeightSelfReduction.powerThreshold_budget n hn (1 / 2) (by norm_num)
  have hroot : (2 * (n : ℝ≥0) * τ) ^ (1 / 2 : ℝ) ≤ (n : ℝ≥0) ^ ((1 : ℝ) / 3) := by
    have h := NNReal.rpow_le_rpow hbudget (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← NNReal.rpow_mul] at h
    norm_num at h
    exact h
  have hA : A ≤ costConstant δ C * (n : ℝ≥0) ^ (2 * δ) * (n : ℝ≥0) ^ ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hroot zero_le
  have hτ : 1 / τ = 4 * (n : ℝ≥0) ^ ((1 : ℝ) / 3) := by
    norm_num [τ, WeightSelfReduction.powerThreshold]
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hp : (1 : ℝ≥0) ≤ (n : ℝ≥0) ^ (2 * δ) :=
    NNReal.one_le_rpow (by exact_mod_cast hn) (by positivity)
  rw [hτ, NNReal.rpow_add hnpos.ne']
  have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ≥0) ≤ 4 * (n : ℝ≥0) ^ ((1 : ℝ) / 3) from zero_le)
  nlinarith

/-- The main mathematical vertex-rounding estimate, with its constant chosen
before every graph, weight and cost, including empty and zero-objective cases. -/
theorem vertex_rounding_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w c : V → ℝ≥0),
        ∃ X : Finset V, IsIntegralCut G X (thresholdDemands G w) ∧
          cutCost c X ≤ (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * weightedCost c w := by
  intro ε hε
  obtain ⟨C, hC, hcore⟩ := exists_uniform_core.{u} (ε / 2) (by positivity)
  refine ⟨4 + 2 * costConstant (ε / 2) C, by positivity, ?_⟩
  intro V _ _ G w c
  by_cases hn : 1 ≤ Fintype.card V
  · have he : (2 : ℝ) * (ε / 2) = ε := by ring
    simpa only [he] using self_reduced_round (ε / 2) (by positivity) C hcore G w c hn
  · have hz : Fintype.card V = 0 := by omega
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    refine ⟨∅, ?_, by simp [cutCost]⟩
    intro s
    exact isEmptyElim s

/-- The same verified result in the existing all-cost graph interface. -/
theorem hasVertexRoundingFactor_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w : V → ℝ≥0),
        HasVertexRoundingFactor G w (K * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε)) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := vertex_rounding_uniform.{u} ε hε
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro V _ _ G w
  refine ⟨by positivity, ?_⟩
  intro c
  obtain ⟨X, hX, hx⟩ := hround V G w c
  exact ⟨X, hX, by exact_mod_cast hx⟩

end
end DirectedFlowCutGap.AdaptiveVertexBound
