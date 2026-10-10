import DirectedFlowCutGap.EncodedHeavyVertexOutput
import DirectedFlowCutGap.EncodedUniformOutput
import DirectedFlowCutGap.EncodedInputSizing

/-!
# Cost-independent size and mass envelopes for the actual transformed arrays

The abbreviations below name successive checked construction expressions for
proofs. They are not a combined runtime entry or a claim that repeated source
expressions share their evaluations. An executable caller retains the records
once and transports these bounds through their defining equalities.

The positive-objective and nontrivial-uniform hypotheses expose the actual
branches where an integer rounding core is needed. Its retained size N and
cutoff L satisfy N≤24*n² and N/L≤6*W, where W is the original total weight.
After heavy removal the second bound improves to N/L≤3*n/q, q=ceilCube n.
The finite envelope retains this mass restriction explicitly; taking a maximum
over every positive L≤N would lose the useful dependence on W.
-/
namespace DirectedFlowCutGap.EncodedWeightedEnvelope

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication

abbrev prepared {n : ℕ} (D : Input n) := EncodedUnitCostPreparation.build D

abbrev replicated {n : ℕ} (D : Input n) :=
  EncodedUnitCostReplication.materialize (prepared D).data (prepared D).data.counts

abbrev retained {n : ℕ} (D : Input n) := EncodedInputSizing.retainReplica (replicated D)

abbrev expanded {n : ℕ} (D : Input n) := EncodedUniformChain.expand (retained D).data

abbrev heavy {n : ℕ} (D : Input n) :=
  EncodedHeavyVertexPreparation.build D (EncodedCubeRootThreshold.threshold n)

theorem objective_positive {m : ℕ} (D : Input m) (hC : D.totals.objective.num≠0) :
    0<weightedCost D.cost D.weight := by
  rw [← D.totals_objective]
  change (0 : ℝ≥0) < (D.totals.objective.value : ℝ≥0)
  exact_mod_cast (Code.value_pos _).mpr (Nat.pos_of_ne_zero hC)

/-- This is about the actually indexed unit-cost replica, including its
zero-cost terminal copies. -/
theorem replica_mass {m : ℕ} (D : Input m) (hC : D.totals.objective.num≠0) :
    2*totalWeight (materialize D D.counts).input.weight ≤ 3*totalWeight D.weight := by
  rw [Input.actual_normalized_totalWeight]
  have hp := objective_positive D hC
  have h := UnitCostReduction.normalized_copied_weight_le D.cost D.weight hp
  have he := UnitCostReduction.scale_objective D.cost D.weight hp
  nlinarith

theorem replicated_mass {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0) :
    totalWeight (replicated D).input.weight ≤ 3*totalWeight D.weight := by
  have h := replica_mass (prepared D).data hC
  have hp := EncodedUnitCostPreparation.build_totalWeight_le_double D
  change 2*totalWeight (replicated D).input.weight ≤ 3*totalWeight (prepared D).data.weight at h
  nlinarith

theorem retained_mass_eq {n : ℕ} (D : Input n) :
    totalWeight (retained D).data.weight = totalWeight (replicated D).input.weight :=
  EncodedInputSizing.castInput_totalWeight (replicated D).weights.size_toArray.symm (replicated D).input

theorem retained_mass {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0) :
    totalWeight (retained D).data.weight ≤ 3*totalWeight D.weight := by
  exact (retained_mass_eq D).trans_le (replicated_mass D hC)

theorem retained_size {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (prepared D).data.totals.objective.num≠0) :
    (retained D).size≤4*n^2 := by
  rw [(retained D).size_eq]
  exact EncodedUnitCostPreparation.build_clone_count D hn hC

theorem uniform_mass_eq {m : ℕ} (D : Input m) :
    totalWeight (EncodedUniformChain.expand D).data.weight =
      ((EncodedUniformChain.expand D).size : ℝ≥0)*(EncodedUniformWeightParameters.compute D).average.realValue := by
  have hw : (EncodedUniformChain.expand D).data.weight =
      fun _ => (EncodedUniformWeightParameters.compute D).average.realValue := by
    funext i
    exact EncodedUniformChain.materialize_weight (EncodedUniformWeightParameters.compute D).ports
      (EncodedUniformWeightParameters.compute D).average (EncodedUniformWeightParameters.compute D).counts i
  rw [hw]
  simp [totalWeight]

/-- The actual integer reciprocal scale is bounded by the uniform mass, even
when the reciprocal is not an integer and the ceiling is strict. -/
theorem integer_mass_le_uniform {m : ℕ} (D : Input m)
    (hU : EncodedUniformWeightParameters.nontrivial D=true) :
    ((EncodedUniformChain.expand D).size : ℝ≥0)/(EncodedUniformChain.expand D).cutoff ≤
      totalWeight (EncodedUniformChain.expand D).data.weight := by
  have h := EncodedUniformWeightParameters.reciprocal_cutoff_le_average D hU
  rw [uniform_mass_eq,EncodedUniformChain.expand_cutoff]
  simpa only [div_eq_mul_inv,one_mul] using
    mul_le_mul_of_nonneg_left h (show 0≤((EncodedUniformChain.expand D).size : ℝ≥0) from zero_le)

theorem uniform_positive {m : ℕ} (D : Input m)
    (hU : EncodedUniformWeightParameters.nontrivial D=true) :
    0<(EncodedUniformWeightParameters.compute D).total.realValue := by
  rw [EncodedUniformWeightParameters.compute_total]
  exact lt_of_lt_of_le (by norm_num) ((EncodedUniformWeightParameters.nontrivial_iff D).mp hU)

theorem expanded_size {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true) :
    (expanded D).size≤24*n^2 := by
  have h := EncodedUniformChain.expand_size_bound (retained D).data
    (uniform_positive (retained D).data hU)
  have hs := retained_size D hn hC
  change (expanded D).size≤6*(retained D).size at h
  omega

theorem expanded_mass {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true) :
    totalWeight (expanded D).data.weight ≤ 6*totalWeight D.weight := by
  have h := EncodedUniformChain.expand_totalWeight_le (retained D).data
    (uniform_positive (retained D).data hU)
  have hr := retained_mass D hC
  change totalWeight (expanded D).data.weight≤2*totalWeight (retained D).data.weight at h
  nlinarith

theorem expanded_integer_mass {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true) :
    ((expanded D).size : ℝ≥0)/(expanded D).cutoff ≤ 6*totalWeight D.weight :=
  (integer_mass_le_uniform (retained D).data hU).trans (expanded_mass D hC hU)

theorem heavy_expanded_size {n : ℕ} (D : Input n) (hR : 0<(heavy D).size)
    (hC : (prepared (heavy D).data).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained (heavy D).data).data=true) :
    (expanded (heavy D).data).size≤24*n^2 := by
  have h := expanded_size (heavy D).data hR hC hU
  have hs := EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)
  change (heavy D).size≤n at hs
  exact h.trans (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hs 2))

theorem heavy_expanded_mass {n : ℕ} (D : Input n)
    (hC : (prepared (heavy D).data).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained (heavy D).data).data=true) :
    totalWeight (expanded (heavy D).data).data.weight ≤
      3*(n : ℝ≥0)/(EncodedCubeRootThreshold.ceilCube n : ℝ≥0) := by
  have h := expanded_mass (heavy D).data hC hU
  have hr := EncodedHeavyVertexPreparation.build_totalWeight_le D (EncodedCubeRootThreshold.threshold n)
  calc
    _ ≤ 6*totalWeight (heavy D).data.weight := h
    _ ≤ 6*(2*(n : ℝ≥0)*(EncodedCubeRootThreshold.threshold n).realValue) :=
      mul_le_mul_of_nonneg_left hr zero_le
    _ = _ := by
      rw [EncodedCubeRootThreshold.threshold_value]
      simp only [div_eq_mul_inv,mul_inv_rev]
      norm_num
      ring

theorem heavy_expanded_integer_mass {n : ℕ} (D : Input n)
    (hC : (prepared (heavy D).data).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained (heavy D).data).data=true) :
    ((expanded (heavy D).data).size : ℝ≥0)/(expanded (heavy D).data).cutoff ≤
      3*(n : ℝ≥0)/(EncodedCubeRootThreshold.ceilCube n : ℝ≥0) :=
  (integer_mass_le_uniform (retained (heavy D).data).data hU).trans (heavy_expanded_mass D hC hU)

noncomputable section

/-- Finite admissible actual sizes/cutoffs, restricted by the mass budget.
Its definition depends on original size and fixed weights, never on costs. -/
def admissible (n : ℕ) (B : ℝ≥0) : Finset (ℕ×ℕ) :=
  ((Finset.range (24*n^2+1)).product (Finset.range (24*n^2+1))).filter
    fun p => 0<p.1 ∧ 0<p.2 ∧ p.2≤p.1 ∧ (p.1 : ℝ≥0)/(p.2 : ℝ≥0)≤B

theorem mem_admissible {n N L : ℕ} {B : ℝ≥0}
    (hN : N≤24*n^2) (hL : 0<L) (hLN : L≤N) (hB : (N : ℝ≥0)/(L : ℝ≥0)≤B) :
    (N,L)∈admissible n B := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
    by omega,hL,hLN,hB⟩

/-- A finite maximum supplies uniformity across all cost-dependent clones
without postulating monotonicity of the integer approximation formula. -/
def factor (α : ℕ → ℕ → ℝ≥0) (n : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  (admissible n B).sup fun p => α p.1 p.2

theorem factor_le {α : ℕ → ℕ → ℝ≥0} {n : ℕ} {B A : ℝ≥0}
    (h : ∀ p∈admissible n B, α p.1 p.2≤A) : factor α n B≤A :=
  Finset.sup_le_iff.mpr h

/-- Plain numeric interface, so finite-supremum inference never unfolds a
retained graph construction merely to infer N, L or the mass budget. -/
theorem le_factor_of_bounds (α : ℕ → ℕ → ℝ≥0) (n N L : ℕ) (B : ℝ≥0)
    (hN : N≤24*n^2) (hL : 0<L) (hLN : L≤N) (hB : (N : ℝ≥0)/(L : ℝ≥0)≤B) :
    α N L ≤ factor α n B := by
  exact Finset.le_sup (f := fun p : ℕ×ℕ => α p.1 p.2)
    (mem_admissible (n := n) (N := N) (L := L) (B := B) hN hL hLN hB)

theorem mass_sensitive_factor {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (α : ℕ → ℕ → ℝ≥0) :
    α (expanded D).size (expanded D).cutoff ≤ factor α n (6*totalWeight D.weight) := by
  have hL := EncodedUniformChain.expand_cutoff_bounds (retained D).data hU
  exact le_factor_of_bounds α n (expanded D).size (expanded D).cutoff (6*totalWeight D.weight)
    (expanded_size D hn hC hU) hL.1 hL.2 (expanded_integer_mass D hC hU)

theorem heavy_factor {n : ℕ} (D : Input n) (hR : 0<(heavy D).size)
    (hC : (prepared (heavy D).data).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained (heavy D).data).data=true)
    (α : ℕ → ℕ → ℝ≥0) :
    α (expanded (heavy D).data).size (expanded (heavy D).data).cutoff ≤
      factor α n (3*(n : ℝ≥0)/(EncodedCubeRootThreshold.ceilCube n : ℝ≥0)) := by
  have hL := EncodedUniformChain.expand_cutoff_bounds (retained (heavy D).data).data hU
  exact le_factor_of_bounds α n (expanded (heavy D).data).size (expanded (heavy D).data).cutoff
    (3*(n : ℝ≥0)/(EncodedCubeRootThreshold.ceilCube n : ℝ≥0))
    (heavy_expanded_size D hR hC hU) hL.1 hL.2 (heavy_expanded_integer_mass D hC hU)

end
end DirectedFlowCutGap.EncodedWeightedEnvelope
