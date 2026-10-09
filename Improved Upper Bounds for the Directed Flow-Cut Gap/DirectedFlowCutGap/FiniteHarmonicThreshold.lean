import DirectedFlowCutGap.SubpolynomialBounds
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A finite harmonic threshold for unit demand pairs

All distances here are finite and nonnegative. Zero distances and an empty
index type are included in the definitions; the positive-sum hypothesis in
the threshold theorem is exactly what supplies a positive threshold.
-/

namespace DirectedFlowCutGap.FiniteHarmonicThreshold
noncomputable section
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

/-- The finite harmonic number, in the same nonnegative field as lengths. -/
def harmonicWeight (m : ℕ) : ℝ≥0 := ∑ i : Fin m, 1 / ((i.val + 1 : ℕ) : ℝ≥0)

@[simp] theorem harmonicWeight_zero : harmonicWeight 0 = 0 := by
  simp [harmonicWeight]

theorem harmonicWeight_coe (m : ℕ) :
    (harmonicWeight m : ℝ) = (harmonic m : ℝ) := by
  simp only [harmonicWeight, harmonic, NNReal.coe_sum, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_natCast, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simpa only [one_div] using Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / ((i + 1 : ℕ) : ℝ)) m

theorem harmonicWeight_pos {m : ℕ} (hm : 0 < m) : 0 < harmonicWeight m := by
  apply Finset.sum_pos'
  · intro i hi
    exact zero_le
  · exact ⟨⟨0, hm⟩, Finset.mem_univ _, by simp⟩

theorem one_le_harmonicWeight {m : ℕ} (hm : 0 < m) : 1 ≤ harmonicWeight m := by
  have h := Finset.single_le_sum (fun (i : Fin m) _ =>
    (show (0 : ℝ≥0) ≤ 1 / ((i.val + 1 : ℕ) : ℝ≥0) from zero_le))
    (Finset.mem_univ (⟨0, hm⟩ : Fin m))
  simpa [harmonicWeight] using h

/-- A rank maximizer controls the entire finite sum by a harmonic factor. -/
theorem exists_rank_threshold {m : ℕ} (d : Fin m → ℝ≥0)
    (hS : 0 < ∑ i, d i) :
    ∃ i : Fin m, 0 < d i ∧
      (∑ j, d j) ≤ harmonicWeight m * (((i.val + 1 : ℕ) : ℝ≥0) * d i) := by
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    subst m
    simp at hS
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin m => ((i.val + 1 : ℕ) : ℝ≥0) * d i) Finset.univ_nonempty
  have hb : (∑ j, d j) ≤
      harmonicWeight m * (((i.val + 1 : ℕ) : ℝ≥0) * d i) := by
    calc
      (∑ j, d j) ≤ ∑ j : Fin m,
          (((i.val + 1 : ℕ) : ℝ≥0) * d i) / ((j.val + 1 : ℕ) : ℝ≥0) := by
        apply Finset.sum_le_sum
        intro j _hj
        apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < ((j.val + 1 : ℕ) : ℝ≥0))).mpr
        simpa only [mul_comm] using hmax j (Finset.mem_univ j)
      _ = _ := by simp [harmonicWeight, div_eq_mul_inv, Finset.mul_sum, mul_comm]
  refine ⟨i, ?_, hb⟩
  by_contra hn
  have hz : d i = 0 := le_antisymm (le_of_not_gt hn) zero_le
  rw [hz, mul_zero, mul_zero] at hb
  exact (not_le_of_gt hS) hb

/-- The threshold counts actual indices, retaining repeated equal distances. -/
def above {α : Type*} [Fintype α] (d : α → ℝ≥0) (τ : ℝ≥0) : Finset α :=
  Finset.univ.filter (fun p => τ ≤ d p)

theorem above_card_le {α : Type*} [Fintype α] (d : α → ℝ≥0) (τ : ℝ≥0) :
    (above d τ).card ≤ Fintype.card α := Finset.card_le_univ _

/-- A positive threshold separates enough finite demands. No ordering or
distinctness assumption on the distance values is required. -/
theorem exists_threshold {α : Type*} [Fintype α] (d : α → ℝ≥0)
    (hS : 0 < ∑ p, d p) :
    ∃ τ : ℝ≥0, 0 < τ ∧ 0 < (above d τ).card ∧
      (∑ p, d p) ≤ harmonicWeight (Fintype.card α) *
        (τ * ((above d τ).card : ℝ≥0)) := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let σ := Tuple.sort (α := OrderDual ℝ≥0) (fun i : Fin (Fintype.card α) =>
    (d (e i) : OrderDual ℝ≥0))
  let q : Fin (Fintype.card α) ≃ α := σ.trans e
  have hanti : Antitone (fun i => d (q i)) := Tuple.monotone_sort (α := OrderDual ℝ≥0)
    (fun i : Fin (Fintype.card α) => (d (e i) : OrderDual ℝ≥0))
  have hsum : (∑ i, d (q i)) = ∑ p, d p := q.sum_comp d
  obtain ⟨i, hi, hbound⟩ := exists_rank_threshold (fun i => d (q i)) (hsum.symm ▸ hS)
  have hc : i.val + 1 ≤ (above d (d (q i))).card := by
    have hh : (Finset.Iic i).card ≤ (above d (d (q i))).card :=
      Finset.card_le_card_of_injOn q
        (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hanti (Finset.mem_Iic.mp hj)⟩) q.injective.injOn
    simpa only [Fin.card_Iic] using hh
  refine ⟨d (q i), hi, by omega, ?_⟩
  rw [hsum] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (show (((i.val + 1 : ℕ) : ℝ≥0)) ≤
        ((above d (d (q i))).card : ℝ≥0) by exact_mod_cast hc)
          (show (0 : ℝ≥0) ≤ d (q i) from zero_le)) zero_le)

/-- The normalized mass `m W / S` is invariant under positive rescaling. -/
theorem normalized_mass_scale (m : ℕ) (W S a : ℝ≥0) (ha : 0 < a) :
    (m : ℝ≥0) * (a * W) / (a * S) = (m : ℝ≥0) * W / S := by
  rw [mul_left_comm (m : ℝ≥0) a W, mul_div_mul_left _ _ ha.ne']

/-- Passing to the chosen threshold increases normalized mass by at most H. -/
theorem scaled_mass_le (m : ℕ) (W S H τ : ℝ≥0) (hS : 0 < S) (hτ : 0 < τ)
    (hbound : S ≤ H * (τ * (m : ℝ≥0))) :
    W / τ ≤ H * ((m : ℝ≥0) * W / S) := by
  apply (div_le_iff₀ hτ).mpr
  calc
    W = (W / S) * S := by field_simp
    _ ≤ (W / S) * (H * (τ * (m : ℝ≥0))) := mul_le_mul_of_nonneg_left hbound zero_le
    _ = _ := by ring

/-- The cut cost is divided by its actual number of separated unit demands. -/
theorem sparsity_transfer (A C S H τ cost : ℝ≥0) (k q : ℕ)
    (hS : 0 < S) (hτ : 0 < τ) (hk : 0 < k) (hkq : k ≤ q)
    (hbound : S ≤ H * (τ * (k : ℝ≥0))) (hcost : cost ≤ A * (C / τ)) :
    cost / (q : ℝ≥0) ≤ A * H * (C / S) := by
  have hq : (0 : ℝ≥0) < q := by exact_mod_cast (lt_of_lt_of_le hk hkq)
  apply (div_le_iff₀ hq).mpr
  refine hcost.trans ?_
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hτ).mpr
  have hs : S ≤ H * (τ * (q : ℝ≥0)) := hbound.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hkq) zero_le) zero_le)
  calc
    A * C = (A * C / S) * S := by field_simp
    _ ≤ (A * C / S) * (H * (τ * (q : ℝ≥0))) := mul_le_mul_of_nonneg_left hs zero_le
    _ = _ := by ring

/-- The fully degenerate finite case has no positive demanded distance. -/
theorem sum_eq_zero_iff {α : Type*} [Fintype α] (d : α → ℝ≥0) :
    (∑ p, d p) = 0 ↔ ∀ p, d p = 0 := by
  simp

/-- A harmless positive logarithmic envelope for at most n² unit demands. -/
def harmonicEnvelope (n : ℕ) : ℝ≥0 := 1 + 2 * (Real.log ((n : ℝ) + 2)).toNNReal

theorem harmonicEnvelope_coe (n : ℕ) :
    (harmonicEnvelope n : ℝ) = 1 + 2 * Real.log ((n : ℝ) + 2) := by
  simp [harmonicEnvelope, Real.toNNReal_of_nonneg (SubpolynomialBounds.log_size_pos n).le]

theorem one_le_harmonicEnvelope (n : ℕ) : 1 ≤ harmonicEnvelope n := by
  exact le_add_of_nonneg_right zero_le

theorem harmonicWeight_le_envelope {m n : ℕ} (hn : 1 ≤ n) (hm : m ≤ n ^ 2) :
    harmonicWeight m ≤ harmonicEnvelope n := by
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hlog : Real.log (m : ℝ) ≤ 2 * Real.log ((n : ℝ) + 2) := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hmpos (by exact_mod_cast hm)
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.log_le_log hnpos (by linarith)) (by norm_num)
  have hH : (harmonicWeight m : ℝ) ≤ 1 + 2 * Real.log ((n : ℝ) + 2) := by
    rw [harmonicWeight_coe]
    exact (harmonic_le_one_add_log m).trans (by linarith)
  rw [← harmonicEnvelope_coe n] at hH
  exact_mod_cast hH

/-- Both harmonic losses admit every positive power of n, with the constant
chosen before n and before the demand count m. -/
theorem harmonic_factors_uniform (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ≥0, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m ≤ n ^ 2 →
      harmonicWeight m ≤ D * (n : ℝ≥0) ^ η ∧
      harmonicWeight m ^ (3 / 2 : ℝ) ≤ D * (n : ℝ≥0) ^ η := by
  have henv : SubpolynomialBounds.Subpolynomial (fun n => (harmonicEnvelope n : ℝ)) := by
    simpa only [harmonicEnvelope_coe] using
      (SubpolynomialBounds.Subpolynomial.const 1).add
        ((SubpolynomialBounds.Subpolynomial.const 2).mul SubpolynomialBounds.log_size_subpolynomial)
  obtain ⟨C, hC, hb⟩ := henv.pow 2 η hη
  let D : ℝ≥0 := ⟨C, hC.le⟩
  refine ⟨D, by exact_mod_cast hC, ?_⟩
  intro n hn m hm
  have he : harmonicEnvelope n ^ 2 ≤ D * (n : ℝ≥0) ^ η := by
    have h := hb n hn
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h
  have hH := harmonicWeight_le_envelope hn hm
  constructor
  · exact (hH.trans (by nlinarith [one_le_harmonicEnvelope n])).trans he
  · calc
      harmonicWeight m ^ (3 / 2 : ℝ) ≤ harmonicEnvelope n ^ (3 / 2 : ℝ) :=
        NNReal.rpow_le_rpow hH (by norm_num)
      _ ≤ harmonicEnvelope n ^ (2 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le (one_le_harmonicEnvelope n) (by norm_num)
      _ = harmonicEnvelope n ^ (2 : ℕ) := NNReal.rpow_natCast _ 2
      _ ≤ _ := he

end
end DirectedFlowCutGap.FiniteHarmonicThreshold
