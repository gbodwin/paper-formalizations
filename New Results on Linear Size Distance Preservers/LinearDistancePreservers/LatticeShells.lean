/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in mathlib's LICENSE.
Authors: Andrew Yang

The finite shell-decomposition proof below is adapted from the cited mathlib
lemma; the sharp finite-radius specialization is added in this development.
-/
import LinearDistancePreservers.LatticeHull
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Analysis.PSeries
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Finite shell estimates for the weighted lattice-normal sums.
The shell-decomposition proof adapts the finite portion of mathlib's
ZLattice.sum_piFinset_Icc_rpow_le (Andrew Yang, Apache 2.0), without its
summability restriction or its final infinite-series bound. -/
namespace LinearDistancePreservers.LatticeShells
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def box (d R : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Icc (-(R : ℤ)) R)

noncomputable def radius {d : ℕ} (z : Fin d → ℤ) : ℝ :=
  Real.sqrt (∑ i, (z i : ℝ)^2)

theorem coord_le_radius {d : ℕ} (z : Fin d → ℤ) (i : Fin d) :
    |(z i : ℝ)| ≤ radius z := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact single_le_sum (fun j _ => sq_nonneg (z j : ℝ)) (mem_univ i)

theorem box_mono {d a b : ℕ} (hab : a ≤ b) : box d a ⊆ box d b := by
  intro z hz
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := mem_Icc.mp (Fintype.mem_piFinset.mp hz i)
  apply mem_Icc.mpr
  constructor <;> omega

theorem shell_card_bound (d k : ℕ) :
    (box d (k+1) \ box d k).card ≤ 2*d*(2*k+3)^(d-1) := by
  rw [card_sdiff_of_subset (box_mono (by omega))]
  simp only [box,Fintype.card_piFinset,Int.card_Icc,prod_const,card_univ,Fintype.card_fin]
  grind [abs_pow_sub_pow_le (α := ℤ) (2*k+3) (2*k+1) d]

/-- A finite weighted sum over the integer box, valid for every negative
exponent, including the nonsummable exponents needed for deep caps. -/
theorem finite_radial_sum (d R : ℕ) (r : ℝ) (hr : r < 0) :
    ∑ z ∈ box d R, (radius z)^r ≤
      (2*d*3^(d-1) : ℕ) * ∑ k ∈ range R, ((k+1 : ℕ) : ℝ)^(((d-1 : ℕ) : ℝ)+r) := by
  have hs0 : box d 0 = {0} := by ext; simp [box,funext_iff]
  have hzero : (radius (0 : Fin d → ℤ))^r = 0 := by simp [radius,hr.ne]
  calc
    _ = ∑ k ∈ range R, ∑ z ∈ (box d (k+1) \ box d k), (radius z)^r := by
      simp [Finset.sum_eq_sum_range_sdiff _ (fun a b hab => box_mono (d := d) hab),hs0,hzero]
    _ ≤ ∑ k ∈ range R, ∑ z ∈ (box d (k+1) \ box d k), ((k+1 : ℕ) : ℝ)^r := by
      gcongr ∑ k ∈ range R, ∑ z ∈ (box d (k+1) \ box d k), ?_ with k hk z hz
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hr.le
      obtain ⟨j,hj⟩ : ∃ i, z i ∉ Icc (-(k : ℤ)) k := by
        simpa [box] using (mem_sdiff.mp hz).2
      have hcoord : (k : ℤ)+1 ≤ |z j| := by
        by_contra! h
        rw [Int.lt_add_one_iff,abs_le,← Finset.mem_Icc] at h
        exact hj h
      exact (show ((k+1 : ℕ) : ℝ) ≤ |(z j : ℝ)| by exact_mod_cast hcoord).trans
        (coord_le_radius z j)
    _ ≤ ∑ k ∈ range R, (2*d*(3*(k+1))^(d-1) : ℕ)*((k+1 : ℕ) : ℝ)^r := by
      simp only [sum_const,nsmul_eq_mul]
      gcongr with k hk
      exact (shell_card_bound d k).trans (by gcongr; omega)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      push_cast
      rw [mul_pow,Real.rpow_add (by positivity),Real.rpow_natCast]
      ring

/-- The radial power sum needed in the deep-cap estimate. For d≥3,
its shell exponent is nonnegative, so a finite endpoint bound suffices. -/
theorem sharp_weighted_sum (d R : ℕ) (hd : 3 ≤ d) :
    ∑ z ∈ box d R, (radius z)^(-((d : ℝ)+1)/2) ≤
      (2*d*3^(d-1) : ℕ) * (R : ℝ)^(((d : ℝ)-1)/2) := by
  have hr : -((d : ℝ)+1)/2 < 0 := by nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hdim : ((d : ℝ)-3)/2 ≥ 0 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : ((d-1 : ℕ) : ℝ)+(-((d : ℝ)+1)/2) = ((d : ℝ)-3)/2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    ring
  have hh := finite_radial_sum d R _ hr
  rw [he] at hh
  by_cases hR : R = 0
  · subst R
    simp only [sum_range_zero,mul_zero] at hh
    exact hh.trans (by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (Nat.pos_of_ne_zero hR)
  have hsum : (∑ k ∈ range R, ((k+1 : ℕ) : ℝ)^(((d : ℝ)-3)/2)) ≤
      (R : ℝ)*(R : ℝ)^(((d : ℝ)-3)/2) := by
    calc
      _ ≤ ∑ _k ∈ range R, (R : ℝ)^(((d : ℝ)-3)/2) := by
        apply sum_le_sum
        intro k hk
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast mem_range.mp hk) hdim
      _ = _ := by simp
  have hp : (R : ℝ)*(R : ℝ)^(((d : ℝ)-3)/2) = (R : ℝ)^(((d : ℝ)-1)/2) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (R : ℝ)]
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  rw [hp] at hsum
  exact hh.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- The second deep-cap sum: grouping by an integer depth k leaves a
reciprocal-square tail, uniformly bounded by 2. Floor division is retained
in the inner finite box, so no unproved continuous-sum replacement is used. -/
theorem deep_weighted_sum (d R : ℕ) (hd : 3 ≤ d) :
    (∑ k ∈ Icc 1 R, (k : ℝ)^(((d : ℝ)-5)/2) *
      ∑ z ∈ box d (R/k), (radius z)^(-((d : ℝ)+1)/2)) ≤
      (4*d*3^(d-1) : ℕ) * (R : ℝ)^(((d : ℝ)-1)/2) := by
  let C : ℝ := (2*d*3^(d-1) : ℕ)
  let p : ℝ := ((d : ℝ)-1)/2
  let q : ℝ := ((d : ℝ)-5)/2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ p := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [p]; linarith
  have hterm (k : ℕ) (hk : k ∈ Icc 1 R) :
      (k : ℝ)^q * (∑ z ∈ box d (R/k), (radius z)^(-((d : ℝ)+1)/2)) ≤
        C*(R : ℝ)^p*((k : ℝ)^2)⁻¹ := by
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)
    have hbase := sharp_weighted_sum d (R/k) hd
    have hdiv : ((R/k : ℕ) : ℝ)^p ≤ ((R : ℝ)/k)^p :=
      Real.rpow_le_rpow (by positivity) Nat.cast_div_le hp
    have he : (k : ℝ)^q * ((R : ℝ)/k)^p = (R : ℝ)^p*((k : ℝ)^2)⁻¹ := by
      rw [Real.div_rpow (by positivity) hk0.le]
      calc
        _ = (R : ℝ)^p*((k : ℝ)^q/(k : ℝ)^p) := by ring
        _ = (R : ℝ)^p*(k : ℝ)^(q-p) := by rw [Real.rpow_sub hk0]
        _ = _ := by
          have he : q-p = -(2 : ℝ) := by dsimp [q,p]; ring
          rw [he,Real.rpow_neg hk0.le]
          norm_num
    calc
      _ ≤ (k : ℝ)^q*(C*((R/k : ℕ) : ℝ)^p) :=
        mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hk0.le _)
      _ ≤ (k : ℝ)^q*(C*((R : ℝ)/k)^p) := by gcongr
      _ = _ := by rw [mul_left_comm,he]; ring
  have hrecip : (∑ k ∈ Icc 1 R, ((k : ℝ)^2)⁻¹) ≤ 2 := by
    have hs : Icc 1 R = Ioo 0 (R+1) := by ext k; simp; omega
    rw [hs]
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (R+1))
  calc
    _ ≤ ∑ k ∈ Icc 1 R, C*(R : ℝ)^p*((k : ℝ)^2)⁻¹ := sum_le_sum hterm
    _ = C*(R : ℝ)^p * ∑ k ∈ Icc 1 R, ((k : ℝ)^2)⁻¹ := by rw [mul_sum]
    _ ≤ C*(R : ℝ)^p*2 :=
      mul_le_mul_of_nonneg_left hrecip (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    _ = _ := by dsimp [C,p]; push_cast; ring

end LinearDistancePreservers.LatticeShells
