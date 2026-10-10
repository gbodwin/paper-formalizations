import LinearDistancePreservers.LatticeCaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

namespace LinearDistancePreservers.LatticeCaps
open Finset
variable {D : Type*} [Fintype D]

theorem dot_comm (u v : D → ℝ) : dot u v = dot v u := by
  unfold dot
  apply sum_congr rfl
  intro i _
  ring

theorem dot_add_smul (q u y : D → ℝ) (a : ℝ) :
    dot q (fun i => a*u i+y i) = a*dot q u+dot q y := by
  unfold dot
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring

theorem normSq_smul (y : D → ℝ) (a : ℝ) :
    normSq (fun i => a*y i) = a^2*normSq y := by
  unfold normSq
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- A width bound in q controls its component along the cap axis. -/
theorem cap_width_axial (u q : D → ℝ) (R h W : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hw : ∀ x ∈ cap u R h, ∀ y ∈ cap u R h, dot q x-dot q y ≤ W) :
    h/2*|dot q u| ≤ W := by
  have hRpos : 0 < R := hh.trans_le hR
  have hy : dot u (fun _ => 0) = 0 := by simp [dot]
  have hyR : normSq (fun _ : D => 0) ≤ R*h/4 := by
    simp only [normSq,zero_pow (by decide : 2 ≠ 0),sum_const_zero]
    positivity
  have hp := cylinder_mem_cap u (fun _ => 0) R h (h/4) hu hy hh hR
    (by rw [abs_of_pos (by positivity)]) hyR
  have hm := cylinder_mem_cap u (fun _ => 0) R h (-h/4) hu hy hh hR
    (by rw [neg_div,abs_neg,abs_of_pos (by positivity)]) hyR
  have hpm := hw _ hp _ hm
  have hmp := hw _ hm _ hp
  rw [dot_add_smul,dot_add_smul] at hpm hmp
  rcases le_total 0 (dot q u) with hq | hq
  · rw [abs_of_nonneg hq]; nlinarith
  · rw [abs_of_nonpos hq]; nlinarith

/-- An arbitrary admissible transverse displacement gives a dual-width
bound, before choosing the extremizing displacement. -/
theorem cap_width_transverse (u q y : D → ℝ) (R h W : ℝ)
    (hu : normSq u = 1) (hy : dot u y = 0) (hh : 0 < h) (hR : h ≤ R)
    (hyR : normSq y ≤ R*h/4)
    (hw : ∀ x ∈ cap u R h, ∀ z ∈ cap u R h, dot q x-dot q z ≤ W) :
    2*|dot q y| ≤ W := by
  have hym : dot u (fun i => -y i) = 0 := by simpa [dot] using congrArg Neg.neg hy
  have hyn : normSq (fun i => -y i) = normSq y := by simp [normSq]
  have hp := cylinder_mem_cap u y R h 0 hu hy hh hR (by simp; positivity) hyR
  have hm := cylinder_mem_cap u (fun i => -y i) R h 0 hu hym hh hR
    (by simp; positivity) (by rw [hyn]; exact hyR)
  have hpm := hw _ hp _ hm
  have hmp := hw _ hm _ hp
  have hqm : dot q (fun i => -y i) = -dot q y := by simp [dot]
  rw [dot_add_smul,dot_add_smul,hqm] at hpm hmp
  rcases le_total 0 (dot q y) with hq | hq
  · rw [abs_of_nonneg hq]; linarith
  · rw [abs_of_nonpos hq]; linarith

/-- The cylinder converts any cap-width certificate into a bound on the
whole normal vector. This does not assert the flatness certificate exists. -/
theorem cap_width_normSq (u q : D → ℝ) (R h W : ℝ)
    (hu : normSq u = 1) (hh : 0 < h) (hR : h ≤ R)
    (hw : ∀ x ∈ cap u R h, ∀ z ∈ cap u R h, dot q x-dot q z ≤ W) :
    h^2*normSq q ≤ 5*W^2 := by
  let a := dot u q
  let v : D → ℝ := fun i => q i-a*u i
  have hv : dot u v = 0 := by
    dsimp [v,dot]
    simp only [mul_sub,sum_sub_distrib]
    have he : (∑ i, u i*(a*u i)) = a*normSq u := by
      unfold normSq
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he,hu,mul_one]
    change a-a = 0
    ring
  have hq : q = fun i => a*u i+v i := by funext i; dsimp [v]; ring
  have hnorm : normSq q = a^2+normSq v := by
    conv_lhs => rw [hq]
    exact normSq_axial u v a hu hv
  have hqv : dot q v = normSq v := by
    rw [dot_comm q v]
    conv_lhs => rw [hq]
    rw [dot_add_smul,dot_comm v u,hv]
    simp [dot,normSq,pow_two]
  have hax := cap_width_axial u q R h W hu hh hR hw
  rw [dot_comm q u] at hax
  change h/2*|a| ≤ W at hax
  have hW : 0 ≤ W := (by positivity : 0 ≤ h/2*|a|).trans hax
  have hax2 := pow_le_pow_left₀ (by positivity : 0 ≤ h/2*|a|) hax 2
  have hax' : h^2*a^2 ≤ 4*W^2 := by
    rw [mul_pow, sq_abs] at hax2
    nlinarith
  have hV0 := normSq_nonneg v
  have hperp : h^2*normSq v ≤ W^2 := by
    by_cases hv0 : normSq v = 0
    · rw [hv0,mul_zero]; positivity
    have hV : 0 < normSq v := lt_of_le_of_ne hV0 (Ne.symm hv0)
    have hRpos : 0 < R := hh.trans_le hR
    let c := Real.sqrt (R*h*normSq v)/(2*normSq v)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hsqrt : Real.sqrt (R*h*normSq v)^2 = R*h*normSq v := Real.sq_sqrt (by positivity)
    let y : D → ℝ := fun i => c*v i
    have hy : dot u y = 0 := by
      have he := dot_add_smul u v (fun _ => 0) c
      rw [hv] at he
      simpa [y,dot] using he
    have hqy : dot q y = c*normSq v := by
      have he := dot_add_smul q v (fun _ => 0) c
      rw [hqv] at he
      simpa [y,dot] using he
    have hyR : normSq y = R*h/4 := by
      rw [show normSq y = c^2*normSq v from normSq_smul v c]
      dsimp [c]
      field_simp
      nlinarith
    have ht := cap_width_transverse u q y R h W hu hy hh hR hyR.le hw
    rw [hqy,abs_of_nonneg (mul_nonneg hc hV0)] at ht
    have he : 2*(c*normSq v) = Real.sqrt (R*h*normSq v) := by
      dsimp [c]
      field_simp
    rw [he] at ht
    have ht2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
    rw [hsqrt] at ht2
    nlinarith
  rw [hnorm]
  nlinarith

end LinearDistancePreservers.LatticeCaps
