import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-! The exponent iterations in Theorems 38 and 43 of arXiv:2410.20471v1. -/

namespace OnlineReachabilityPreservers

open Filter Set
open scoped Topology

private theorem iterate_to_fixed_point (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (step : ∀ x ∈ Ico a b, x < f x ∧ f x < b)
    (continuous : ContinuousOn f (Icc a b)) (fixed : ∀ x ∈ Icc a b, f x = x → x = b) :
    StrictMono (fun k => f^[k] a) ∧
      (∀ k, f^[k] a ∈ Ico a b) ∧ Tendsto (fun k => f^[k] a) atTop (𝓝 b) := by
  let v (k : ℕ) := f^[k] a
  have hv (k : ℕ) : v (k + 1) = f (v k) := Function.iterate_succ_apply' _ _ _
  have hmem (k : ℕ) : v k ∈ Ico a b := by
    induction k with
    | zero => exact ⟨le_rfl, hab⟩
    | succ k ih =>
      rw [hv]
      obtain ⟨h1, h2⟩ := step (v k) ih
      exact ⟨ih.1.trans h1.le, h2⟩
  have hmono : StrictMono v := strictMono_nat_of_lt_succ fun k =>
    (step (v k) (hmem k)).1.trans_le (hv k).ge
  have hbdd : BddAbove (range v) := ⟨b, by
    rintro _ ⟨k, rfl⟩
    exact (hmem k).2.le⟩
  let s := ⨆ k, v k
  have hs : s ∈ Icc a b := ⟨le_ciSup hbdd 0, ciSup_le fun k => (hmem k).2.le⟩
  have hlim : Tendsto v atTop (𝓝 s) := tendsto_atTop_ciSup hmono.monotone hbdd
  have hwithin : Tendsto v atTop (𝓝[Icc a b] s) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall fun k => ⟨(hmem k).1, (hmem k).2.le⟩⟩
  have hstep : Tendsto (fun k => v (k + 1)) atTop (𝓝 (f s)) := by
    simp only [hv]
    exact (continuous s hs).tendsto.comp hwithin
  have hshift : Tendsto (fun k => v (k + 1)) atTop (𝓝 s) :=
    (tendsto_add_atTop_iff_nat 1).mpr hlim
  have heq : s = b := fixed s hs (tendsto_nhds_unique hstep hshift)
  exact ⟨hmono, hmem, heq ▸ hlim⟩

/-- The cubic obtained from the corrected recurrence in Appendix A. -/
noncomputable def onlineCubic (x : ℝ) : ℝ :=
  4*x^3 - 13*x^2 + 10*x - 2

/-- The update from Lemma 37 used in Theorem 38. -/
noncomputable def onlineExponentStep (x : ℝ) : ℝ :=
  (7*x - 2*x^2 - 2) / (11*x - 4*x^2 - 3)

private theorem interval_mul_le {x y : ℝ} (hx : x ∈ Icc (2/3 : ℝ) (3/4))
    (hy : y ∈ Icc (2/3 : ℝ) (3/4)) : x*y ≤ (3/4 : ℝ)^2 := by
  rw [pow_two]
  exact mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (by norm_num)

private theorem onlineCubic_decreasing : StrictAntiOn onlineCubic (Icc (2/3 : ℝ) (3/4)) := by
  intro x hx y hy hxy
  apply sub_neg.mp
  have h : 4 * (y^2 + x*y + x^2) - 13 * (x + y) + 10 < 0 := by
    nlinarith only [interval_mul_le hx hx, interval_mul_le hx hy, interval_mul_le hy hy, hx.1, hy.1]
  calc
    onlineCubic y - onlineCubic x = (y-x) * (4*(y^2+x*y+x^2)-13*(x+y)+10) := by
      unfold onlineCubic
      ring
    _ < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) h

private theorem onlineExponent_denom_pos {x : ℝ} (hx : x ∈ Icc (2/3 : ℝ) (3/4)) :
    0 < 11*x - 4*x^2 - 3 := by
  nlinarith only [hx.1, interval_mul_le hx hx]

private theorem onlineExponentStep_increasing :
    StrictMonoOn onlineExponentStep (Icc (2/3 : ℝ) (3/4)) := by
  intro x hx y hy hxy
  unfold onlineExponentStep
  rw [div_lt_div_iff₀ (onlineExponent_denom_pos hx) (onlineExponent_denom_pos hy)]
  apply sub_pos.mp
  have he : 0 < 6*x*y - 2*(x+y) + 1 := by
    have h := mul_nonneg (show 0 ≤ x-1/3 by linarith [hx.1]) (show 0 ≤ y-1/3 by linarith [hy.1])
    nlinarith only [h]
  calc
    _ = (y-x) * (6*x*y - 2*(x+y) + 1) := by ring
    _ > 0 := mul_pos (sub_pos.mpr hxy) he

private theorem online_step_fixed_iff {x : ℝ} (hx : x ∈ Icc (2/3 : ℝ) (3/4)) :
    onlineExponentStep x = x ↔ onlineCubic x = 0 := by
  rw [onlineExponentStep, div_eq_iff (onlineExponent_denom_pos hx).ne', onlineCubic]
  constructor <;> intro h <;> linarith only [h]

private theorem online_root_interval {x : ℝ} (hx : x ∈ Icc (7/10 : ℝ) (701/1000)) :
    x ∈ Icc (2/3 : ℝ) (3/4) :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The cubic has a unique root in the interval used for the online estimate. -/
theorem theorem38_root :
    ∃! α : ℝ, α ∈ Ioo (7/10 : ℝ) (701/1000) ∧ onlineCubic α = 0 := by
  have lower : 0 < onlineCubic (7/10 : ℝ) := by norm_num [onlineCubic]
  have upper : onlineCubic (701/1000 : ℝ) < 0 := by norm_num [onlineCubic]
  have continuous : Continuous onlineCubic := by unfold onlineCubic; fun_prop
  obtain ⟨α, ha, hz⟩ := intermediate_value_Icc' (by norm_num : (7/10 : ℝ) ≤ 701/1000)
    continuous.continuousOn (show 0 ∈ Icc (onlineCubic (701/1000)) (onlineCubic (7/10)) from
      ⟨upper.le, lower.le⟩)
  have ha' : α ∈ Ioo (7/10 : ℝ) (701/1000) := by
    refine ⟨ha.1.lt_of_ne ?_, ha.2.lt_of_ne ?_⟩
    · intro eq
      exact lower.ne' (eq ▸ hz)
    · intro eq
      exact upper.ne (eq ▸ hz)
  refine ⟨α, ⟨ha', hz⟩, ?_⟩
  rintro x ⟨hx, hxz⟩
  exact onlineCubic_decreasing.injOn
    (online_root_interval ⟨hx.1.le, hx.2.le⟩) (online_root_interval ha) (hxz.trans hz.symm)

/-- The second exponent in the online pairwise bound. -/
noncomputable def onlineSecondExponent (k : ℕ) : ℝ := onlineExponentStep^[k] (2/3)

private noncomputable def firstExponentFormula (x : ℝ) : ℝ := (2+x) / (3+x)

/-- The first exponent in the online pairwise bound. -/
noncomputable def onlineFirstExponent : ℕ → ℝ
  | 0 => 8/11
  | k + 1 => firstExponentFormula (onlineSecondExponent k)

/-- The corrected arithmetic iteration stays below the limiting root and converges to it.
The limiting assertion here concerns the exponents. -/
theorem theorem38_exponent_limits {α : ℝ} (ha : α ∈ Ioo (7/10 : ℝ) (701/1000))
    (hz : onlineCubic α = 0) :
    StrictMono onlineSecondExponent ∧
      (∀ k, onlineSecondExponent k ∈ Ico (2/3 : ℝ) α) ∧
      (∀ k, onlineFirstExponent k ∈ Ico (8/11 : ℝ) (3/4)) ∧
      Tendsto onlineSecondExponent atTop (𝓝 α) ∧
      Tendsto onlineFirstExponent atTop (𝓝 ((2+α)/(3+α))) := by
  have ha' := online_root_interval ⟨ha.1.le, ha.2.le⟩
  have hstart : (2/3 : ℝ) < α := by linarith [ha.1]
  have sub : Icc (2/3 : ℝ) α ⊆ Icc (2/3 : ℝ) (3/4) :=
    fun _ hx => ⟨hx.1, hx.2.trans ha'.2⟩
  have hfix := (online_step_fixed_iff ha').mpr hz
  have grow (x : ℝ) (hx : x ∈ Ico (2/3 : ℝ) α) : x < onlineExponentStep x ∧ onlineExponentStep x < α := by
    have hwide := sub (show x ∈ Icc (2/3 : ℝ) α from ⟨hx.1, hx.2.le⟩)
    have hp := onlineCubic_decreasing hwide ha' hx.2
    rw [hz, onlineCubic] at hp
    refine ⟨?_, (onlineExponentStep_increasing hwide ha' hx.2).trans_le hfix.le⟩
    rw [onlineExponentStep, lt_div_iff₀ (onlineExponent_denom_pos hwide)]
    linarith only [hp]
  have hc : ContinuousOn onlineExponentStep (Icc (2/3 : ℝ) α) := by
    unfold onlineExponentStep
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun x hx => (onlineExponent_denom_pos (sub hx)).ne'
  obtain ⟨hmono, hmem, hlim⟩ := iterate_to_fixed_point onlineExponentStep hstart grow hc
    (fun _ hx eq => onlineCubic_decreasing.injOn (sub hx) ha'
      (((online_step_fixed_iff (sub hx)).mp eq).trans hz.symm))
  refine ⟨hmono, hmem, ?_, hlim, ?_⟩
  · intro k
    cases k with
    | zero => norm_num [onlineFirstExponent]
    | succ k =>
      have hl : (2/3 : ℝ) ≤ onlineSecondExponent k := (hmem k).1
      have hu : onlineSecondExponent k ≤ (3/4 : ℝ) := (hmem k).2.le.trans ha'.2
      have hd : 0 < 3 + onlineSecondExponent k := by linarith
      refine ⟨(le_div_iff₀ hd).mpr ?_, (div_lt_iff₀ hd).mpr ?_⟩ <;> linarith
  · have hf : ContinuousAt firstExponentFormula α := by
      unfold firstExponentFormula
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (ne_of_gt (by linarith [ha.1]))
    apply (tendsto_add_atTop_iff_nat 1).mp
    change Tendsto (firstExponentFormula ∘ onlineSecondExponent) atTop (𝓝 (firstExponentFormula α))
    exact hf.tendsto.comp hlim

/-- The Appendix B exponent update. -/
noncomputable def offlineExponentStep (x : ℝ) : ℝ := (2*x+1)/(2*x+2)

noncomputable def offlineExponent (k : ℕ) : ℝ := offlineExponentStep^[k] (2/3)

/-- The Appendix B arithmetic iteration converges from below to the claimed exponent. -/
theorem theorem43_exponent_limit :
    StrictMono offlineExponent ∧
      (∀ k, offlineExponent k ∈ Ico (2/3 : ℝ) (1 / Real.sqrt 2)) ∧
      Tendsto offlineExponent atTop (𝓝 (1 / Real.sqrt 2)) := by
  let α : ℝ := 1 / Real.sqrt 2
  have ha : 0 < α := one_div_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  have hsq : α^2 = 1/2 := by
    simp [α, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hstart : (2/3 : ℝ) < α := (sq_lt_sq₀ (by norm_num) ha.le).mp (by rw [hsq]; norm_num)
  have hd (x : ℝ) (hx : (2/3 : ℝ) ≤ x) : 0 < 2*x+2 := by linarith
  have hfix : offlineExponentStep α = α := (div_eq_iff (hd α hstart.le).ne').mpr (by
    linarith only [hsq])
  have grow (x : ℝ) (hx : x ∈ Ico (2/3 : ℝ) α) : x < offlineExponentStep x ∧ offlineExponentStep x < α := by
    have hxsq : x^2 < α^2 := (sq_lt_sq₀ (by linarith [hx.1]) ha.le).mpr hx.2
    constructor
    · rw [offlineExponentStep, lt_div_iff₀ (hd x hx.1)]
      linarith only [hxsq, hsq]
    · rw [← hfix, offlineExponentStep, offlineExponentStep,
        div_lt_div_iff₀ (hd x hx.1) (hd α hstart.le)]
      linarith only [hx.2]
  have hc : ContinuousOn offlineExponentStep (Icc (2/3 : ℝ) α) := by
    unfold offlineExponentStep
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun x hx => (hd x hx.1).ne'
  exact iterate_to_fixed_point offlineExponentStep hstart grow hc (fun x hx eq => by
    have hw := (div_eq_iff (hd x hx.1).ne').mp eq
    have hs : x^2 = α^2 := by linarith only [hw, hsq]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).resolve_right (by linarith [hx.1]))

end OnlineReachabilityPreservers
