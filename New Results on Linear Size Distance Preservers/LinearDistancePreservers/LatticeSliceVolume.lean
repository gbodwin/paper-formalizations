import LinearDistancePreservers.LatticeCapVolume
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set

/-- An annulus estimate in terms of the difference of squared radii.
Unlike a bound on the difference of radii, this does not divide by the
inner radius, and remains valid when the inner ball disappears. -/
theorem annulus_square_power_bound (n : ℕ) (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    a^(n+2)-b^(n+2) ≤ (n+2 : ℕ)*(a^2-b^2)*a^n := by
  have ha : 0 ≤ a := hb.trans hba
  have hh := annulus_power_bound a (a-b) (sub_nonneg.mpr hba) (by linarith) (n+1)
  have hm := mul_le_mul_of_nonneg_left
    (show a*(a-b) ≤ a^2-b^2 by nlinarith) (pow_nonneg ha n)
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ (n+2 : ℕ))
  have hn : n+1+1 = n+2 := by omega
  rw [sub_sub_cancel,hn] at hh
  simp only [pow_succ] at hh ⊢
  push_cast at hh hmul ⊢
  nlinarith

/-- Exact volume bound for the transverse Euclidean annulus, including a
zero inner radius. The dimension n+2 is precisely the d≥3 restriction. -/
theorem transverse_annulus_volume (n : ℕ) (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) a \ closedBall 0 b) ≤
      (n+2 : ℕ)*(a^2-b^2)*a^n*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1) := by
  have ha : 0 ≤ a := hb.trans hba
  rw [measureReal_sdiff (closedBall_subset_closedBall hba) measurableSet_closedBall
    measure_closedBall_lt_top.ne]
  rw [Measure.addHaar_real_closedBall' volume _ ha,
    Measure.addHaar_real_closedBall' volume _ hb]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  have hh := mul_le_mul_of_nonneg_right (annulus_square_power_bound n a b hb hba)
    (measureReal_nonneg (μ := volume) (s := closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1))
  nlinarith

/-- A bounded axial interval and a uniform transverse-section bound give
a genuine product-volume bound by Tonelli. No measurability of an arbitrary
union of caps is needed once it is covered by a measurable cell. -/
theorem volume_le_interval_mul_section {E : Type*}
    [MeasureSpace E] [SFinite (volume : Measure E)]
    (S : Set (ℝ × E)) (hS : MeasurableSet S) (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hslab : ∀ x ∈ S, x.1 ∈ Icc a b)
    (hsection : ∀ t ∈ Icc a b,
      volume (Prod.mk t ⁻¹' S) ≤ ENNReal.ofReal C) :
    volume.real S ≤ (b-a)*C := by
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sub_nonneg.mpr hab) hC)
  rw [Measure.volume_eq_prod,Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ t : ℝ, (Icc a b).indicator (fun _ => ENNReal.ofReal C) t := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ Icc a b
      · rw [Set.indicator_of_mem ht]
        exact hsection t ht
      · rw [Set.indicator_of_notMem ht]
        have he : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact ht (hslab (t,x) hx)
        change volume (Prod.mk t ⁻¹' S) ≤ 0
        rw [he,measure_empty]
    _ = ENNReal.ofReal C*volume (Icc a b) := lintegral_indicator_const measurableSet_Icc _
    _ = _ := by rw [Real.volume_Icc,← ENNReal.ofReal_mul hC]; congr 1; ring

/-- The same transverse estimate with both spherical boundaries retained.
The inner sphere has zero volume in positive dimension. -/
theorem transverse_squared_annulus_volume (n : ℕ) (A B : ℝ)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    volume.real {y : EuclideanSpace ℝ (Fin (n+2)) | B ≤ ‖y‖^2 ∧ ‖y‖^2 ≤ A} ≤
      (n+2 : ℕ)*(A-B)*(Real.sqrt A)^n*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1) := by
  have hA : 0 ≤ A := hB.trans hBA
  have hrad : Real.sqrt B ≤ Real.sqrt A := Real.sqrt_le_sqrt hBA
  have he : {y : EuclideanSpace ℝ (Fin (n+2)) | B ≤ ‖y‖^2 ∧ ‖y‖^2 ≤ A} =
      closedBall 0 (Real.sqrt A) \ ball 0 (Real.sqrt B) := by
    ext y
    simp only [Set.mem_setOf_eq,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,
      dist_zero_right,not_lt]
    constructor
    · rintro ⟨hb,ha⟩
      constructor <;> nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB,
        Real.sqrt_nonneg A,Real.sqrt_nonneg B,norm_nonneg y]
    · rintro ⟨ha,hb⟩
      constructor <;> nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB,
        Real.sqrt_nonneg A,Real.sqrt_nonneg B,norm_nonneg y]
  rw [he,measureReal_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall hrad))
    measurableSet_ball measure_closedBall_lt_top.ne]
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume 0 (Real.sqrt B)]
  rw [Measure.addHaar_real_closedBall' volume _ (Real.sqrt_nonneg A),
    Measure.addHaar_real_closedBall' volume _ (Real.sqrt_nonneg B)]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  have hh := annulus_square_power_bound n (Real.sqrt A) (Real.sqrt B)
    (Real.sqrt_nonneg B) hrad
  rw [Real.sq_sqrt hA,Real.sq_sqrt hB] at hh
  have hm := mul_le_mul_of_nonneg_right hh
    (measureReal_nonneg (μ := volume) (s := closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1))
  nlinarith

/-- A spherical shell intersected with an axial slab, in product
coordinates. Both boundaries are retained for an upper-volume cover. -/
def productShellCell (n : ℕ) (R H a b : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin (n+2))) :=
  {z | z.1 ∈ Icc a b ∧ ‖z.2‖^2+z.1^2 ≤ R^2 ∧
    (R-H)^2 ≤ ‖z.2‖^2+z.1^2}

theorem measurableSet_productShellCell (n : ℕ) (R H a b : ℝ) :
    MeasurableSet (productShellCell n R H a b) := by
  have hc : Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin (n+2)) => ‖z.2‖^2+z.1^2) := by
    fun_prop
  exact (measurable_fst measurableSet_Icc).inter
    ((isClosed_le hc continuous_const).measurableSet.inter
      (isClosed_le continuous_const hc).measurableSet)

/-- Tonelli plus the squared-radius annulus estimate bounds an entire
shell/slab cell, without a surface-area formula or any cap/facet counting. -/
theorem productShellCell_volume_le (n : ℕ) (R H a b L : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hHR : H ≤ R) (hab : a ≤ b) (hL : 0 ≤ L)
    (hslice : ∀ t ∈ Icc a b, t^2 ≤ R^2 → R^2-t^2 ≤ L) :
    volume.real (productShellCell n R H a b) ≤
      (b-a)*((n+2 : ℕ)*(2*R*H)*(Real.sqrt L)^n*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) := by
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  apply volume_le_interval_mul_section _ (measurableSet_productShellCell n R H a b)
    a b _ hab (by positivity)
  · intro z hz; exact hz.1
  intro t ht
  by_cases htR : t^2 ≤ R^2
  · let A := R^2-t^2
    let B := max ((R-H)^2-t^2) 0
    have hA : 0 ≤ A := sub_nonneg.mpr htR
    have hB : 0 ≤ B := le_max_right _ _
    have hBA : B ≤ A := max_le (by dsimp [A]; nlinarith) hA
    have hAB : A-B ≤ 2*R*H := by
      have hb := le_max_left ((R-H)^2-t^2) 0
      change (R-H)^2-t^2 ≤ B at hb
      dsimp [A]
      nlinarith
    have hAL : A ≤ L := hslice t ht htR
    let T := {y : EuclideanSpace ℝ (Fin (n+2)) | B ≤ ‖y‖^2 ∧ ‖y‖^2 ≤ A}
    have hsub : Prod.mk t ⁻¹' productShellCell n R H a b ⊆ T := by
      intro y hy
      refine ⟨max_le ?_ (sq_nonneg _),?_⟩
      · have hh := hy.2.2; linarith
      · have hh := hy.2.1; linarith
    have hTb : T ⊆ closedBall 0 (Real.sqrt A) := by
      intro y hy
      simp only [mem_closedBall,dist_zero_right]
      have hh := hy.2
      nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A,norm_nonneg y]
    have hTfinite : volume T ≠ ⊤ := measure_ne_top_of_subset hTb measure_closedBall_lt_top.ne
    have hfinite : volume (Prod.mk t ⁻¹' productShellCell n R H a b) ≠ ⊤ :=
      measure_ne_top_of_subset hsub hTfinite
    have hv := (measureReal_mono hsub hTfinite).trans (transverse_squared_annulus_volume n A B hB hBA)
    have hb : volume.real (Prod.mk t ⁻¹' productShellCell n R H a b) ≤
        (n+2 : ℕ)*(2*R*H)*(Real.sqrt L)^n*V := by
      apply hv.trans
      dsimp [V]
      gcongr
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hb
  · have he : Prod.mk t ⁻¹' productShellCell n R H a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh := hy.2.1
      exact htR (by nlinarith [sq_nonneg ‖y‖])
    rw [he,measure_empty]
    positivity

/-- Specialization to the actual normal/depth scales. It is uniform in
all k≥1, including the nearly parallel-normal cell. -/
theorem productShellCell_normal_scale (n : ℕ) (R C W p k : ℝ)
    (hC : 0 ≤ C) (hCR : C ≤ R) (hW : 0 ≤ W) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    volume.real (productShellCell n R (C/(k*p))
      (R-(k+W+1)/p) (R-(k-W-1)/p)) ≤
      (2*(W+1)/p)*((n+2 : ℕ)*(2*R*(C/(k*p)))*
        (Real.sqrt (2*R*(W+2)*k/p))^n*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) := by
  have hR : 0 ≤ R := hC.trans hCR
  have hp0 : 0 < p := by linarith
  have hk0 : 0 < k := by linarith
  have hkp : 1 ≤ k*p := by nlinarith
  have hH : 0 ≤ C/(k*p) := by positivity
  have hHR : C/(k*p) ≤ R := (div_le_self hC hkp).trans hCR
  have hab : R-(k+W+1)/p ≤ R-(k-W-1)/p := by
    apply sub_le_sub_left
    apply (div_le_div_iff_of_pos_right hp0).mpr
    linarith
  have hL : 0 ≤ 2*R*(W+2)*k/p := by positivity
  have hs : ∀ t ∈ Icc (R-(k+W+1)/p) (R-(k-W-1)/p),
      t^2 ≤ R^2 → R^2-t^2 ≤ 2*R*(W+2)*k/p := by
    intro t ht htR
    have htlo : -R ≤ t := by nlinarith
    have hthi : t ≤ R := by nlinarith
    have htp : (R-t)*p ≤ k+W+1 := (le_div_iff₀ hp0).mp (by linarith [ht.1])
    apply (le_div_iff₀ hp0).mpr
    calc
      (R^2-t^2)*p = ((R-t)*p)*(R+t) := by ring
      _ ≤ (k+W+1)*(R+t) := mul_le_mul_of_nonneg_right htp (by linarith)
      _ ≤ (k+W+1)*(2*R) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ((W+2)*k)*(2*R) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = _ := by ring
  have hh := productShellCell_volume_le n R (C/(k*p)) _ _ _ hR hH hHR hab hL hs
  have he : (R-(k-W-1)/p)-(R-(k+W+1)/p) = 2*(W+1)/p := by ring
  rwa [he] at hh

end LinearDistancePreservers.LatticeCaps
