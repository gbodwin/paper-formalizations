import LinearDistancePreservers.LatticeCapVolume
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Algebra.Order.Floor.Ring

namespace LinearDistancePreservers.PolytopeApproximation
open Set Metric MeasureTheory
open scoped RealInnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A closed radial cone around a point in the unit ball. No normalization
or nonzero assumption on the generating point is required. -/
def shadow (u : E) (m : ℕ) : Set E :=
  {x | (1 - 1 / (2 * (m : ℝ)^2)) * ‖x‖ ≤ inner ℝ x u}

def unitShadow (u : E) (m : ℕ) : Set E := closedBall 0 1 ∩ shadow u m

theorem isClosed_shadow (u : E) (m : ℕ) : IsClosed (shadow u m) :=
  isClosed_le (continuous_const.mul continuous_norm) (continuous_id.inner continuous_const)

theorem mem_shadow_smul_iff (u x : E) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    t • x ∈ shadow u m ↔ x ∈ shadow u m := by
  simp only [shadow,Set.mem_ofPred_eq,norm_smul,Real.norm_eq_abs,
    abs_of_pos ht,real_inner_smul_left]
  constructor <;> intro h <;> nlinarith

/-- A point in the cone is uniformly close to its projection onto the
possibly shorter generating ray. -/
theorem dist_ray_le {u x : E} {m : ℕ} (hm : 0 < m) (hu : ‖u‖ ≤ 1)
    (hx : x ∈ unitShadow u m) : dist x (‖x‖ • u) ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxN : ‖x‖ ≤ 1 := by simpa using hx.1
  have hxS := hx.2
  change (1 - 1 / (2 * (m : ℝ)^2)) * ‖x‖ ≤ inner ℝ x u at hxS
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hx2 : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdot := mul_le_mul_of_nonneg_left hxS (norm_nonneg x)
  have hnorm : ‖x - ‖x‖ • u‖^2 = ‖x‖^2 + ‖x‖^2 * ‖u‖^2 -
      2 * ‖x‖ * inner ℝ x u := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),
      real_inner_smul_right,mul_pow]
    ring
  have huMul := mul_le_mul_of_nonneg_left hu2 (sq_nonneg ‖x‖)
  have hden : 0 < 2 * (m : ℝ)^2 := by positivity
  have hinv : 0 < 1 / (m : ℝ) := by positivity
  have hid : 2 * (1 / (2 * (m : ℝ)^2)) = (1 / (m : ℝ))^2 := by field_simp
  rw [dist_eq_norm]
  nlinarith [sq_nonneg (‖x - ‖x‖ • u‖ - 1 / (m : ℝ)), norm_nonneg (x - ‖x‖ • u),
    mul_le_mul_of_nonneg_left hx2 (le_of_lt (show 0 < 1 / (2 * (m : ℝ)^2) by positivity))]

/-- A cone in the unit ball is covered by m+1 balls along its generating
ray. This avoids surface measure and rotation-coordinate machinery. -/
theorem unitShadow_subset_balls {u : E} {m : ℕ} (hm : 0 < m) (hu : ‖u‖ ≤ 1) :
    unitShadow u m ⊆ ⋃ k ∈ Finset.range (m+1),
      closedBall (((k : ℝ) / m) • u) (2 / m) := by
  intro x hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxN : ‖x‖ ≤ 1 := by simpa using hx.1
  let k := ⌊(m : ℝ) * ‖x‖⌋₊
  have hk : k ≤ m := Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_left hxN hmR.le)
  have hklo : (k : ℝ) ≤ (m : ℝ) * ‖x‖ := Nat.floor_le (by positivity)
  have hkhi : (m : ℝ) * ‖x‖ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have ht0 : 0 ≤ ‖x‖ - (k : ℝ) / m := by apply sub_nonneg.mpr; exact (div_le_iff₀ hmR).mpr (by simpa [mul_comm] using hklo)
  have ht1 : ‖x‖ - (k : ℝ) / m ≤ 1 / m := by
    apply (le_div_iff₀ hmR).mpr
    have he : (‖x‖ - (k : ℝ) / m) * m = (m : ℝ) * ‖x‖ - k := by field_simp
    rw [he]; linarith
  have hdist : dist (‖x‖ • u) (((k : ℝ) / m) • u) ≤ 1 / m := by
    rw [dist_eq_norm,← sub_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hu ht0).trans (by simpa using ht1)
  have htri := (dist_triangle x (‖x‖ • u) (((k : ℝ) / m) • u)).trans
    (add_le_add (dist_ray_le hm hu hx) hdist)
  apply Set.mem_iUnion.mpr
  refine ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
  simpa only [mem_closedBall,div_eq_mul_inv,← two_mul,one_mul] using htri

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Explicit finite-ball covering estimate with the correct angular
exponent dim(E)-1. -/
theorem unitShadow_volume_le {u : E} {m : ℕ} (hm : 0 < m) (hu : ‖u‖ ≤ 1) :
    volume.real (unitShadow u m) ≤
      (m+1 : ℕ) * (2 / (m : ℝ))^(Module.finrank ℝ E) *
        volume.real (closedBall (0 : E) 1) := by
  let f : ℕ → Set E := fun k => closedBall (((k : ℝ) / m) • u) (2 / m)
  have hf : volume (⋃ k ∈ Finset.range (m+1), f k) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr (fun _ _ => measure_closedBall_lt_top))
  have hmono := measureReal_mono (unitShadow_subset_balls hm hu) hf
  have hs := measureReal_biUnion_finset_le (μ := volume) (Finset.range (m+1)) f
  have he (k : ℕ) : volume.real (f k) = (2 / (m : ℝ))^(Module.finrank ℝ E) *
      volume.real (closedBall (0 : E) 1) :=
    Measure.addHaar_real_closedBall' volume _ (by positivity)
  simp_rw [he] at hs
  simpa [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using hmono.trans hs

/-- The directions already accounted for by a finite vertex set. -/
def shadows (V : Finset E) (m : ℕ) : Set E := ⋃ u ∈ V, shadow u m

def uncovered (V : Finset E) (m : ℕ) : Set E := closedBall 0 1 \ shadows V m

theorem isClosed_shadows (V : Finset E) (m : ℕ) : IsClosed (shadows V m) :=
  isClosed_biUnion_finset (fun u _ => isClosed_shadow u m)

theorem measurableSet_uncovered (V : Finset E) (m : ℕ) :
    MeasurableSet (uncovered V m) :=
  measurableSet_closedBall.diff (isClosed_shadows V m).measurableSet

theorem mem_shadows_smul_iff (V : Finset E) (m : ℕ) (x : E) {t : ℝ} (ht : 0 < t) :
    t • x ∈ shadows V m ↔ x ∈ shadows V m := by
  simp only [shadows,mem_iUnion,mem_shadow_smul_iff _ _ _ ht]

/-- Outside all vertex cones, the convex hull has strictly smaller radius. -/
theorem norm_lt_of_mem_hull_not_shadows {V : Finset E} {m : ℕ} {x : E}
    (hx : x ∈ convexHull ℝ (V : Set E)) (hout : x ∉ shadows V m) :
    ‖x‖ < 1 - 1 / (2 * (m : ℝ)^2) := by
  let f := (InnerProductSpace.toDual ℝ E x).toLinearMap
  obtain ⟨u,hu,hxu⟩ := f.convexOn (s := Set.univ) convex_univ |>.exists_ge_of_mem_convexHull
    (Set.subset_univ _) hx
  have hnot : x ∉ shadow u m := by
    intro hm
    exact hout (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hm⟩⟩)
  have hlt : inner ℝ x u < (1 - 1 / (2 * (m : ℝ)^2)) * ‖x‖ := lt_of_not_ge hnot
  have hxinner : ‖x‖^2 ≤ inner ℝ x u := by
    change inner ℝ x x ≤ inner ℝ x u at hxu
    simpa only [real_inner_self_eq_norm_sq] using hxu
  nlinarith [norm_nonneg x]

/-- Exact radial homothety of the region outside the vertex cones. -/
theorem smul_uncovered {V : Finset E} {m : ℕ} {t : ℝ} (ht : 0 < t) :
    t • uncovered V m = closedBall 0 t \ shadows V m := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨?_,fun h => hy.2 ((mem_shadows_smul_iff V m y ht).mp h)⟩
    have hn : ‖y‖ ≤ 1 := by simpa using hy.1
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith
  · intro hx
    refine ⟨t⁻¹ • x,?_,smul_inv_smul₀ ht.ne' x⟩
    refine ⟨?_,fun h => hx.2 ((mem_shadows_smul_iff V m x (inv_pos.mpr ht)).mp h)⟩
    have hn : ‖x‖ ≤ t := by simpa using hx.1
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_iff₀ ht).mpr (by simpa using hn)

/-- Uncovered outer directions are genuinely missing from the convex hull. -/
theorem uncovered_shell_subset_missed {V : Finset E} {m : ℕ} {t : ℝ}
    (ht : 0 < t) (hdepth : 1 - 1 / (2 * (m : ℝ)^2) ≤ t) :
    uncovered V m \ t • uncovered V m ⊆
      closedBall 0 1 \ convexHull ℝ (V : Set E) := by
  intro x hx
  refine ⟨hx.1.1,?_⟩
  intro hP
  have hnorm := (norm_lt_of_mem_hull_not_shadows hP hx.1.2).trans_le hdepth
  apply hx.2
  rw [smul_uncovered ht]
  exact ⟨by simpa using hnorm.le,hx.1.2⟩

theorem real_volume_smul (S : Set E) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (t • S) = t^(Module.finrank ℝ E) * volume.real S := by
  rw [measureReal_def,Measure.addHaar_smul_of_nonneg volume ht,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ht _)]
  rfl

/-- A lower bound from any unaccounted-for radial directions. -/
theorem missed_volume_ge_uncovered {V : Finset E} {m : ℕ} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hdepth : 1 - 1 / (2 * (m : ℝ)^2) ≤ t) :
    (1 - t^(Module.finrank ℝ E)) * volume.real (uncovered V m) ≤
      volume.real (closedBall 0 1 \ convexHull ℝ (V : Set E)) := by
  have hfinite : volume (uncovered V m) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset measure_closedBall_lt_top.ne
  have hsub : t • uncovered V m ⊆ uncovered V m := by
    rw [smul_uncovered ht]
    exact Set.sdiff_subset_sdiff_left (closedBall_subset_closedBall ht1)
  have hmeas : MeasurableSet (t • uncovered V m) := by
    rw [smul_uncovered ht]
    exact measurableSet_closedBall.diff (isClosed_shadows V m).measurableSet
  have hmono := measureReal_mono (uncovered_shell_subset_missed (V := V) ht hdepth)
    (measure_ne_top_of_subset Set.sdiff_subset (measure_closedBall_lt_top (μ := volume) (x := (0 : E)) (r := 1)).ne)
  rw [measureReal_sdiff hsub hmeas hfinite,real_volume_smul _ ht.le] at hmono
  nlinarith

/-- Finite subadditivity converts the cone cover into an explicit bound
on all covered directions. -/
theorem covered_volume_le {V : Finset E} {m : ℕ} (hm : 0 < m)
    (hV : ∀ u ∈ V, ‖u‖ ≤ 1) :
    volume.real (closedBall 0 1 ∩ shadows V m) ≤
      V.card * ((m+1 : ℕ) * (2 / (m : ℝ))^(Module.finrank ℝ E)) *
        volume.real (closedBall (0 : E) 1) := by
  have he : closedBall (0 : E) 1 ∩ shadows V m = ⋃ u ∈ V, unitShadow u m := by
    simp only [shadows,unitShadow,Set.inter_iUnion]
  rw [he]
  have hs := measureReal_biUnion_finset_le (μ := volume) V (fun u => unitShadow u m)
  have hb := Finset.sum_le_sum (fun u hu => unitShadow_volume_le hm (hV u hu))
  exact (hs.trans hb).trans_eq (by simp [Finset.sum_const,nsmul_eq_mul,mul_assoc])

/-- If the angular cones occupy at most half the unit ball, at least half
of its volume is left in directions outside every vertex cone. -/
theorem uncovered_volume_ge {V : Finset E} {m : ℕ} (hm : 0 < m)
    (hV : ∀ u ∈ V, ‖u‖ ≤ 1)
    (hcard : (V.card : ℝ) * ((m+1 : ℕ) * (2 / (m : ℝ))^(Module.finrank ℝ E)) ≤ 1/2) :
    volume.real (closedBall (0 : E) 1) / 2 ≤ volume.real (uncovered V m) := by
  have hcov := covered_volume_le hm hV
  have hcov' := mul_le_mul_of_nonneg_right hcard
    (measureReal_nonneg (μ := volume) (s := closedBall (0 : E) 1))
  have he : uncovered V m = closedBall 0 1 \ (closedBall 0 1 ∩ shadows V m) := by
    ext x; simp [uncovered]
  rw [he,measureReal_sdiff Set.inter_subset_left
    (measurableSet_closedBall.inter (isClosed_shadows V m).measurableSet)
    measure_closedBall_lt_top.ne]
  linarith

/-- An unconditional polytope approximation estimate. The count condition
is explicit and the conclusion concerns the actual missed Euclidean volume. -/
theorem missed_volume_lower {V : Finset E} {m : ℕ} (hm : 0 < m)
    (hd : 0 < Module.finrank ℝ E) (hV : ∀ u ∈ V, ‖u‖ ≤ 1)
    (hcard : (V.card : ℝ) * ((m+1 : ℕ) * (2 / (m : ℝ))^(Module.finrank ℝ E)) ≤ 1/2) :
    volume.real (closedBall (0 : E) 1) / (4 * (m : ℝ)^2) ≤
      volume.real (closedBall 0 1 \ convexHull ℝ (V : Set E)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let t : ℝ := 1 - 1 / (2 * (m : ℝ)^2)
  have hinv : 0 < 1 / (2 * (m : ℝ)^2) := by positivity
  have hinv1 : 1 / (2 * (m : ℝ)^2) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (m : ℝ)^2)).mpr
    nlinarith
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hp : t^(Module.finrank ℝ E) ≤ t :=
    (pow_le_pow_of_le_one ht.le ht1 hd).trans_eq (pow_one t)
  have hU := uncovered_volume_ge hm hV hcard
  have hmiss := missed_volume_ge_uncovered (V := V) ht ht1 (le_refl t)
  have hV0 := measureReal_nonneg (μ := volume) (s := closedBall (0 : E) 1)
  have hU0 := measureReal_nonneg (μ := volume) (s := uncovered V m)
  have hprod := mul_le_mul_of_nonneg_left hU hinv.le
  have he : (1 / (2 * (m : ℝ)^2)) * (volume.real (closedBall (0 : E) 1) / 2) =
      volume.real (closedBall (0 : E) 1) / (4 * (m : ℝ)^2) := by ring
  rw [he] at hprod
  dsimp [t] at hp hmiss
  nlinarith

/-- Integer-grid form of the approximation inequality. Its count scale is
m^(d-1) and its radial loss is m^(-2), giving the sharp approximation exponent. -/
theorem missed_volume_lower_grid {V : Finset E} {m n : ℕ} (hm : 0 < m)
    (hd : Module.finrank ℝ E = n+1) (hV : ∀ u ∈ V, ‖u‖ ≤ 1)
    (hcard : 2^(n+3) * V.card ≤ m^n) :
    volume.real (closedBall (0 : E) 1) / (4 * (m : ℝ)^2) ≤
      volume.real (closedBall 0 1 \ convexHull ℝ (V : Set E)) := by
  apply missed_volume_lower hm (by omega) hV
  rw [hd]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by positivity
  have hcast : (2 : ℝ)^(n+3) * V.card ≤ (m : ℝ)^n := by exact_mod_cast hcard
  have he : (V.card : ℝ) * (((m+1 : ℕ) : ℝ) * (2 / (m : ℝ))^(n+1)) =
      ((V.card : ℝ) * ((m : ℝ)+1) * 2^(n+1)) / (m : ℝ)^(n+1) := by
    push_cast
    rw [div_pow]
    ring
  rw [he]
  apply (div_le_iff₀ (pow_pos hmpos _)).mpr
  have hsmall : (m : ℝ)+1 ≤ 2*m := by linarith
  have hb := mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (Nat.cast_nonneg V.card) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n+1)))
  have hc := mul_le_mul_of_nonneg_right hcast hmpos.le
  rw [show n+3 = (n+1)+2 by omega,pow_add] at hc
  rw [pow_succ (m : ℝ) n]
  norm_num at hc
  nlinarith

/-- The same sharp-order estimate at an arbitrary positive radius. -/
theorem missed_volume_lower_grid_scaled {V : Finset E} {m n : ℕ} {R : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hd : Module.finrank ℝ E = n+1)
    (hV : ∀ u ∈ V, ‖u‖ ≤ R) (hcard : 2^(n+3) * V.card ≤ m^n) :
    R^(n+1) * volume.real (closedBall (0 : E) 1) / (4 * (m : ℝ)^2) ≤
      volume.real (closedBall 0 R \ convexHull ℝ (V : Set E)) := by
  classical
  let V₁ := V.image (fun u => R⁻¹ • u)
  have hV₁ : ∀ u ∈ V₁, ‖u‖ ≤ 1 := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hV v hv)
  have hcard₁ : 2^(n+3) * V₁.card ≤ m^n :=
    (Nat.mul_le_mul_left _ (Finset.card_image_le)).trans hcard
  have hb := missed_volume_lower_grid hm hd hV₁ hcard₁
  have hset : (V₁ : Set E) = R⁻¹ • (V : Set E) := by
    simp only [V₁,Finset.coe_image]; rfl
  have hrestore : R • (V₁ : Set E) = (V : Set E) := by
    rw [hset,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  have hmiss : R • (closedBall 0 1 \ convexHull ℝ (V₁ : Set E)) =
      closedBall 0 R \ convexHull ℝ (V : Set E) := by
    rw [smul_set_sdiff₀ hR.ne',← convexHull_smul,hrestore,
      _root_.smul_closedBall R (0 : E) (by norm_num : (0 : ℝ) ≤ 1)]
    simp [Real.norm_eq_abs,abs_of_pos hR]
  calc
    _ = R^(Module.finrank ℝ E) * (volume.real (closedBall (0 : E) 1) / (4 * (m : ℝ)^2)) := by
      rw [hd]; ring
    _ ≤ R^(Module.finrank ℝ E) * volume.real (closedBall 0 1 \ convexHull ℝ (V₁ : Set E)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hR.le _)
    _ = _ := by rw [← real_volume_smul _ hR.le,hmiss]

end LinearDistancePreservers.PolytopeApproximation
