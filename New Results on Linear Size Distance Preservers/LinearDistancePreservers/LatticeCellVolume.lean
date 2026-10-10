import LinearDistancePreservers.LatticeCapGrouping
import LinearDistancePreservers.LatticeSliceVolume
import LinearDistancePreservers.LatticeSlicing

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set
open scoped RealInnerProductSpace

theorem productShellCell_subset_closedBall (n : ℕ) (R H a b : ℝ) (hR : 0 ≤ R) :
    productShellCell n R H a b ⊆ closedBall 0 R := by
  intro z hz
  simp only [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs]
  have hh := hz.2.1
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg ‖z.2‖]
  · nlinarith [sq_nonneg z.1,norm_nonneg z.2]

/-- The actual integer-normal shell cell has the product-coordinate volume
bound. The coordinate rotation is proved volume-preserving, and this estimate
concerns the actual Euclidean set used in the missed-region covering. -/
theorem depthCell_volume_le (n : ℕ) (R C W : ℝ) (q : Fin (n+3) → ℤ) (k : ℕ)
    (hC : 0 ≤ C) (hCR : C ≤ R) (hW : 0 ≤ W) (hq : q ≠ 0) (hk : 1 ≤ k) :
    volume.real (depthCell (n+3) R W C q k) ≤
      (2*(W+1)/LatticeShells.radius q)*
        ((n+2 : ℕ)*(2*R*(C/((k : ℝ)*LatticeShells.radius q)))*
        (Real.sqrt (2*R*(W+2)*k/LatticeShells.radius q))^n*
        volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) := by
  let p := LatticeShells.radius q
  let qE := LatticeBody.vector q
  have hp : 1 ≤ p := one_le_integer_radius q hq
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hR : 0 ≤ R := hC.trans hCR
  have hnq : ‖qE‖ = p := by
    have he := EuclideanSpace.real_norm_sq_eq qE
    have he' : p^2 = ∑ i, (q i : ℝ)^2 := Real.sq_sqrt (by positivity)
    change ‖qE‖^2 = ∑ i, (q i : ℝ)^2 at he
    nlinarith [norm_nonneg qE]
  let u := p⁻¹ • qE
  have hu : ‖u‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp0),hnq,inv_mul_cancel₀ hp0.ne']
  obtain ⟨e,he,hex⟩ := exists_axial_slicing n u hu
  let H := C/((k : ℝ)*p)
  let a := R-((k : ℝ)+W+1)/p
  let b := R-((k : ℝ)-W-1)/p
  have hHR : H ≤ R := (div_le_self hC (by nlinarith : 1 ≤ (k : ℝ)*p)).trans hCR
  have hsub : depthCell (n+3) R W C q k ⊆ e ⁻¹' productShellCell n R H a b := by
    intro x hx
    have hdot : dot (LatticeHull.realVector q) (fun i => x i) = p*(e x).1 := by
      rw [(hex x).1]
      have heq : dot (LatticeHull.realVector q) (fun i => x i) = inner ℝ qE x :=
        LatticeBody.dot_eq_inner qE x
      rw [heq]
      change inner ℝ qE x = p*inner ℝ (p⁻¹ • qE) x
      rw [real_inner_smul_left,← mul_assoc,mul_inv_cancel₀ hp0.ne',one_mul]
    have hb := abs_le.mp hx.2.2
    rw [hdot] at hb
    have hlo : R-(e x).1 ≤ ((k : ℝ)+W+1)/p :=
      (le_div_iff₀ hp0).mpr (by nlinarith [hb.1])
    have hup : ((k : ℝ)-W-1)/p ≤ R-(e x).1 :=
      (div_le_iff₀ hp0).mpr (by nlinarith [hb.2])
    have hsq := (hex x).2
    have hxR := hx.1
    have hxH : R-H < ‖x‖ := hx.2.1
    refine ⟨⟨by change a ≤ (e x).1; dsimp [a]; linarith,
      by change (e x).1 ≤ b; dsimp [b]; linarith⟩,?_,?_⟩
    · nlinarith [norm_nonneg x]
    · nlinarith [norm_nonneg x]
  have hmeas := measurableSet_productShellCell n R H a b
  have hfinite : volume (productShellCell n R H a b) ≠ ⊤ :=
    measure_ne_top_of_subset (productShellCell_subset_closedBall n R H a b hR)
      measure_closedBall_lt_top.ne
  have hmeasure : volume (e ⁻¹' productShellCell n R H a b) = volume (productShellCell n R H a b) :=
    he.measure_preimage hmeas.nullMeasurableSet
  have hpre : volume (e ⁻¹' productShellCell n R H a b) ≠ ⊤ := by rwa [hmeasure]
  have hmono := measureReal_mono hsub hpre
  simp only [measureReal_def] at hmono
  rw [hmeasure] at hmono
  exact hmono.trans (productShellCell_normal_scale n R C W p k hC hCR hW hp hkR)

/-- Exact real-power algebra for the normal/depth slice scales. -/
theorem cell_scale_algebra (n : ℕ) (R C W p k V : ℝ)
    (hR : 0 < R) (hW : 0 ≤ W) (hp : 0 < p) (hk : 0 < k) :
    (2*(W+1)/p)*((n+2 : ℕ)*(2*R*(C/(k*p)))*
      (Real.sqrt (2*R*(W+2)*k/p))^n*V) =
    (4*(W+1)*(n+2 : ℕ)*C*(2*(W+2))^((n : ℝ)/2)*V)*
      R^(((n : ℝ)+2)/2)*p^(-((n : ℝ)+4)/2)*k^(((n : ℝ)-2)/2) := by
  let a := (n : ℝ)/2
  have hA : 0 < 2*(W+2) := by positivity
  have hbase : 0 ≤ 2*(W+2)*R*k/p := by positivity
  have hs : (Real.sqrt (2*R*(W+2)*k/p))^n =
      (2*(W+2))^a*R^a*k^a/p^a := by
    rw [show 2*R*(W+2)*k/p = 2*(W+2)*R*k/p by ring,Real.sqrt_eq_rpow,
      ← Real.rpow_natCast,← Real.rpow_mul hbase]
    have he : (1/2 : ℝ)*(n : ℝ) = a := by dsimp [a]; ring
    rw [he,Real.div_rpow (by positivity) hp.le,
      Real.mul_rpow (by positivity) hk.le,Real.mul_rpow hA.le hR.le]
  have heR : R^(((n : ℝ)+2)/2) = R^a*R := by
    rw [show ((n : ℝ)+2)/2 = a+1 by dsimp [a]; ring,
      Real.rpow_add hR,Real.rpow_one]
  have hek : k^(((n : ℝ)-2)/2) = k^a/k := by
    rw [show ((n : ℝ)-2)/2 = a-1 by dsimp [a]; ring,
      Real.rpow_sub hk,Real.rpow_one]
  have hep : p^(-((n : ℝ)+4)/2) = (p^a*p^2)⁻¹ := by
    rw [show -((n : ℝ)+4)/2 = -(a+2) by dsimp [a]; ring,
      Real.rpow_neg hp.le,Real.rpow_add hp,Real.rpow_two]
  rw [hs,heR,hek,hep]
  change _ = (4*(W+1)*(n+2 : ℕ)*C*(2*(W+2))^a*V)*(R^a*R)*
    (p^a*p^2)⁻¹*(k^a/k)
  have hpa : p^a ≠ 0 := (Real.rpow_pos_of_pos hp a).ne'
  field_simp
  <;> ring

noncomputable def cellCoefficient (n : ℕ) (W C : ℝ) : ℝ :=
  4*(W+1)*(n+2 : ℕ)*C*(2*(W+2))^((n : ℝ)/2)*
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+2))) 1)

/-- Sharp normal/depth powers for the actual Euclidean cell, including
zero normals as empty summands. This is the estimate consumed by the finite
weighted lattice double sum. -/
theorem depthCell_sharp_volume (n : ℕ) (R C W : ℝ) (q : Fin (n+3) → ℤ) (k : ℕ)
    (hR : 0 < R) (hC : 0 ≤ C) (hCR : C ≤ R) (hW : 0 ≤ W) (hk : 1 ≤ k) :
    volume.real (depthCell (n+3) R W C q k) ≤
      cellCoefficient n W C * R^(((n : ℝ)+2)/2)*
        (LatticeShells.radius q)^(-((n : ℝ)+4)/2)*(k : ℝ)^(((n : ℝ)-2)/2) := by
  by_cases hq : q = 0
  · subst q
    have hz : LatticeShells.radius (0 : Fin (n+3) → ℤ) = 0 := by simp [LatticeShells.radius]
    have he : -((n : ℝ)+4)/2 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    rw [depthCell_zero,hz,Real.zero_rpow he]
    simp
  · have hh := depthCell_volume_le n R C W q k hC hCR hW hq hk
    rw [cell_scale_algebra n R C W _ _ _ hR hW
      (zero_lt_one.trans_le (one_le_integer_radius q hq))
      (by exact_mod_cast (show 0 < k by omega))] at hh
    exact hh

end LinearDistancePreservers.LatticeCaps
