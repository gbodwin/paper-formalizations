import LinearDistancePreservers.PolytopeApproximation
import LinearDistancePreservers.LatticeBody
import Mathlib.Analysis.Convex.KreinMilman

namespace LinearDistancePreservers.LatticeBody
open Set Metric MeasureTheory

/-- The actual finite integer hull is recovered from exactly the vertices
used by the graph construction. Compactness removes the Krein--Milman closure. -/
theorem convexHull_vertices (d R : ℕ) :
    convexHull ℝ (vector '' (LatticeHull.vertices (LatticeHull.ball d R) : Set (Fin d → ℤ))) =
      body d R := by
  have h := closure_convexHull_extremePoints (isCompact_body d R) (convex_convexHull ℝ _)
  rw [← image_vertices] at h
  have hcompact := ((LatticeHull.vertices (LatticeHull.ball d R)).finite_toSet.image vector).isCompact_convexHull ℝ
  rwa [hcompact.isClosed.closure_eq] at h

/-- A sharp-order approximation lower bound for the concrete lattice hull.
The displayed finite count condition is an inequality, not an oracle for
facets, normals, or a replacement polytope. -/
theorem missed_volume_lower_grid {n R m : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hcard : 2^(n+3) * (LatticeHull.vertices (LatticeHull.ball (n+1) R)).card ≤ m^n) :
    (R : ℝ)^(n+1) * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) /
      (4 * (m : ℝ)^2) ≤
      volume.real (closedBall 0 R \ body (n+1) R) := by
  classical
  let V := (LatticeHull.vertices (LatticeHull.ball (n+1) R)).image vector
  have hV : ∀ u ∈ V, ‖u‖ ≤ (R : ℝ) := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
    have hball := (Finset.mem_filter.mp hz).1
    simpa using (vector_mem_closedBall_iff z).mpr hball
  have hc : 2^(n+3) * V.card ≤ m^n :=
    (Nat.mul_le_mul_left _ Finset.card_image_le).trans hcard
  have hh := PolytopeApproximation.missed_volume_lower_grid_scaled
    (by exact_mod_cast hR : (0 : ℝ) < R) hm
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) hV hc
  have he : convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n+1)))) = body (n+1) R := by
    simpa only [V,Finset.coe_image] using convexHull_vertices (n+1) R
  rwa [he] at hh

/-- A sufficiently small missed volume forces many actual lattice vertices. -/
theorem vertex_count_of_missed_volume {n R m : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hvol : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R \ body (n+1) R) <
      (R : ℝ)^(n+1) * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) /
        (4 * (m : ℝ)^2)) :
    m^n < 2^(n+3) * (LatticeHull.vertices (LatticeHull.ball (n+1) R)).card := by
  by_contra! h
  exact (not_lt_of_ge (missed_volume_lower_grid hR hm h)) hvol

/-- The only remaining geometric estimate needed for the graph-facing
sharp vertex count is an eventual sharp-order missed-volume upper bound.
All approximation, radius scaling, constants, and small b are handled here. -/
theorem uniform_vertices_of_missed_bound {n R₀ : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A)
    (hmiss : ∀ R : ℕ, R₀ ≤ R →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R \ body (n+1) R) ≤
        A * (R : ℝ)^(((n+1 : ℕ) : ℝ)*n/(n+2))) :
    ∃ C : ℕ, 0 < C ∧ ∀ b : ℕ, 0 < b →
      b^((n+1)*n) ≤ (LatticeHull.vertices (LatticeHull.ball (n+1) (C*b^(n+2)))).card := by
  let B := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
  let K : ℕ := 2^(n+3)
  let a : ℝ := ((n+1 : ℕ) : ℝ)*n/(n+2)
  have hB : 0 < B := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0 : ℝ) < 1)).ne'
    measure_closedBall_lt_top.ne
  have hK : 0 < K := by dsimp [K]; positivity
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨C,hC⟩ := exists_nat_gt (max (4*(K : ℝ)^2*A/B) (R₀ : ℝ) + 1)
  have hC1 : (1 : ℝ) < C := by
    have h0 : (0 : ℝ) ≤ max (4*(K : ℝ)^2*A/B) (R₀ : ℝ) := (Nat.cast_nonneg R₀).trans (le_max_right _ _)
    linarith
  have hCpos : 0 < C := by exact_mod_cast (zero_lt_one.trans hC1)
  have hCR : (0 : ℝ) < C := by positivity
  have hC₀ : R₀ ≤ C := by
    have hh : (R₀ : ℝ) ≤ C := by have := le_max_right (4*(K : ℝ)^2*A/B) (R₀ : ℝ); linarith
    exact_mod_cast hh
  have hCV : 4*(K : ℝ)^2*A < (C : ℝ)*B := by
    apply (div_lt_iff₀ hB).mp
    have := le_max_left (4*(K : ℝ)^2*A/B) (R₀ : ℝ)
    linarith
  have ha : a+1 ≤ (n+1 : ℕ) := by
    dsimp [a]
    have hnR : (0 : ℝ) ≤ n := by positivity
    have hd : (0 : ℝ) < (n : ℝ)+2 := by positivity
    have he : ((n+1 : ℕ) : ℝ)*n/((n : ℝ)+2) ≤ n := by
      apply (div_le_iff₀ hd).mpr
      push_cast
      nlinarith
    push_cast at *
    linarith
  have hCa : (C : ℝ)^a * C ≤ (C : ℝ)^(n+1) := by
    calc
      _ = (C : ℝ)^(a+1) := by rw [Real.rpow_add hCR,Real.rpow_one]
      _ ≤ _ := by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hC1.le ha
  have hcoef : A*(C : ℝ)^a < (C : ℝ)^(n+1)*B/(4*(K : ℝ)^2) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4*(K : ℝ)^2)).mpr
    have hh := mul_lt_mul_of_pos_right hCV (Real.rpow_pos_of_pos hCR a)
    have hh' := mul_le_mul_of_nonneg_right hCa hB.le
    nlinarith
  refine ⟨C,hCpos,?_⟩
  intro b hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  let R := C*b^(n+2)
  let m := K*b^(n+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hlarge : R₀ ≤ R := hC₀.trans (Nat.le_mul_of_pos_right C (by positivity))
  by_contra! hc
  have hKn : K ≤ K^n := Nat.le_self_pow hn.ne' K
  have hcount : K*(LatticeHull.vertices (LatticeHull.ball (n+1) R)).card ≤ m^n := by
    calc
      _ ≤ K*b^((n+1)*n) := Nat.mul_le_mul_left _ hc.le
      _ ≤ K^n*b^((n+1)*n) := Nat.mul_le_mul_right _ hKn
      _ = _ := by simp only [m,mul_pow,← pow_mul]
  have hlow := missed_volume_lower_grid hR hm hcount
  have hupp := hmiss R hlarge
  have hpower : ((b : ℝ)^(n+2))^a = (b : ℝ)^((n+1)*n) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hbR.le]
    have he : ((n+2 : ℕ) : ℝ)*a = ((n+1)*n : ℕ) := by
      dsimp [a]; push_cast; field_simp <;> ring
    rw [he,Real.rpow_natCast]
  have hRp : (R : ℝ)^a = (C : ℝ)^a*(b : ℝ)^((n+1)*n) := by
    dsimp [R]
    push_cast
    rw [Real.mul_rpow hCR.le (pow_nonneg hbR.le _),hpower]
  have hbp : ((b : ℝ)^(n+2))^(n+1) = (b : ℝ)^((n+1)*n)*((b : ℝ)^(n+1))^2 := by
    rw [← pow_mul,← pow_mul,← pow_add]
    congr 1
    ring
  have hleft : (R : ℝ)^(n+1)*B/(4*(m : ℝ)^2) =
      ((C : ℝ)^(n+1)*B/(4*(K : ℝ)^2)) * (b : ℝ)^((n+1)*n) := by
    dsimp [R,m]
    push_cast
    rw [mul_pow,mul_pow,hbp]
    field_simp
  have hstrict := mul_lt_mul_of_pos_right hcoef (pow_pos hbR ((n+1)*n))
  change (R : ℝ)^(n+1)*B/(4*(m : ℝ)^2) ≤ _ at hlow
  change _ ≤ A*(R : ℝ)^a at hupp
  rw [hleft] at hlow
  rw [hRp] at hupp
  nlinarith

end LinearDistancePreservers.LatticeBody
