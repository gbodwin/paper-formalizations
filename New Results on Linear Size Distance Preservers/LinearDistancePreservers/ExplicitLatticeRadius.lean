import LinearDistancePreservers.LatticeVertices

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory Metric Set Finset

noncomputable def missedCoefficient (n : ℕ) : ℝ :=
  (n+3 : ℕ)*volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)+
    deepCoefficient n+1

noncomputable def missedThreshold (n : ℕ) : ℕ :=
  Nat.ceil (depthConstant (n+2)+1)+1

theorem concrete_missed_volume_bound (n : ℕ) :
    0 < missedCoefficient n ∧ ∀ R : ℕ, missedThreshold n ≤ R →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) R \ LatticeBody.body (n+3) R) ≤
        missedCoefficient n*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := by
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let D := deepCoefficient n
  let C := depthConstant (n+2)
  let A := (n+3 : ℕ)*V+D+1
  have hV : 0 ≤ V := measureReal_nonneg
  have hC : 0 ≤ C := by dsimp [C,depthConstant,flatnessWidth]; positivity
  have hD : 0 ≤ D := by dsimp [D,deepCoefficient,cellCoefficient,depthConstant,flatnessWidth]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let R₀ := missedThreshold n
  have hR₀ : C+1 < (R₀ : ℝ) := by
    have hh := Nat.le_ceil (C+1)
    dsimp [R₀,missedThreshold,C]
    push_cast
    linarith
  refine ⟨hA,?_⟩
  intro R hR
  have hRR : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hCR : C ≤ R := by linarith
  have hR0 : (0 : ℝ) < R := zero_lt_one.trans_le hR1
  let δ := criticalHeight n R
  have hδ : 0 < δ := Real.rpow_pos_of_pos hR0 _
  have hδR : δ ≤ R := by
    apply (Real.rpow_le_one_of_one_le_of_nonpos hR1 (neg_nonpos.mpr (by positivity))).trans hR1
  have hcover := missed_subset_shallow_union_deep (n+2) R δ hδ
  have hunion : volume (shallowCaps (n+3) R δ ∪ deepCells (n+2) R δ) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.union_subset
      ((shallowCaps_subset_annulus hδR).trans Set.sdiff_subset)
      (deepCells_subset_closedBall (n+2) R δ)) measure_closedBall_lt_top.ne
  have hm := measureReal_mono hcover hunion
  have hs0 := shallowCaps_critical_volume (n+2) R hR1
  have hs : volume.real (shallowCaps (n+3) R δ) ≤
      (n+3 : ℕ)*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4))*V := by
    simpa [δ,criticalHeight,V,Nat.cast_add,Nat.cast_ofNat,← neg_div,show n+2+1=n+3 by omega,show (n : ℝ)+2+2=n+4 by ring] using hs0
  have hd := deepCells_critical_volume n R hR1 hCR
  have hrpow : 0 ≤ (R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) := Real.rpow_nonneg hR0.le _
  have hsum := (measureReal_union_le (μ := volume) (shallowCaps (n+3) R δ) (deepCells (n+2) R δ))
  change volume.real (deepCells (n+2) R δ) ≤ D*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4)) at hd
  change _ ≤ A*(R : ℝ)^(((n : ℝ)+3)*((n : ℝ)+2)/(n+4))
  dsimp [A]
  nlinarith [hm,hsum]

end LinearDistancePreservers.LatticeCaps

namespace LinearDistancePreservers.LatticeBody
open Set Metric MeasureTheory

noncomputable def vertexRadius (n : ℕ) (A : ℝ) (R₀ : ℕ) : ℕ :=
  Nat.ceil (max (4*((2^(n+3) : ℕ) : ℝ)^2*A /
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) (R₀ : ℝ))+2

theorem uniform_vertices_explicit_radius {n R₀ : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A)
    (hmiss : ∀ R : ℕ, R₀ ≤ R →
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) R \ body (n+1) R) ≤
        A * (R : ℝ)^(((n+1 : ℕ) : ℝ)*n/(n+2))) :
    0 < vertexRadius n A R₀ ∧ ∀ b : ℕ, 0 < b →
      b^((n+1)*n) ≤ (LatticeHull.vertices (LatticeHull.ball (n+1)
        (vertexRadius n A R₀*b^(n+2)))).card := by
  let B := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
  let K : ℕ := 2^(n+3)
  let a : ℝ := ((n+1 : ℕ) : ℝ)*n/(n+2)
  have hB : 0 < B := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0 : ℝ) < 1)).ne'
    measure_closedBall_lt_top.ne
  have hK : 0 < K := by dsimp [K]; positivity
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  let C := vertexRadius n A R₀
  have hC : max (4*(K : ℝ)^2*A/B) (R₀ : ℝ)+1 < (C : ℝ) := by
    have hh := Nat.le_ceil (max (4*(K : ℝ)^2*A/B) (R₀ : ℝ))
    dsimp [C,vertexRadius,K,B]
    push_cast
    dsimp [K,B] at hh
    push_cast at hh
    linarith
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
  refine ⟨hCpos,?_⟩
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

namespace LinearDistancePreservers.LatticeHull

/-- A closed dimension-dependent radius factor, with all ceiling witnesses
exposed. A small-growth bound for this explicit number is still separate. -/
noncomputable def explicitRadius (n : ℕ) : ℕ :=
  LatticeBody.vertexRadius (n+2) (LatticeCaps.missedCoefficient n)
    (LatticeCaps.missedThreshold n)

theorem uniform_vertices_explicit (n : ℕ) :
    0 < explicitRadius n ∧ ∀ b : ℕ, 0 < b →
      b^((n+3)*(n+2)) ≤ (vertices (ball (n+3) (explicitRadius n*b^(n+4)))).card := by
  obtain ⟨hA,hmiss⟩ := LatticeCaps.concrete_missed_volume_bound n
  have hh := LatticeBody.uniform_vertices_explicit_radius (n := n+2)
    (by omega) hA (by
      intro R hR
      convert hmiss R hR using 1 <;> norm_num [Nat.cast_add,Nat.cast_ofNat] <;> ring_nf <;> simp)
  simpa [explicitRadius,add_assoc] using hh

end LinearDistancePreservers.LatticeHull
