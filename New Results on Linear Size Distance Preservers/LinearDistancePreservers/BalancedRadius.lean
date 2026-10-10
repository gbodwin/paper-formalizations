import LinearDistancePreservers.BalancedVolume

set_option maxRecDepth 2048

namespace LinearDistancePreservers.LatticeHull
open MeasureTheory Metric

noncomputable def balancedRadius (n : ℕ) : ℕ :=
  LatticeBody.vertexRadius (n+2) (LatticeCaps.balancedCoefficient n)
    (LatticeCaps.balancedThreshold n)

theorem balanced_radius_vertices (n : ℕ) :
    0 < balancedRadius n ∧ ∀ b : ℕ, 0 < b →
      b^((n+3)*(n+2)) ≤ (vertices (ball (n+3) (balancedRadius n*b^(n+4)))).card := by
  obtain ⟨hA,hR⟩ := LatticeCaps.balanced_missed_volume_bound n
  have hh := LatticeBody.uniform_vertices_explicit_radius (n := n+2)
    (R₀ := LatticeCaps.balancedThreshold n) (by omega) hA (by
      intro R hr
      convert hR R hr using 1 <;> norm_num [Nat.cast_add,Nat.cast_ofNat] <;> ring_nf <;> simp)
  simpa [balancedRadius,add_assoc] using hh

/-- Balancing the actual shallow and deep volumes improves the explicit
radius factor from d^(O(d²)) to d^(O(d)). -/
theorem balancedRadius_bound (n : ℕ) : balancedRadius n ≤ (n+3)^(100*(n+3)) := by
  let d : ℕ := n+3
  let x : ℝ := d
  let Q : ℕ := LatticeCaps.balanceScale n
  let V := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n+3))) 1)
  let A := LatticeCaps.balancedCoefficient n
  let J : ℕ := 2^(n+5)
  let Z := max (4*(J : ℝ)^2*A/V) ((Q^2 : ℕ) : ℝ)
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hx3 : (3 : ℝ) ≤ x := by change (3 : ℝ) ≤ (d : ℝ); exact_mod_cast hd
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume _ (by norm_num : (0 : ℝ)<1)).ne'
    measure_closedBall_lt_top.ne
  have hQ : (Q : ℝ)=x^(40*d) := by
    dsimp [Q,LatticeCaps.balanceScale,x,d]
    rw [Nat.cast_pow]
  have hA : 0 < A := (LatticeCaps.balanced_missed_volume_bound n).1
  have hratio : A/V=x*(Q : ℝ)+1 := by
    change ((x*(Q : ℝ)+1)*V)/V=x*(Q : ℝ)+1
    exact mul_div_cancel_right₀ _ hV.ne'
  have ha : A/V ≤ x^(40*d+2) := by
    rw [hratio,hQ,← pow_succ']
    have hp : 1 ≤ x^(40*d+1) := one_le_pow₀ hx1
    calc
      _ ≤ 2*x^(40*d+1) := by linarith
      _ ≤ x*x^(40*d+1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [← pow_succ']
  have hJ : (J : ℝ) ≤ x^(d+2) := by
    dsimp [J,x,d]
    push_cast
    exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 2≤n+3 by omega)) _
  have hscale : 4*(J : ℝ)^2 ≤ x^(2*d+6) := by
    calc
      _ ≤ x^2*(x^(d+2))^2 := by gcongr; nlinarith
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hterm : 4*(J : ℝ)^2*A/V ≤ x^(80*d) := by
    calc
      _ = (4*(J : ℝ)^2)*(A/V) := by ring
      _ ≤ x^(2*d+6)*x^(40*d+2) := mul_le_mul hscale ha
        (div_nonneg hA.le hV.le) (by positivity)
      _ = x^(42*d+8) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hx1 (by omega)
  have hthreshold : ((Q^2 : ℕ) : ℝ)=x^(80*d) := by
    rw [Nat.cast_pow,hQ,← pow_mul]
    congr 1
    omega
  have hZ : Z ≤ x^(80*d) := max_le hterm (le_of_eq hthreshold)
  have hZ0 : 0 ≤ Z := (Nat.cast_nonneg (Q^2)).trans (le_max_right _ _)
  have hc := Nat.ceil_lt_add_one hZ0
  have hp : 3 ≤ x^(80*d) := hx3.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1≤80*d by omega))
  have hm := mul_le_mul_of_nonneg_right hx3 (by positivity : 0≤x^(80*d))
  have hfinal : (balancedRadius n : ℝ) ≤ x^(100*d) := by
    change ((⌈Z⌉₊+2 : ℕ) : ℝ) ≤ x^(100*d)
    rw [Nat.cast_add,Nat.cast_ofNat]
    calc
      _ ≤ x^(80*d)+3 := by linarith
      _ ≤ x*x^(80*d) := by nlinarith only [hp,hm]
      _ = x^(80*d+1) := by rw [← pow_succ']
      _ ≤ _ := pow_le_pow_right₀ hx1 (by omega)
  dsimp [x,d] at hfinal
  exact_mod_cast hfinal

end LinearDistancePreservers.LatticeHull

