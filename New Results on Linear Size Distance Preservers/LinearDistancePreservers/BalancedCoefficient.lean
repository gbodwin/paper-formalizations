import LinearDistancePreservers.RootRate

namespace LinearDistancePreservers.HigherProduct

set_option maxHeartbeats 200000 in
/-- A deliberately coarse bound for the literal integer-power coefficient.
The radius upper bound is numerical; the geometry supplying it is separate. -/
theorem balanced_rateFactor_dimension_bound {C d : ℕ} (hd : 3 ≤ d)
    (hC : C ≤ d^(100*d)) : rateFactor C d ≤ d^(1000*d^4) := by
  let c := 2*C+1
  let D := d*(d+1)
  let P := d^(500*d^4)
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have h5 : 1 ≤ d^4 := one_le_pow₀ hd1
  have h15 : d ≤ d^4 := by simpa using Nat.pow_le_pow_right hd1 (show 1≤4 by omega)
  have h25 : d^2 ≤ d^4 := Nat.pow_le_pow_right hd1 (by omega)
  have h35 : d^3 ≤ d^4 := Nat.pow_le_pow_right hd1 (by omega)
  have h45 : d^4 ≤ d^4 := Nat.pow_le_pow_right hd1 (by omega)
  have hc1 : 1 ≤ c := by dsimp [c]; omega
  have hp : 1 ≤ d^(100*d) := one_le_pow₀ hd1
  have hc : c ≤ d^(101*d) := by
    calc
      _ ≤ 3*d^(100*d) := by dsimp [c]; omega
      _ ≤ d*d^(100*d) := Nat.mul_le_mul_right _ hd
      _ = d^(100*d+1) := (pow_succ' d (100*d)).symm
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by omega)
  have hcd : c^d ≤ d^(101*d^2) := by
    calc
      _ ≤ (d^(101*d))^d := Nat.pow_le_pow_left hc d
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hp' : 1 ≤ d^(101*d^2) := one_le_pow₀ hd1
  have hX : c^d+2 ≤ d^(101*d^2+1) := by
    calc
      _ ≤ 3*d^(101*d^2) := by omega
      _ ≤ d*d^(101*d^2) := Nat.mul_le_mul_right _ hd
      _ = _ := (pow_succ' d (101*d^2)).symm
  have h2D : 2^D ≤ d^D := Nat.pow_le_pow_left hd2 D
  have h2s : 2^(d^2) ≤ d^(d^2) := Nat.pow_le_pow_left hd2 _
  have h2ss : 2^(2*d^2) ≤ d^(2*d^2) := Nat.pow_le_pow_left hd2 _
  have hXD : (c^d+2)*2^D ≤ d^(101*d^2+1+D) := by
    calc
      _ ≤ d^(101*d^2+1)*d^D := Nat.mul_le_mul hX h2D
      _ = _ := (pow_add d (101*d^2+1) D).symm
  have hCD : c^d*2^(d^2) ≤ d^(101*d^2+d^2) := by
    calc
      _ ≤ d^(101*d^2)*d^(d^2) := Nat.mul_le_mul hcd h2s
      _ = _ := (pow_add d (101*d^2) (d^2)).symm
  have hsub : (c^d)^(d^2-1) ≤ (d^(101*d^2))^(d^2) :=
    (Nat.pow_le_pow_left hcd _).trans
      (Nat.pow_le_pow_right (one_le_pow₀ hd1) (Nat.sub_le _ _))
  have hsub' : (c^d*2^(d^2))^(d^2-1) ≤ (d^(101*d^2+d^2))^(d^2) :=
    (Nat.pow_le_pow_left hCD _).trans
      (Nat.pow_le_pow_right (one_le_pow₀ hd1) (Nat.sub_le _ _))
  have ha : (c^d+2)^(2*d) ≤ P := by
    calc
      _ ≤ (d^(101*d^2+1))^(2*d) := Nat.pow_le_pow_left hX _
      _ = d^((101*d^2+1)*(2*d)) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by nlinarith only [h15,h35])
  have hb : (c^d)^(d^2-1)*2^D ≤ P := by
    calc
      _ ≤ (d^(101*d^2))^(d^2)*d^D := Nat.mul_le_mul hsub h2D
      _ = d^(101*d^2*d^2+D) := by rw [← pow_mul,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by dsimp [D]; nlinarith only [h15,h25])
  have he : ((c^d+2)*2^D)^(2*d) ≤ P := by
    calc
      _ ≤ (d^(101*d^2+1+D))^(2*d) := Nat.pow_le_pow_left hXD _
      _ = d^((101*d^2+1+D)*(2*d)) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by dsimp [D]; nlinarith only [h15,h25,h35])
  have hf : (c^d*2^(d^2))^(d^2-1)*((c^d+2)*2^D)^(2*d)*
      (2^(2*d^2))^D ≤ P := by
    calc
      _ ≤ (d^(101*d^2+d^2))^(d^2)*(d^(101*d^2+1+D))^(2*d)*(d^(2*d^2))^D :=
        Nat.mul_le_mul (Nat.mul_le_mul hsub' (Nat.pow_le_pow_left hXD _))
          (Nat.pow_le_pow_left h2ss _)
      _ = d^((101*d^2+d^2)*d^2+(101*d^2+1+D)*(2*d)+(2*d^2)*D) := by
        simp only [← pow_mul,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by dsimp [D]; nlinarith only [h15,h25,h35])
  have hfactor : HigherParameters.factor c d ≤ d^(500*d^4+2) := by
    calc
      _ ≤ 4*P := by unfold HigherParameters.factor; change _ ≤ 4*P; dsimp [D] at hb he hf; omega
      _ ≤ d^2*P := Nat.mul_le_mul_right P (by nlinarith only [hd])
      _ = _ := by dsimp [P]; rw [← pow_add]; congr 1; omega
  have h4 : 4 ≤ d^2 := by nlinarith only [hd]
  have h12 : 12 ≤ d^3 := by have hh := Nat.pow_le_pow_left hd 3; norm_num at hh; omega
  have houter4 : 4^(d*(d-1)) ≤ d^(2*d^2) := by
    calc
      _ ≤ (d^2)^(d^2) := (Nat.pow_le_pow_left h4 _).trans
        (Nat.pow_le_pow_right (one_le_pow₀ hd1) (by nlinarith only [Nat.sub_le d 1]))
      _ = _ := by rw [← pow_mul]
  have houter12 : 12^(d^2-1) ≤ d^(3*d^2) := by
    calc
      _ ≤ (d^3)^(d^2) := (Nat.pow_le_pow_left h12 _).trans
        (Nat.pow_le_pow_right (one_le_pow₀ hd1) (Nat.sub_le _ _))
      _ = _ := by rw [← pow_mul]
  let F := 500*d^4+5*d^2+2
  have hlarge : 4^(d*(d-1))*12^(d^2-1)*HigherParameters.factor c d ≤ d^F := by
    calc
      _ ≤ d^(2*d^2)*d^(3*d^2)*d^(500*d^4+2) := Nat.mul_le_mul (Nat.mul_le_mul houter4 houter12) hfactor
      _ = _ := by dsimp [F]; simp only [← pow_add]; congr 1; omega
  have hsmall : 5^(d*(d-1)+(d^2-1))*2^D ≤ d^F := by
    have h5base : 5 ≤ d^2 := by nlinarith only [hd]
    have hpowers : d*(d-1)+(d^2-1) ≤ 2*d^2 := by nlinarith only [Nat.sub_le d 1,Nat.sub_le (d^2) 1]
    calc
      _ ≤ (d^2)^(2*d^2)*d^D := Nat.mul_le_mul
        ((Nat.pow_le_pow_left h5base _).trans (Nat.pow_le_pow_right (one_le_pow₀ hd1) hpowers)) h2D
      _ = d^(2*(2*d^2)+D) := by rw [← pow_mul,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hd1 (by dsimp [D,F]; nlinarith only [h15])
  calc
    _ ≤ 2*d^F := by change _+_ ≤ 2*d^F; dsimp [c,D] at hlarge hsmall; omega
    _ ≤ d*d^F := Nat.mul_le_mul_right _ hd2
    _ = d^(F+1) := (pow_succ' d F).symm
    _ ≤ _ := Nat.pow_le_pow_right hd1 (by dsimp [F]; nlinarith only [h5,h25])

/-- The exact graph coefficient loses only d^(1000 d^2) after taking its root. -/
theorem balanced_rateFactor_root_dimension_bound {C d : ℕ} (hd : 3 ≤ d)
    (hC : C ≤ d^(100*d)) :
    (rateFactor C d : ℝ)^(((d*(d+1) : ℕ) : ℝ)⁻¹) ≤ (d:ℝ)^(1000*d^2) := by
  have hD : d*(d+1) ≠ 0 := by positivity
  have hnat : rateFactor C d ≤ (d^(1000*d^2))^(d*(d+1)) := by
    apply (balanced_rateFactor_dimension_bound hd hC).trans
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    nlinarith only [Nat.zero_le (d^3)]
  have hreal : (rateFactor C d : ℝ) ≤ ((d:ℝ)^(1000*d^2))^(d*(d+1)) := by
    exact_mod_cast hnat
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rwa [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) hD]

end LinearDistancePreservers.HigherProduct

