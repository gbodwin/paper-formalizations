import LinearDistancePreservers.SphereCoefficients

namespace LinearDistancePreservers.SphereScales
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Every numerical scale and outer Behrend capacity is selected internally. -/
theorem exact_size_power_bound {N T d : ℕ} (hd : 3≤d)
    (hT : 2≤T) (hTN : 2*T≤N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (T : ℝ)^(d*(d-2)+(d+1)*(d-2))*(N : ℝ)^(2*d-2)*
          (Real.exp (-4*Real.sqrt (Real.log T)))^((d+1)*(d-2)) ≤
          ((sphereFactor d : ℝ)^(d^2-2))*(H.edgeFinset.card : ℝ)^(d^2-2) := by
  obtain ⟨hc,hsmall⟩ := terminal_coefficients hd (sphere_coefficient_bound hd)
  by_cases hlarge : 6≤T
  · obtain ⟨M,R,Q,hM,hR,hQM,hcap,hMT,hTM,hQ⟩ := TheoremFourPlanar.terminal_scales hlarge
    have hQpos : 0<Q := by
      have ht : (0 : ℝ)<(T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)) := by positivity
      have hq : (0 : ℝ)<Q := by linarith
      exact_mod_cast hq
    obtain ⟨G,S,hS,hE⟩ := capacity_power_bound (N := N) (T := T) hd hM hQpos hQM hR hcap (by omega) hMT (by omega)
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    have hh : M^(d*(d-2))*Q^((d+1)*(d-2))*N^(2*d-2) ≤
        (2^((3*d-1)*(d^2-2)+(2*d-2))*d^(d*(d-2)))*H.edgeFinset.card^(d^2-2) := by
      exact_mod_cast hE H hH hp
    have he := HigherRate.real_product_rate hTM hQ hh
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast hc
  · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound hT (by omega : T≤N)
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    have hD := Nat.sub_add_cancel (show 2≤d^2 by nlinarith)
    have hq := Nat.sub_add_cancel (show 2≤2*d by omega)
    have he := HigherRate.small_path_rate (p := d*(d-2)+(d+1)*(d-2))
      (e := (d+1)*(d-2)) hT (by omega : T≤N) hlarge
      (by nlinarith : 2*d-2≤d^2-2)
    exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) (by positivity))

/-- Elementary spheres give an actual graph rate with coefficient at most
exp(7d); no lattice vertex-count or scale-selection premise remains. -/
theorem exact_size_lower_bound {N T d : ℕ} (hd : 3≤d)
    (hT : 2≤T) (hTN : 2*T≤N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (N : ℝ)^(((2*d-2 : ℕ) : ℝ)/(d^2-2 : ℕ))*
          (T : ℝ)^((((2*d+1)*(d-2) : ℕ) : ℝ)/(d^2-2 : ℕ))*
          Real.exp (-4*Real.sqrt (Real.log N)) ≤
          (sphereFactor d : ℝ)*(H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := exact_size_power_bound hd hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  let D := d^2-2
  have hD : D≠0 := by
    dsimp [D]
    have hh : 9≤d^2 := by nlinarith
    omega
  have hDr : (0 : ℝ)<D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hpdim : d*(d-2)+(d+1)*(d-2)=(2*d+1)*(d-2) := by ring
  have hpower : (T : ℝ)^(d*(d-2)+(d+1)*(d-2))*(N : ℝ)^(2*d-2)*
      (Real.exp (-4*Real.sqrt (Real.log T)))^((d+1)*(d-2)) ≤
      ((sphereFactor d^D : ℕ) : ℝ)*(H.edgeFinset.card : ℝ)^D := by
    simpa [D] using hE H hH hp
  have hr := HigherRate.rate_of_power_root hD hpower
  have hroot : ((sphereFactor d^D : ℕ) : ℝ)^((D : ℝ)⁻¹)=(sphereFactor d : ℝ) := by
    rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul (by positivity),mul_inv_cancel₀ hDr.ne',Real.rpow_one]
  rw [hroot,hpdim] at hr
  have hs := Nat.sub_add_cancel (show 2≤d by omega)
  have hDsub := Nat.sub_add_cancel (show 2≤d^2 by nlinarith)
  have heD : (d+1)*(d-2)≤D := by dsimp [D]; nlinarith
  have hcoef : (0 : ℝ)≤4*((d+1)*(d-2) : ℕ)/D := by positivity
  have hcoef4 : (4 : ℝ)*((d+1)*(d-2) : ℕ)/D≤4 := by
    apply (div_le_iff₀ hDr).mpr
    have hh : (((d+1)*(d-2) : ℕ) : ℝ)≤D := by exact_mod_cast heD
    linarith
  have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log (by positivity : (0 : ℝ)<T)
    (by exact_mod_cast (show T≤N by omega) : (T : ℝ)≤(N : ℝ)))
  have hloss : Real.exp (-4*Real.sqrt (Real.log N))≤
      Real.exp (-(4*((d+1)*(d-2) : ℕ)/D)*Real.sqrt (Real.log T)) := by
    apply Real.exp_le_exp.mpr
    have ht0 := Real.sqrt_nonneg (Real.log (T : ℝ))
    nlinarith
  exact (mul_le_mul_of_nonneg_left hloss (by positivity)).trans hr

end LinearDistancePreservers.SphereScales

