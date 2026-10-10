import LinearDistancePreservers.TheoremFourPlanar

/-! Quantitative Behrend substitution for the two-dimensional construction.
The sixth-power formulation avoids conventions for fractional powers and
retains the displayed exponents N^(2/3) T^(5/6). -/
namespace LinearDistancePreservers.TheoremFourPlanar
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem terminal_scales {T : ℕ} (hT : 6 ≤ T) :
    ∃ M R Q : ℕ, 0 < M ∧ 3*R ≤ M ∧ Q ≤ M ∧ Q ≤ rothNumberNat R ∧
      2*M ≤ T ∧ T ≤ 4*M ∧
      (T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)) ≤ 12*(Q : ℝ) := by
  let R := T/6
  let M := 3*R
  let Q := rothNumberNat R
  have hR : 0 < R := by
    have : 1 ≤ R := (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mpr (by simpa using hT)
    omega
  have hRT : 6*R ≤ T := by simpa [R,Nat.mul_comm] using Nat.div_mul_le_self T 6
  have hTR : T ≤ 12*R := by
    have hh := Nat.lt_mul_div_succ T (by decide : 0 < 6)
    change T < 6*(R+1) at hh
    omega
  have hRle : R ≤ T := Nat.div_le_self _ _
  have hlog : Real.log (R : ℝ) ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRle)
  have hloss : Real.exp (-4*Real.sqrt (Real.log T)) ≤
      Real.exp (-4*Real.sqrt (Real.log R)) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.sqrt_le_sqrt hlog
    linarith
  refine ⟨M,R,Q,by dsimp [M]; positivity,le_rfl,
    (rothNumberNat_le R).trans (by dsimp [M]; omega),le_rfl,?_,?_,?_⟩
  · dsimp [M]; omega
  · dsimp [M]; omega
  · calc
      _ ≤ (12*(R : ℝ))*Real.exp (-4*Real.sqrt (Real.log T)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hTR) (by positivity)
      _ = 12*((R : ℝ)*Real.exp (-4*Real.sqrt (Real.log T))) := by ring
      _ ≤ 12*((R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R))) := by gcongr
      _ ≤ 12*(Q : ℝ) := mul_le_mul_of_nonneg_left Behrend.roth_lower_bound (by norm_num)

theorem real_product_rate {N T M Q E : ℕ}
    (hT : T ≤ 4*M)
    (hQ : (T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)) ≤ 12*(Q : ℝ))
    (hE : M^2*Q^3*N^4 ≤ 16777216^6*E^6) :
    (T : ℝ)^5*(N : ℝ)^4*(Real.exp (-4*Real.sqrt (Real.log T)))^3 ≤
      100663296^6*(E : ℝ)^6 := by
  have ht : (T : ℝ) ≤ 4*(M : ℝ) := by exact_mod_cast hT
  have he : (M : ℝ)^2*(Q : ℝ)^3*(N : ℝ)^4 ≤ 16777216^6*(E : ℝ)^6 := by
    exact_mod_cast hE
  calc
    _ = (T : ℝ)^2*((T : ℝ)*Real.exp (-4*Real.sqrt (Real.log T)))^3*(N : ℝ)^4 := by ring
    _ ≤ (4*(M : ℝ))^2*(12*(Q : ℝ))^3*(N : ℝ)^4 := by gcongr
    _ = 27648*((M : ℝ)^2*(Q : ℝ)^3*(N : ℝ)^4) := by ring
    _ ≤ 27648*(16777216^6*(E : ℝ)^6) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ _ := by nlinarith only [pow_nonneg (Nat.cast_nonneg E : (0 : ℝ) ≤ E) 6]

theorem small_path_rate {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) (hlarge : ¬ 6 ≤ T) :
    (T : ℝ)^5*(N : ℝ)^4*(Real.exp (-4*Real.sqrt (Real.log T)))^3 ≤
      100663296^6*((N-1 : ℕ) : ℝ)^6 := by
  have hT5 : (T : ℝ) ≤ 5 := by exact_mod_cast (show T ≤ 5 by omega)
  have hTNr : (T : ℝ) ≤ N := by exact_mod_cast hTN
  have hN : (N : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ 2*(N-1) by omega)
  have hloss : Real.exp (-4*Real.sqrt (Real.log T)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (Real.log T); linarith)
  calc
    _ ≤ (T : ℝ)^5*(N : ℝ)^4*1 := by gcongr; simpa using pow_le_pow_left₀ (by positivity) hloss 3
    _ = (T : ℝ)^3*(T : ℝ)^2*(N : ℝ)^4 := by ring
    _ ≤ (5 : ℝ)^3*(N : ℝ)^2*(N : ℝ)^4 := by gcongr
    _ = 125*(N : ℝ)^6 := by ring
    _ ≤ 125*(2*((N-1 : ℕ) : ℝ))^6 := by gcongr
    _ ≤ _ := by nlinarith only [pow_nonneg (Nat.cast_nonneg (N-1) : (0 : ℝ) ≤ (N-1 : ℕ)) 6]

theorem rate_of_sixth_power {N T E : ℕ}
    (h : (T : ℝ)^5*(N : ℝ)^4*(Real.exp (-4*Real.sqrt (Real.log T)))^3 ≤
      100663296^6*(E : ℝ)^6) :
    (N : ℝ)^((2 : ℝ)/3)*(T : ℝ)^((5 : ℝ)/6)*
      Real.exp (-2*Real.sqrt (Real.log T)) ≤ 100663296*(E : ℝ) := by
  have hn : ((N : ℝ)^((2 : ℝ)/3))^6 = (N : ℝ)^4 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have ht : ((T : ℝ)^((5 : ℝ)/6))^6 = (T : ℝ)^5 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T)]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 6 ≠ 0)).mp
  rw [mul_pow,mul_pow,hn,ht,← Real.exp_nat_mul]
  rw [mul_pow]
  have hh : ((6 : ℕ) : ℝ)*(-2*Real.sqrt (Real.log T)) = ((3 : ℕ) : ℝ)*(-4*Real.sqrt (Real.log T)) := by push_cast; ring
  rw [hh,Real.exp_nat_mul]
  nlinarith only [h]

/-- Finite d=2 lower bound for every prescribed 2≤T≤N. Taking sixth roots
gives E ≥ (100663296)⁻¹ N^(2/3) T^(5/6) exp(-2 sqrt(log T)). -/
theorem exact_size_lower_bound {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T : ℝ)^5*(N : ℝ)^4*(Real.exp (-4*Real.sqrt (Real.log T)))^3 ≤
          100663296^6*(H.edgeFinset.card : ℝ)^6 := by
  by_cases hlarge : 6 ≤ T
  · obtain ⟨M,R,Q,hM,hR,hQM,hcap,hMT,hTM,hQ⟩ := terminal_scales hlarge
    obtain ⟨G,S,hS,hE⟩ := capacity_lower_bound hM hR hQM hcap hMT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    exact real_product_rate hTM hQ (hE H hH hp)
  · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound hT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact small_path_rate hT hTN hlarge

/-- The literal displayed d=2 rate, uniformly for every 2≤T≤N.
The graph and terminal set have the exact prescribed cardinalities. -/
theorem displayed_lower_bound {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N : ℝ)^((2 : ℝ)/3)*(T : ℝ)^((5 : ℝ)/6)*
          Real.exp (-2*Real.sqrt (Real.log N)) ≤ 100663296*(H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := exact_size_lower_bound hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hr := rate_of_sixth_power (hE H hH hp)
  have hlog : Real.log (T : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < T by omega)) (by exact_mod_cast hTN)
  have hloss : Real.exp (-2*Real.sqrt (Real.log N)) ≤
      Real.exp (-2*Real.sqrt (Real.log T)) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.sqrt_le_sqrt hlog
    linarith
  exact (mul_le_mul_of_nonneg_left hloss (by positivity)).trans hr

end LinearDistancePreservers.TheoremFourPlanar
