import LinearDistancePreservers.GrowingDimension
import LinearDistancePreservers.FixedGap

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Remove an explicit exponential coefficient, retaining its exact loss. -/
theorem compensate_coefficient {P E K c x q : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hK : K ≤ Real.exp q) (hc : c ≤ 4) (hx : 0 ≤ x)
    (hbound : P*Real.exp (-c*x) ≤ K*E) :
    P*Real.exp (-4*x-q) ≤ E := by
  have hloss : Real.exp (-4*x-q) ≤ Real.exp (-c*x)*Real.exp (-q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc hx
    linarith
  calc
    _ ≤ P*(Real.exp (-c*x)*Real.exp (-q)) := mul_le_mul_of_nonneg_left hloss hP
    _ = (P*Real.exp (-c*x))*Real.exp (-q) := by ring
    _ ≤ (K*E)*Real.exp (-q) := mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
    _ ≤ (Real.exp q*E)*Real.exp (-q) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK hE) (Real.exp_nonneg _)
    _ = E := by rw [mul_right_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

/-- Fully explicit finite dimension dependence with no dimension budget. -/
theorem displayed_lower_bound_quantitative {N T : ℕ} (n : ℕ)
    (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N:ℝ)^((2:ℝ)/(n+4)) *
          (T:ℝ)^((((2*(n+3)+1)*(n+2):ℕ):ℝ)/(((n+3)*(n+4):ℕ):ℝ)) *
          Real.exp (-4*Real.sqrt (Real.log N)-100*((n+3:ℕ):ℝ)^3*Real.log (n+3))
            ≤ (H.edgeFinset.card:ℝ) := by
  have hc : 4*((n+2:ℕ):ℝ)/((n+3:ℕ):ℝ) ≤ 4 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (show 0<n+3 by omega))).mpr
    push_cast
    linarith only [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hpow := dimension_power_le_exp (d := n+3) (by omega : 0<n+3)
    (le_refl (100*((n+3:ℕ):ℝ)^3*Real.log (n+3:ℕ)))
  have hC := LatticeCaps.explicitRadius_bound n
  have hroot := HigherProduct.rateFactor_root_dimension_bound (by omega : 3 ≤ n+3) hC
  obtain ⟨G,S,hS,hG⟩ := displayed_lower_bound_explicit n hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hh := compensate_coefficient
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
    (Nat.cast_nonneg _) (hroot.trans hpow) hc (Real.sqrt_nonneg _) (hG H hHG hpres)
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

/-- A finite lower bound measured directly against T squared. The exponent
is explicit, so this theorem does not hide an eventual dimension-dependent
threshold or assert the printed near-threshold asymptotic range. -/
theorem terminal_lower_bound_quantitative {N T : ℕ} (n : ℕ) (eps : ℝ)
    (hT : 2 ≤ T) (hTN : T ≤ N)
    (hcap : (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3-eps)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T:ℝ)^2 * Real.exp (
          ((3*(n+3)*eps+eps-2/3)/((n+3)*(n+4)))*Real.log N -
            4*Real.sqrt (Real.log N)-100*((n+3:ℕ):ℝ)^3*Real.log (n+3))
          ≤ (H.edgeFinset.card:ℝ) := by
  let η := (3*((n:ℝ)+3)*eps+eps-2/3)/(((n:ℝ)+3)*(n+4))
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hT0 : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hβ : (((2*(n+3)+1)*(n+2):ℕ):ℝ)/(((n+3)*(n+4):ℕ):ℝ) ≤ 2 := by
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hη : (2:ℝ)/(n+4)+
      ((((2*(n+3)+1)*(n+2):ℕ):ℝ)/(((n+3)*(n+4):ℕ):ℝ)-2)*
      ((2:ℝ)/3-eps) = η := by
    dsimp [η]
    push_cast
    field_simp
    ring
  have hr := terminal_rate_lower hN0 hT0 hcap hβ hη
  obtain ⟨G,S,hS,hG⟩ := displayed_lower_bound_quantitative n hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hh := (mul_le_mul_of_nonneg_right hr
    (Real.exp_nonneg (-4*Real.sqrt (Real.log N)-100*((n+3:ℕ):ℝ)^3*Real.log (n+3)))).trans
      (hG H hHG hpres)
  rw [Real.rpow_def_of_pos hN0,mul_assoc,← Real.exp_add] at hh
  convert hh using 1 <;> congr 2 <;> dsimp [η] <;> ring

end LinearDistancePreservers.TheoremFourGeneral
