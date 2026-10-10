import LinearDistancePreservers.NearThreshold

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Both the concrete sixth-root threshold and every requested edge-factor
threshold eventually hold at all natural graph sizes. -/
theorem eventually_sixth_root_threshold (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (16:ℝ)^6 ≤ Real.log N ∧
      B < Real.exp (Real.sqrt (Real.log N)) := by
  let M := max ((16:ℝ)^3) (max B 0+1)
  have hM : (16:ℝ)^3 ≤ M := le_max_left _ _
  have hMB : max B 0+1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (Real.exp (M^2)+1)
  refine ⟨N₀,?_⟩
  intro N hN
  have hNN : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ)<N := by linarith [Real.exp_pos (M^2)]
  have hlog : M^2 < Real.log N := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hN0]
    linarith
  have hlog0 : 0 ≤ Real.log N := by nlinarith
  have hsqrt := Real.sq_sqrt hlog0
  have hsqrt0 := Real.sqrt_nonneg (Real.log (N:ℝ))
  have hxM : M ≤ Real.sqrt (Real.log N) := by nlinarith
  constructor
  · nlinarith
  · have hB := le_max_left B 0
    have he := Real.add_one_le_exp (Real.sqrt (Real.log N))
    linarith

/-- Quantifier-explicit superquadraticity in the corrected sixth-root
terminal range. The target factor is fixed before the eventual N threshold;
the terminal count may vary with N throughout the displayed range. -/
theorem superquadratic_sixth_root_eventual (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → 2 ≤ T → T ≤ N →
      (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3)*Real.exp (-8*(Real.log N)^((5:ℝ)/6)) →
      ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
        ∀ H : SimpleGraph (Fin N), H ≤ G →
          (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
          B*(T:ℝ)^2 < (H.edgeFinset.card:ℝ) := by
  obtain ⟨N₀,hN₀⟩ := eventually_sixth_root_threshold B
  refine ⟨N₀,?_⟩
  intro N T hN hT hTN hcap
  obtain ⟨hsize,hfactor⟩ := hN₀ N hN
  obtain ⟨G,S,hS,hG⟩ := superquadratic_sixth_root hT hTN hsize hcap
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hT0 : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hh := mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hT0)
  simpa only [mul_comm] using hh.trans_le (hG H hHG hpres)

end LinearDistancePreservers.TheoremFourGeneral
