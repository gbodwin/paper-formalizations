import LinearDistancePreservers.QuarterRootTheorem
import LinearDistancePreservers.NearThresholdEventual

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The target factor is fixed before one threshold, uniformly over every
later graph size and every admissible terminal count in the new range. -/
theorem superquadratic_quarter_root_eventual (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N T : ℕ, N₀≤N → 2≤T → T≤N →
      (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3)*Real.exp (-32*(Real.log N)^((3 : ℝ)/4)) →
      ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
        ∀ H : SimpleGraph (Fin N), H≤G →
          (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
          B*(T : ℝ)^2<(H.edgeFinset.card : ℝ) := by
  obtain ⟨N₀,hN₀⟩ := eventually_sixth_root_threshold B
  refine ⟨N₀,?_⟩
  intro N T hN hT hTN hcap
  obtain ⟨hsize,hfactor⟩ := hN₀ N hN
  obtain ⟨G,S,hS,hG⟩ := superquadratic_quarter_root hT hTN (by linarith : (8 : ℝ)^4≤Real.log N) hcap
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hT0 : (0 : ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hh := mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hT0)
  simpa only [mul_comm] using hh.trans_le (hG H hHG hpres)

end LinearDistancePreservers.TheoremFourGeneral
