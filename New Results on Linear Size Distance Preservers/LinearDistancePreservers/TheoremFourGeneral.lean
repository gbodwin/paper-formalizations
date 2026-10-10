import LinearDistancePreservers.LatticeVertices
import LinearDistancePreservers.HigherBehrend

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The literal lower-bound rate in every dimension at least two, with no
unproved geometric premise. The constant depends only on the dimension;
all vertex and terminal counts are prescribed exactly. -/
theorem displayed_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℕ, 0 < K ∧ ∀ N T : ℕ, 2 ≤ T → T ≤ N →
      ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
        ∀ H : SimpleGraph (Fin N), H ≤ G →
          (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
          (N : ℝ)^((2 : ℝ)/(d+1)) *
            (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
            Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤
            (K : ℝ)*(H.edgeFinset.card : ℝ) := by
  by_cases hd2 : d = 2
  · subst d
    refine ⟨100663296,by norm_num,?_⟩
    intro N T hT hTN
    convert TheoremFourPlanar.displayed_lower_bound hT hTN using 1 <;> norm_num
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, d = n+3 := ⟨d-3,by omega⟩
    obtain ⟨C,hC,hvertices⟩ := LatticeHull.uniform_vertices n
    refine ⟨HigherProduct.rateFactor C (n+3),HigherProduct.rateFactor_pos _ _,?_⟩
    intro N T hT hTN
    apply HigherProduct.displayed_lower_bound (C := C) (by omega) _ hT hTN
    simpa only [show n+3-1=n+2 by omega,show n+3+1=n+4 by omega] using hvertices

end LinearDistancePreservers.TheoremFourGeneral
