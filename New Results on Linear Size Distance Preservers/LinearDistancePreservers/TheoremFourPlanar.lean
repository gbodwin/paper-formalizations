import LinearDistancePreservers.PlanarProduct
import LinearDistancePreservers.PlanarParameters
import LinearDistancePreservers.UnweightedPath
import LinearDistancePreservers.UnweightedClique

/-! Uniform exact-size planar lower bounds from an explicit outer capacity.
The remaining analytical step is to substitute the quantitative Behrend
estimate with all small-parameter cases handled. -/
namespace LinearDistancePreservers.TheoremFourPlanar
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem square_le_choose {M T : ℕ} (hM : 0 < M) (hT : 2*M ≤ T) :
    M^2 ≤ T.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have hh := Nat.mul_le_mul hT (show M ≤ T-1 by omega)
  nlinarith only [hh]

/-- All vertex and terminal counts are prescribed. Only the scalar outer
capacity Q remains; no lattice, graph, path, or rounding inputs are assumed. -/
theorem capacity_lower_bound {N T M R Q : ℕ}
    (hM : 0 < M) (hR : 3*R ≤ M) (hQM : Q ≤ M)
    (hcap : Q ≤ rothNumberNat R) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        M^2*Q^3*N^4 ≤ 16777216^6*H.edgeFinset.card^6 := by
  have hT2 : 2 ≤ T := by omega
  have hN2 : 2 ≤ N := by omega
  rcases PlanarParameters.parameters_or_baselines hN2 hM hQM with hpath | hclique | hprod
  · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound hT2 hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hpath
  · obtain ⟨G,S,hS,hE⟩ := UnweightedClique.clique_lower_bound (by omega) hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hclique.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (square_le_choose hM hT) 6))
  · obtain ⟨B,x,n,k,hn,hx,hinner,hport,hvert,hedge⟩ := hprod
    letI : NeZero n := ⟨by omega⟩
    letI : NeZero M := ⟨by omega⟩
    obtain ⟨G,S,hS,hE⟩ := PlanarProduct.lower_bound_of_roth hx hinner hR
      (hport.trans hcap) hvert hT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hedge

end LinearDistancePreservers.TheoremFourPlanar
