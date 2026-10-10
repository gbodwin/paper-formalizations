import LinearDistancePreservers.HigherParameters
import LinearDistancePreservers.LatticeProduct
import LinearDistancePreservers.TheoremFourPlanar

/-! General-dimensional parameter selection assembled with the native
unweighted graph. The single open geometric input is explicitly a lower
bound on the number of actual vertices of the finite integer-ball hull.
It is an ordinary theorem hypothesis, not an axiom or a completed estimate. -/
namespace LinearDistancePreservers.HigherProduct
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Conditional on a sharp lattice-ball count, all prescribed vertex
and terminal counts and all integer rounding are handled by proved lemmas.
No direction, path-uniqueness, or graph construction input remains. -/
theorem capacity_lower_bound {N T M R Q C d : ℕ}
    (hd : 1 ≤ d)
    (hvertices : ∀ b : ℕ, 0 < b →
      b^(d*(d-1)) ≤ (LatticeHull.vertices (LatticeHull.ball d (C*b^(d+1)))).card)
    (hM : 0 < M) (hR : 3*R ≤ M) (hQM : Q ≤ M)
    (hcap : Q ≤ rothNumberNat R) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤
          HigherParameters.factor (2*C+1) d*H.edgeFinset.card^(d*(d+1)) := by
  have hT2 : 2 ≤ T := by omega
  have hN2 : 2 ≤ N := by omega
  rcases HigherParameters.parameters_or_baselines (c := 2*C+1)
      (by omega) hd hN2 hM hQM with hpath | hclique | hprod
  · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound hT2 hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hpath
  · obtain ⟨G,S,hS,hE⟩ := UnweightedClique.clique_lower_bound (by omega) hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hclique.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (TheoremFourPlanar.square_le_choose hM hT) (d*(d+1))))
  · obtain ⟨b,n,k,hb,hn,hinner,hport,hvert,hedge⟩ := hprod
    letI : NeZero n := ⟨by omega⟩
    letI : NeZero M := ⟨by omega⟩
    have hbpow : 1 ≤ b^(d+1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hB : 2*(C*b^(d+1))+1 ≤ (2*C+1)*b^(d+1) := by nlinarith only [hbpow]
    have hinner' : (k+1)*(2*(C*b^(d+1))+1) ≤ n :=
      (Nat.mul_le_mul_left _ hB).trans hinner
    obtain ⟨G,S,hS,hE⟩ := LatticeProduct.lower_bound_of_roth (hvertices b hb) hinner' hR
      (hport.trans hcap) hvert hT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    exact hedge

end LinearDistancePreservers.HigherProduct
