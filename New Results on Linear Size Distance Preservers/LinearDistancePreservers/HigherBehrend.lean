import LinearDistancePreservers.HigherProduct
import LinearDistancePreservers.HigherRate
import LinearDistancePreservers.PlanarBehrend

/-! All quantitative and graph steps of the general-dimensional lower bound,
conditional only on the explicitly stated sharp integer-ball vertex count.
That count remains an unproved theorem, not an axiom of this development. -/
namespace LinearDistancePreservers.HigherProduct
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def rateFactor (C d : ℕ) : ℕ :=
  4^(d*(d-1))*12^(d^2-1)*HigherParameters.factor (2*C+1) d +
    5^(d*(d-1)+(d^2-1))*2^(d*(d+1))

theorem rateFactor_pos (C d : ℕ) : 0 < rateFactor C d := by
  unfold rateFactor
  positivity

/-- The sharp vertex-count hypothesis is the sole remaining construction
input; all terminal ranges, dimensions, and integer scales are handled. -/
theorem exact_size_lower_bound {N T C d : ℕ} (hd : 1 ≤ d)
    (hvertices : ∀ b : ℕ, 0 < b →
      b^(d*(d-1)) ≤ (LatticeHull.vertices (LatticeHull.ball d (C*b^(d+1)))).card)
    (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T : ℝ)^(d*(d-1)+(d^2-1))*(N : ℝ)^(2*d)*
          (Real.exp (-4*Real.sqrt (Real.log T)))^(d^2-1) ≤
          (rateFactor C d : ℝ)*(H.edgeFinset.card : ℝ)^(d*(d+1)) := by
  by_cases hlarge : 6 ≤ T
  · obtain ⟨M,R,Q,hM,hR,hQM,hcap,hMT,hTM,hQ⟩ := TheoremFourPlanar.terminal_scales hlarge
    obtain ⟨G,S,hS,hE⟩ := capacity_lower_bound hd hvertices hM hR hQM hcap hMT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    have he := HigherRate.real_product_rate hTM hQ (hE H hH hp)
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (show 4^(d*(d-1))*12^(d^2-1)*HigherParameters.factor (2*C+1) d ≤
      rateFactor C d by unfold rateFactor; omega)
  · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound hT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    have he := HigherRate.small_path_rate (p := d*(d-1)+(d^2-1)) (e := d^2-1)
      hT hTN hlarge (by nlinarith : 2*d ≤ d*(d+1))
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (show 5^(d*(d-1)+(d^2-1))*2^(d*(d+1)) ≤ rateFactor C d by
      unfold rateFactor; omega)

/-- The literal displayed general-dimensional rate. The only open
hypothesis is the sharp count of the concrete finite integer-ball vertices. -/
theorem displayed_lower_bound {N T C d : ℕ} (hd : 1 ≤ d)
    (hvertices : ∀ b : ℕ, 0 < b →
      b^(d*(d-1)) ≤ (LatticeHull.vertices (LatticeHull.ball d (C*b^(d+1)))).card)
    (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(d+1)) *
          (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
          Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤
          (rateFactor C d : ℝ)*(H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := exact_size_lower_bound hd hvertices hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  exact HigherRate.dimension_rate hd (by omega) hTN (hE H hH hp)

end LinearDistancePreservers.HigherProduct
