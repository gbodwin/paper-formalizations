import LinearDistancePreservers.PrimitiveDirections
import LinearDistancePreservers.BehrendProduct

/-! Exact-size unweighted subset-preserver witnesses from the sharp
planar direction construction and Behrend outer ports. All construction
inputs below are numerical. Global parameter optimization, and sharp
directions in higher dimensions, are separate remaining obligations. -/
namespace LinearDistancePreservers.PlanarProduct
open SimpleGraph Finset DirectionGraph DirectionObstacle
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

/-- A planar inner product with exactly N vertices and T terminals.
The hypotheses supply no directions, graph, or path-uniqueness oracle. -/
theorem lower_bound_of_roth {B x n M k R N T : ℕ} [NeZero n] [NeZero M]
    (hx : 4*x ≤ B^2) (hn : (k+1)*(B^3+1) ≤ n) (hM : 3*R ≤ M)
    (hcap : n^2*x ≤ rothNumberNat R)
    (hN : 2*M+M*(k+1)*n^2 ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^2*x*(k+2) := by
  classical
  obtain ⟨v,hinj,hvr,hc⟩ := PrimitiveDirections.exists_planar_directions_of_card hx
  obtain ⟨G,S,hS,hG,hE⟩ := BehrendProduct.exists_product (n := n) (M := M) (k := k)
    v hinj hvr hn hc hM (by simpa using hcap)
  have hv : Fintype.card (ProductVertex Bool Unit n M k) ≤ N := by
    simpa [ProductVertex,ObstacleProduct.Vertex,DirectionGraph.Vertex,ZMod.card,
      mul_assoc,two_mul,add_assoc,add_left_comm,add_comm] using hN
  have hST : S.card ≤ T := hS.le.trans hT
  obtain ⟨K,S',hS',hK,hE'⟩ := UnweightedPadding.pad G S hG hv hST hTN
  refine ⟨K,S',hS',?_⟩
  intro H hH hp
  have heq : H = K := hK H hH hp
  subst H
  simp only [Fintype.card_fin,Fintype.card_bool] at hE
  simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE hE' ⊢
  exact hE'.trans hE

/-- Same graph statement, with the outer capacity supplied by the
explicit quantitative Behrend estimate. -/
theorem lower_bound {B x n M k R N T : ℕ} [NeZero n] [NeZero M]
    (hx : 4*x ≤ B^2) (hn : (k+1)*(B^3+1) ≤ n) (hM : 3*R ≤ M)
    (hcap : ((n^2*x : ℕ) : ℝ) ≤ (R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R)))
    (hN : 2*M+M*(k+1)*n^2 ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^2*x*(k+2) := by
  apply lower_bound_of_roth hx hn hM _ hN hT hTN
  exact_mod_cast hcap.trans Behrend.roth_lower_bound

end LinearDistancePreservers.PlanarProduct
