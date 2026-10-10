import LinearDistancePreservers.LatticeHull
import LinearDistancePreservers.BehrendProduct

/-! Actual unweighted graph witnesses from vertices of the integer ball.
The only remaining geometric input is an inequality about the cardinality
of a concretely defined finite set. No direction family, convexity, path
uniqueness, graph, or forced-edge hypothesis is supplied by the caller.
This does not prove the sharp higher-dimensional vertex-count estimate. -/
namespace LinearDistancePreservers.LatticeProduct
open SimpleGraph Finset DirectionGraph DirectionObstacle
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

/-- The lattice-hull theorem supplies exactly the rigidity condition
used by the native unweighted shortest-path proof. -/
theorem directions {d B x : ℕ}
    (hx : x ≤ (LatticeHull.vertices (LatticeHull.ball d B)).card) :
    ∃ v : Fin x → Fin d → ℕ,
      Function.Injective v ∧ (∀ a i, v a i < 2*B+1) ∧ AverageRigid v :=
  LatticeHull.exists_directions hx

/-- Exact-size, exact-terminal graph construction in every dimension.
The lattice vertex count is the sole geometric capacity inequality. -/
theorem lower_bound_of_roth {d B x n M k R N T : ℕ} [NeZero n] [NeZero M]
    (hx : x ≤ (LatticeHull.vertices (LatticeHull.ball d B)).card)
    (hn : (k+1)*(2*B+1) ≤ n) (hM : 3*R ≤ M)
    (hcap : n^d*x ≤ rothNumberNat R)
    (hN : 2*M+M*(k+1)*n^d ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^d*x*(k+2) := by
  classical
  obtain ⟨v,hinj,hvr,hc⟩ := directions hx
  obtain ⟨G,S,hS,hG,hE⟩ := BehrendProduct.exists_product (n := n) (M := M) (k := k)
    v hinj hvr hn hc hM (by simpa using hcap)
  have hv : Fintype.card (ProductVertex (Fin d) Unit n M k) ≤ N := by
    simpa [ProductVertex,ObstacleProduct.Vertex,DirectionGraph.Vertex,ZMod.card,
      mul_assoc,two_mul,add_assoc,add_left_comm,add_comm] using hN
  have hST : S.card ≤ T := hS.le.trans hT
  obtain ⟨K,S',hS',hK,hE'⟩ := UnweightedPadding.pad G S hG hv hST hTN
  refine ⟨K,S',hS',?_⟩
  intro H hH hp
  have heq : H = K := hK H hH hp
  subst H
  simp only [Fintype.card_fin] at hE
  simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE hE' ⊢
  exact hE'.trans hE

/-- The same graph theorem with the explicit quantitative Behrend bound. -/
theorem lower_bound {d B x n M k R N T : ℕ} [NeZero n] [NeZero M]
    (hx : x ≤ (LatticeHull.vertices (LatticeHull.ball d B)).card)
    (hn : (k+1)*(2*B+1) ≤ n) (hM : 3*R ≤ M)
    (hcap : ((n^d*x : ℕ) : ℝ) ≤ (R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R)))
    (hN : 2*M+M*(k+1)*n^d ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^d*x*(k+2) := by
  apply lower_bound_of_roth hx hn hM _ hN hT hTN
  exact_mod_cast hcap.trans Behrend.roth_lower_bound

end LinearDistancePreservers.LatticeProduct
