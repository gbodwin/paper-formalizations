import MinorFreeSpanners.ResidualBipartiteSelection

/-! Internally construct the maximum clean star family and derive either a
small dense witness, an actual unbalanced bipartite subgraph, or coverage of
all but at most half the original vertices by stars and large vertices.
This is the coverage stage; the final minor-density ratio is not asserted. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every family and local maximality consequence used by this alternative
is constructed inside the theorem. The graph has the stated original minimum
degree and original edge-density upper bound; deriving a densest induced
input satisfying both is a separate subsequent reduction. -/
theorem general_clean_coverage_alternative (G : SimpleGraph V) (k ell : ℕ)
    (K eps1 eps2 d : ℝ) (hk : 8 ≤ k) (hell : 4*ell ≤ k)
    (hK : 4*(k:ℝ)^2 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hmin : ∀ x, d ≤ (G.degree x:ℝ))
    (hE : (G.edgeFinset.card:ℝ) ≤ d*(Fintype.card V:ℝ)) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ X Y : Finset V, ∃ H : SimpleGraph V, H ≤ G ∧
      H.IsBipartiteWith (X:Set V) (Y:Set V) ∧ X.Nonempty ∧ ell*Y.card ≤ X.card ∧
      ∀ x ∈ X, d-(2+3*(k:ℝ))*eps1*d ≤ (H.degree x:ℝ)) ∨
    ∃ C : Finset V, ∃ L : V → Finset V,
      SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L ∧
      2*(smallResidualVertices G C L (K*d)).card ≤ Fintype.card V := by
  classical
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : 1 ≤ K := by nlinarith
  have hp : 0 < eps1*d := by linarith
  obtain hDense | ⟨C,L,h,_hm,hr,hb⟩ :=
    dense_or_maximum_clean_forest_local_bounds G k K eps1 eps2 d
      (by omega) hK1 hd he1 he1' he2 hq hkd
  · exact Or.inl hDense
  by_cases hsmall : 2*(smallResidualVertices G C L (K*d)).card ≤ Fintype.card V
  · exact Or.inr (Or.inr ⟨C,L,h,hsmall⟩)
  have hres : ∀ x ∈ smallResidualVertices G C L (K*d),
      ((smallResidualNeighbors G C L (K*d) x).card:ℝ) ≤ 2*eps1*d := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact (hr x hx'.1 hx'.2).le
  exact Or.inr (Or.inl (residual_bipartite_of_large_residual G k ell C L K eps1 d
    hk hell (by linarith) hp hK hE h.1 (fun x _ => hmin x) hres hb (lt_of_not_ge hsmall)))

end MinorFreeSpanners
