import MinorFreeSpanners.CleanStarForestExtension

/-! Maximality now has an actual graph consequence: too many small residual
neighbors would create a new protected clean star and strictly increase the
internally selected family. All neighborhoods refer to original host edges. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Original-host neighbors that are residual and have the required original
small-degree bound. Neither adjacency nor degree is taken in a deleted graph. -/
noncomputable def smallResidualNeighbors (G : SimpleGraph V) (C : Finset V) (L : V → Finset V)
    (D : ℝ) (c : V) : Finset V :=
  (starResidual C L).filter (fun x => G.Adj c x ∧ (G.degree x:ℝ) ≤ D)

theorem maximum_clean_forest_residual_bound (G : SimpleGraph V)
    (k : ℕ) (C : Finset V) (L : V → Finset V) (K eps1 eps2 d : ℝ)
    (h : SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L)
    (hmax : ∀ C' L', SmallCleanStarForest G k (K*d) (4*(eps2*d)) C' L' → C'.card ≤ C.card)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hDense : ¬∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) :
    ∀ c ∈ starResidual C L, (G.degree c:ℝ) ≤ K*d →
      ((smallResidualNeighbors G C L (K*d) c).card:ℝ) < 2*eps1*d := by
  intro c hc hdeg
  by_contra hlt
  have hT : 2*eps1*d ≤ ((smallResidualNeighbors G C L (K*d) c).card:ℝ) := le_of_not_gt hlt
  let T := smallResidualNeighbors G C L (K*d) c
  have hTR : T ⊆ starResidual C L := fun x hx => (Finset.mem_filter.mp hx).1
  have hadj : ∀ x ∈ T, G.Adj c x := fun x hx => (Finset.mem_filter.mp hx).2.1
  have hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d := by
    intro x hx
    rcases hx with hx | hx
    · have he : x=c := hx
      subst x
      exact hdeg
    · exact (Finset.mem_filter.mp hx).2.2
  have hh := extend_clean_forest_or_dense G k C T L c K eps1 eps2 d h hc hTR
    hk hK hd he1 he1' he2 hq hkd hT hadj hsmall
  obtain ⟨L',h',_,hcard⟩ := hh.resolve_left hDense
  have hle := hmax (insert c C) L' h'
  omega

/-- The finite maximum is selected internally, and its residual neighborhood
bound follows from the constructed augmentation, not a maximality oracle. -/
theorem dense_or_maximum_clean_forest_residual (G : SimpleGraph V)
    (k : ℕ) (K eps1 eps2 d : ℝ)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    ∃ C : Finset V, ∃ L : V → Finset V,
      SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L ∧
      (∀ C' L', SmallCleanStarForest G k (K*d) (4*(eps2*d)) C' L' → C'.card ≤ C.card) ∧
      ∀ c ∈ starResidual C L, (G.degree c:ℝ) ≤ K*d →
        ((smallResidualNeighbors G C L (K*d) c).card:ℝ) < 2*eps1*d := by
  classical
  by_cases hDense : ∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)
  · exact Or.inl hDense
  obtain ⟨C,L,h,hmax⟩ := exists_maximum_small_clean_star_forest G k (K*d) (4*(eps2*d))
  exact Or.inr ⟨C,L,h,hmax,maximum_clean_forest_residual_bound G k C L K eps1 eps2 d
    h hmax hk hK hd he1 he1' he2 hq hkd hDense⟩

end MinorFreeSpanners
