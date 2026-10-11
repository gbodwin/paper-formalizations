import MinorFreeSpanners.TwoStarReplacement
import MinorFreeSpanners.MaximumForestResidual

/-! A maximum clean family has at most one vertex in any old star with many
original small residual neighbors. Two such vertices would replace their
old star by two actual protected stars with the complete clean loss budget. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def largeResidualStarVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) (b : V) : Finset V :=
  (insert b (L b)).filter (fun x => threshold ≤ (smallResidualNeighbors G C L D x).card)

theorem maximum_clean_forest_branch_bound (G : SimpleGraph V)
    (k : ℕ) (C : Finset V) (L : V → Finset V) (K eps1 eps2 d : ℝ)
    (h : SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L)
    (hmax : ∀ C' L', SmallCleanStarForest G k (K*d) (4*(eps2*d)) C' L' → C'.card ≤ C.card)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hDense : ¬∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) :
    ∀ b ∈ C, (largeResidualStarVertices G C L (K*d) (3*eps1*d) b).card ≤ 1 := by
  intro b hb
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra huv
  have hu' := Finset.mem_filter.mp hu
  have hv' := Finset.mem_filter.mp hv
  let T1 := smallResidualNeighbors G C L (K*d) u
  let T2 := smallResidualNeighbors G C L (K*d) v
  have hnon : 0 ≤ eps1*d := mul_nonneg he1 (by linarith)
  have hT1 : 2*eps1*d ≤ (T1.card:ℝ) := by
    have hh := hu'.2
    change 3*eps1*d ≤ (T1.card:ℝ) at hh
    linarith
  have hT2 : 3*eps1*d ≤ (T2.card:ℝ) := hv'.2
  obtain ⟨L',h',_,hc⟩ := replace_one_star_by_two G k C T1 T2 L b u v K eps1 eps2 d h
    hb hu'.1 hv'.1 huv
    (fun _ hx => (Finset.mem_filter.mp hx).1)
    (fun _ hx => (Finset.mem_filter.mp hx).1)
    hk hK hd he1 he1' he2 hq hkd hT1 hT2
    (fun _ hx => (Finset.mem_filter.mp hx).2.1)
    (fun _ hx => (Finset.mem_filter.mp hx).2.1)
    (fun _ hx => (Finset.mem_filter.mp hx).2.2)
    (fun _ hx => (Finset.mem_filter.mp hx).2.2) hDense
  have hh := hmax _ L' h'
  omega

/-- Both local maximality consequences hold for one internally selected
actual family. No family, augmentation oracle or replacement certificate is
supplied by the caller. Quantitative global coverage is a subsequent step. -/
theorem dense_or_maximum_clean_forest_local_bounds (G : SimpleGraph V)
    (k : ℕ) (K eps1 eps2 d : ℝ)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    ∃ C : Finset V, ∃ L : V → Finset V,
      SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L ∧
      (∀ C' L', SmallCleanStarForest G k (K*d) (4*(eps2*d)) C' L' → C'.card ≤ C.card) ∧
      (∀ c ∈ starResidual C L, (G.degree c:ℝ) ≤ K*d →
        ((smallResidualNeighbors G C L (K*d) c).card:ℝ) < 2*eps1*d) ∧
      ∀ b ∈ C, (largeResidualStarVertices G C L (K*d) (3*eps1*d) b).card ≤ 1 := by
  classical
  by_cases hDense : ∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)
  · exact Or.inl hDense
  obtain ⟨C,L,h,hm,hr⟩ :=
    (dense_or_maximum_clean_forest_residual G k K eps1 eps2 d hk hK hd he1 he1' he2 hq hkd).resolve_left hDense
  exact Or.inr ⟨C,L,h,hm,hr,maximum_clean_forest_branch_bound G k C L K eps1 eps2 d
    h hm hk hK hd he1 he1' he2 hq hkd hDense⟩

end MinorFreeSpanners
