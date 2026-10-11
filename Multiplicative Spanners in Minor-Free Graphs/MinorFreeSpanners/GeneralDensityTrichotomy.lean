import MinorFreeSpanners.ResidualMinorDensity
import MinorFreeSpanners.GeneralCleanCoverageAlternative
import MinorFreeSpanners.FiniteBoundedMinor

/-! Actual general-graph density trichotomy on an explicit densest-core
domain. The maximum star family, local bounds and retained minor are all
constructed, rather than supplied as a cleaning or coverage certificate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dense original witness, actual unbalanced bipartite subgraph, or a
positive k-bounded minor of density at least (k-7)d. -/
theorem general_density_trichotomy (G : SimpleGraph V) (k ell : ℕ)
    (K eps1 eps2 d : ℝ) (hk : 8 ≤ k) (hell : 4*ell ≤ k)
    (hn : 0 < Fintype.card V) (hK : 4*(k:ℝ)^2 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hcoef : (3*eps1+4*eps2)*(k:ℝ) ≤ 5)
    (hmin : ∀ x, d ≤ (G.degree x:ℝ))
    (hE : (G.edgeFinset.card:ℝ)=d*(Fintype.card V:ℝ))
    (hglobal : ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ)) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ X Y : Finset V, ∃ H : SimpleGraph V, H ≤ G ∧
      H.IsBipartiteWith (X:Set V) (Y:Set V) ∧ X.Nonempty ∧ ell*Y.card ≤ X.card ∧
      ∀ x∈X, d-(2+3*(k:ℝ))*eps1*d ≤ (H.degree x:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0<n ∧ M.IsBounded k ∧ ((k:ℝ)-7)*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : 1 ≤ K := by nlinarith
  have hp : 0 < eps1*d := by linarith
  obtain hDense | ⟨C,L,h,_hm,hr,hb⟩ :=
    dense_or_maximum_clean_forest_local_bounds G k K eps1 eps2 d
      (by omega) hK1 hd he1 he1' he2 hq hkd
  · exact Or.inl hDense
  by_cases hhalf : 2*(smallResidualVertices G C L (K*d)).card ≤ Fintype.card V
  · obtain ⟨M,hM,hpos,hD⟩ := clean_coverage_retained_minor_density G k C L K eps1 eps2 d
      hk hn (by linarith) he1 hK hcoef h hb hhalf hE.ge hglobal hE.le
    apply Or.inr
    apply Or.inr
    apply exists_finite_bounded_dense_minor _ G k (((k:ℝ)-7)*d) M hM
    · simpa only [← Set.toFinset_card,Finset.toFinset_coe] using hpos
    · simp only [← Set.toFinset_card,Finset.toFinset_coe]
      simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hD ⊢
      exact hD
  · have hres : ∀ x∈smallResidualVertices G C L (K*d),
        ((smallResidualNeighbors G C L (K*d) x).card:ℝ) ≤ 2*eps1*d := by
      intro x hx
      obtain ⟨hxR,hxD⟩ := Finset.mem_filter.mp hx
      exact (hr x hxR hxD).le
    exact Or.inr (Or.inl (residual_bipartite_of_large_residual G k ell C L K eps1 d
      hk hell (by linarith) hp hK hE.le h.1 (fun x _ => hmin x) hres hb (lt_of_not_ge hhalf)))

end MinorFreeSpanners
