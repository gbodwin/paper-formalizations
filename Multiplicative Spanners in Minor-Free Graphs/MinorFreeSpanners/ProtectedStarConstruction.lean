import MinorFreeSpanners.ProtectedStarGrowth

/-! The finite clean-star iteration retains exact initial branches at every
step. The actual bounded-minor alternative supplies each mate bound. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
universe u

/-- An actual initial singleton state grows to k vertices. The only
alternative is an actual small dense induced subgraph in the original host. -/
theorem clean_star_grow_preserving_or_dense {I0 V : Type u} [Fintype V]
    (G : SimpleGraph V) (F0 : SimpleGraph I0) (M0 : MinorModel F0 G) (k : ℕ) (c : V) (T : Finset V)
    (K eps1 eps2 d : ℝ) (N E : ℕ)
    (s0 : CleanStarState G k c T (eps2*d) N E 1)
    (hold : CleanStarState.OldBranchInvariant M0 s0)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT : 2*eps1*d ≤ (T.card:ℝ)) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      ∃ s : CleanStarState G k c T (eps2*d) N E k, CleanStarState.OldBranchInvariant M0 s := by
  classical
  by_cases hDense : ∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)
  · exact Or.inl hDense
  have hKk : (1:ℝ) ≤ K*k := by
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hun : ∀ r, ∀ s : CleanStarState G k c T (eps2*d) N E r,
      Unmated s.graph (K*k) eps1 eps2 d := by
    intro r s
    exact (postle_bounded_minor_dense_or_unmated s.graph G s.model k s.bounded
      (K*k) d eps1 eps2 hKk hd he1 he1' he2).resolve_left hDense
  have grow : ∀ t : ℕ, t+1 ≤ k →
      ∃ s : CleanStarState G k c T (eps2*d) N E (t+1), CleanStarState.OldBranchInvariant M0 s := by
    intro t
    induction t with
    | zero => intro _; exact ⟨s0,hold⟩
    | succ t ih =>
      intro ht
      obtain ⟨s,hs⟩ := ih (by omega)
      exact s.step_preserving M0 hs (by omega) (by linarith) (by linarith) hq hkd hT hadj hsmall (hun _ s)
  have hh := grow (k-1) (by omega)
  rw [Nat.sub_add_cancel hk] at hh
  exact Or.inr hh


end MinorFreeSpanners
