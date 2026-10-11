import MinorFreeSpanners.CleanStarGrowth
import MinorFreeSpanners.PostlePullback

/-! Iterate actual low-loss singleton contractions to construct a full
size-k star branch, or return the genuine small dense host witness. Unmated
quotients are obtained from the proved bounded-minor alternative each time. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
universe u

/-- An actual initial singleton state grows to k vertices. The only
alternative is an actual small dense induced subgraph in the original host. -/
theorem clean_star_grow_or_dense {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (c : V) (T : Finset V)
    (K eps1 eps2 d : ℝ) (N E : ℕ)
    (s0 : CleanStarState G k c T (eps2*d) N E 1)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT : 2*eps1*d ≤ (T.card:ℝ)) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      Nonempty (CleanStarState G k c T (eps2*d) N E k) := by
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
      Nonempty (CleanStarState G k c T (eps2*d) N E (t+1)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨s0⟩
    | succ t ih =>
      intro ht
      obtain ⟨s⟩ := ih (by omega)
      exact s.step (by omega) (by linarith) (by linarith) hq hkd hT hadj hsmall (hun _ s)
  have hh := grow (k-1) (by omega)
  exact Or.inr (by simpa only [Nat.sub_add_cancel hk] using hh)

/-- Starting from the actual uncontracted graph constructs a size-k star
branch with all host vertices retained, and pays its complete actual simple
edge loss. No minor, growth step, mate-free certificate or target loss bound
is supplied by the caller. -/
theorem exists_clean_star_or_dense {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (c : V) (T : Finset V)
    (K eps1 eps2 d : ℝ)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT : 2*eps1*d ≤ (T.card:ℝ)) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      Nonempty (CleanStarState G k c T (eps2*d) (Fintype.card V) G.edgeFinset.card k) := by
  classical
  let M := MinorModel.identity G
  have hMk : M.IsBounded k := fun i => (MinorModel.identity_bounded G i).trans hk
  let s0 := CleanStarState.initial (T := T) (c := c) G M (MinorModel.identity_covers G)
    (MinorModel.identity_full G) hMk c rfl (fun x _ => ⟨x,rfl⟩) (eps2*d)
  exact clean_star_grow_or_dense G k c T K eps1 eps2 d (Fintype.card V) G.edgeFinset.card
    s0 hk hK hd he1 he1' he2 hq hkd hT hadj hsmall

end MinorFreeSpanners
