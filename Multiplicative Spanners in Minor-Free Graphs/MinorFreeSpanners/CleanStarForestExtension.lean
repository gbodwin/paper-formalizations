import MinorFreeSpanners.CleanStarForestAdjoin

/-! A new clean star is constructed in the residual set of an existing actual
family. Every original star is protected, and the literal enlarged canonical
quotient retains the complete proved edge-loss budget. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No protected-growth or extension certificate is supplied: the new star,
its old-branch invariant and its canonical full quotient are constructed. -/
theorem extend_clean_forest_or_dense (G : SimpleGraph V)
    (k : ℕ) (C T : Finset V) (L : V → Finset V) (c : V)
    (K eps1 eps2 d : ℝ)
    (h : SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L)
    (hcR : c ∈ starResidual C L) (hTR : T ⊆ starResidual C L)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT : 2*eps1*d ≤ (T.card:ℝ)) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    ∃ L' : V → Finset V, SmallCleanStarForest G k (K*d) (4*(eps2*d)) (insert c C) L' ∧
      (∀ b ∈ C, L' b=L b) ∧ (insert c C).card=C.card+1 := by
  classical
  let F := fullStarContraction G C L
  let M := h.1.fullMinorModel
  let i : StarContractionVertex C L := .inr ⟨c,hcR⟩
  let s0 := CleanStarState.initial (c:=c) (T:=T) F M
    h.1.fullMinorModel_covers h.1.fullMinorModel_full (h.1.fullMinorModel_bounded hk) i (by simp [M,i,IsGeneralStarForest.fullMinorModel,fullStarBranch])
    (fun x hx => ⟨.inr ⟨x,hTR hx⟩,by simp [M,IsGeneralStarForest.fullMinorModel,fullStarBranch]⟩) (eps2*d)
  have hold : CleanStarState.OldBranchInvariant M s0 := fun j _ => ⟨j,rfl⟩
  obtain hDense | ⟨s,hs⟩ := clean_star_grow_preserving_or_dense G F M k c T K eps1 eps2 d
    (Fintype.card (StarContractionVertex C L)) F.edgeFinset.card s0 hold
    hk hK hd he1 he1' he2 hq hkd hT hadj hsmall
  · exact Or.inl hDense
  · exact Or.inr (s.adjoin_clean_forest h hcR hTR hs (by linarith) hadj hsmall)

end MinorFreeSpanners
