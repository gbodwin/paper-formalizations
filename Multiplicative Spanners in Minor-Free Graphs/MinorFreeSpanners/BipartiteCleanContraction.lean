import MinorFreeSpanners.BipartiteCleaningScales

/-! A genuine induced-dense-or-clean-covering-minor theorem on one explicit
inverse-quadratic threshold domain. Initial-family construction and the full
paper density increment are separate joins. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem exists_bipartite_dense_induced_or_small_loss_contraction
    (G : SimpleGraph V) (A B C : Finset V) (ell D : ℕ)
    (k d : ℝ) (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k)
    (hd : k ≤ d) (hD : (D:ℝ) ≤ 5*k^2*d)
    (hUnmated : Unmated G (5*k^2) (1/(100*k)) (1/(100*k^2)) d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hCB : C ⊆ B)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G (d/(100*k^2)) (insert b (L b : Set V)))
    (hsmall : ∀ x ∈ C ∪ C.biUnion L, G.degree x ≤ D) :
    (∃ H : Finset V, (H.card:ℝ) ≤ 10*k^3*d ∧
      (d/(100*k))^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ) ∧
      d/(400000*k^5)*(H.card:ℝ) ≤ ((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G (d/(100*k^2)) (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∃ model : MinorModel (fullStarContraction G C M) G,
        model.IsBounded (ell+1) ∧
        (∀ i, MateFreeOn G (d/(100*k^2)) (model.branch i)) ∧
        (∀ x, ∃ i, x ∈ model.branch i) ∧
        Fintype.card (StarContractionVertex C M)+ell*C.card=Fintype.card V ∧
        (G.edgeFinset.card:ℝ) ≤ (fullStarContraction G C M).edgeFinset.card+
          (2*ell*d/k)*C.card) := by
  have hd0 : 0 ≤ d := hk.le.trans hd
  have hq : 0 ≤ (1/(100*k^2))*d := by positivity
  have hqeq : (1/(100*k^2))*d=d/(100*k^2) := by ring
  have hr : 4*(ell:ℝ)*((1/(100*k^2))*d) ≤ d/(100*k) := by
    rw [hqeq]
    exact bipartite_cleaning_scale_threshold k ell d hk hellk hd0
  have hfree' : ∀ b ∈ C, MateFreeOn G ((1/(100*k^2))*d) (insert b (L b:Set V)) := by
    simpa only [hqeq] using hfree
  obtain hs | ⟨M,hM,hMf,hMn,hcov,model,hwidth,hmates,hcover,hcount,hedges⟩ :=
    exists_dense_induced_or_clean_star_contraction G A B C ell D (5*k^2)
      (1/(100*k)) (1/(100*k^2)) d (d/(100*k)) hq hr hD hUnmated
      L hG hCB hL hfull hfree' hsmall
  · obtain ⟨H,hn,he⟩ := hs
    have hnR : (H.card:ℝ) ≤ 2*((ell:ℝ)+1)*D := by exact_mod_cast hn
    have he' : (1:ℝ) ≤ ell := by exact_mod_cast hell
    have hb := bipartite_cleaning_dense_scale k ell d D H.card (G.induce (H:Set V)).edgeFinset.card
      hk he' hellk hd0 (Nat.cast_nonneg _) hD hnR he
    exact Or.inl ⟨H,hb.1,he,hb.2⟩
  · right
    refine ⟨M,hM,hMf,?_,hcov,model,hwidth,?_,hcover,hcount,?_⟩
    · simpa only [hqeq] using hMn
    · simpa only [hqeq] using hmates
    · have hcoef := bipartite_cleaning_scale_nat_loss k d ell hk hell hellk hd
      have hm := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg C.card)
      linarith

end MinorFreeSpanners
