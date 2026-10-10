import MinorFreeSpanners.MateFreeStarContraction
import MinorFreeSpanners.PostleBipartiteTrim
import MinorFreeSpanners.PostleSubgraphUnmated

/-! Construct the small-left domain by real edge deletion, then reapply the
small-dense alternative to that graph. No hereditary unmatedness is assumed.
The mate-free assertion concerns the constructed regular subgraph, while the
bounded minor is also a genuine minor of the original host. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual bipartite minimum-degree input yields either a small dense
induced host subgraph or a full covering star contraction of an internally
constructed left-regular subgraph. This is the selection stage only: there
is no cleaning or edge-loss conclusion. -/
theorem regularize_dense_or_mate_free_stars (G : SimpleGraph V) (A B : Finset V)
    (ell d : ℕ) (K eps1 eps2 : ℝ)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hd : 0 < d) (hK : 1 ≤ K)
    (he1 : 0 ≤ eps1) (he1' : eps1 < 1) (he2 : 0 < eps2)
    (hsize : ell*B.card ≤ A.card) (hdegree : ∀ x ∈ A, d ≤ G.degree x) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*K*d ∧
      eps1*eps2*(d:ℝ)^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartiteWith (A:Set V) (B:Set V) ∧
      (∀ x ∈ A, H.degree x = d) ∧ H.edgeFinset.card = d*A.card ∧
      ∃ C : Finset V, ∃ L : V → Finset V,
        C ⊆ B ∧ IsStarPacking H A C ell L ∧
        (∀ b ∈ C, (L b).card = ell) ∧
        (∀ w ∈ C.biUnion L,
          (((B \ C).filter fun b => H.Adj w b).card:ℝ) ≤ eps1*d) ∧
        (A.Nonempty → C.Nonempty) ∧
        ∃ M : MinorModel (fullStarContraction H C L) G,
          M.IsBounded (ell+1) ∧
          (∀ i, MateFreeOn H (eps2*d) (M.branch i)) ∧
          (∀ x, ∃ i, x ∈ M.branch i) ∧
          Fintype.card (StarContractionVertex C L) + ell*C.card = Fintype.card V := by
  classical
  obtain ⟨H,hHG,hH,hreg,hcard⟩ := exists_left_regular_subgraph G A B hG d hdegree
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  rcases postle_subgraph_dense_or_unmated G H hHG K d eps1 eps2 hK hdR
    he1 he1'.le he2.le with h | hu
  · exact Or.inl h
  have hsmall : ∀ x ∈ A, (H.degree x:ℝ) ≤ K*d := by
    intro x hx
    rw [hreg x hx]
    nlinarith
  have hB : ∀ x ∈ A, d ≤ (B.filter fun b => H.Adj x b).card := by
    intro x hx
    have he : B.filter (fun b => H.Adj x b) = H.neighborFinset x := by
      ext b
      simp only [Finset.mem_filter,mem_neighborFinset]
      exact ⟨And.right,fun he => ⟨hH.mem_of_mem_adj hx he,he⟩⟩
    rw [he,card_neighborFinset_eq_degree,hreg x hx]
  obtain ⟨C,L,hCB,hL,hfull,hbound,hne,M,hM,hfree,hcover,hcount⟩ :=
    unmated_small_left_full_star_contraction H A B ell d K eps1 eps2 hH hd
      he1 he1' he2 hsize hsmall hu hB
  exact Or.inr ⟨H,hHG,hH,hreg,hcard,C,L,hCB,hL,hfull,hbound,hne,
    M.mapSupergraph hHG,hM,hfree,hcover,hcount⟩

end MinorFreeSpanners
