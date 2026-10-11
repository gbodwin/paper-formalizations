import MinorFreeSpanners.FullStarEdgeBudget
import MinorFreeSpanners.DenseOrBadPairBudget

/-! A genuine small induced witness or an actual bounded covering minor
with a proved quantitative edge-loss budget. The admissible star family
and all degree/threshold premises remain explicit. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- No cleaning or contraction-loss oracle is assumed: the finite minimum,
all residual fibers and the actual minor model are constructed. -/
theorem exists_dense_induced_or_clean_star_contraction
    (G : SimpleGraph V) (A B C : Finset V) (ell D : ℕ)
    (K eps1 eps2 d r : ℝ) (hq : 0 ≤ eps2*d) (hr : 4*ell*(eps2*d) ≤ r)
    (hD : (D:ℝ) ≤ K*d) (hUnmated : Unmated G K eps1 eps2 d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hCB : C ⊆ B)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G (eps2*d) (insert b (L b : Set V)))
    (hsmall : ∀ x ∈ C ∪ C.biUnion L, G.degree x ≤ D) :
    (∃ H : Finset V, H.card ≤ 2*(ell+1)*D ∧
      r^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G (eps2*d) (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∃ model : MinorModel (fullStarContraction G C M) G,
        model.IsBounded (ell+1) ∧
        (∀ i, MateFreeOn G (eps2*d) (model.branch i)) ∧
        (∀ x, ∃ i, x ∈ model.branch i) ∧
        Fintype.card (StarContractionVertex C M)+ell*C.card=Fintype.card V ∧
        (G.edgeFinset.card:ℝ) ≤ (fullStarContraction G C M).edgeFinset.card+
          ((ell:ℝ)+4*((ell*(ell-1):ℕ):ℝ)*(eps2*d)+
            (ell+1)*eps1*d+ell*r)*C.card) := by
  classical
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  obtain hd | ⟨M,hM,hMf,hMn,hcov,hscore,_⟩ :=
    exists_dense_induced_or_bad_pair_budget G A B C ell D K eps1 eps2 d r hq hr
      hD hUnmated L hG hAC hL hfull hfree hsmall
  · exact Or.inl hd
  right
  have hleaffree : ∀ b ∈ C, MateFreeOn G (eps2*d) (M b:Set V) := by
    intro b hb x hx y hy hxy
    exact hMn b hb x (Set.mem_insert_of_mem b hx) y (Set.mem_insert_of_mem b hy) hxy
  have he := hM.fullContraction_edges_ge_mateFree_budget hG hCB (eps2*d) hMf hleaffree
  refine ⟨M,hM,hMf,hMn,hcov,hM.fullMinorModel hAC,hM.fullMinorModel_bounded hAC,
    hM.fullMinorModel_mateFree hAC hMn,?_,hM.fullContraction_card hAC hMf,?_⟩
  · intro x
    exact fullStarBranch_cover C M x
  · nlinarith

end MinorFreeSpanners
