import MinorFreeSpanners.MateFreeStarSelection
import MinorFreeSpanners.FullStarContraction

/-! Actual end-to-end mate-free star contraction on the full original host.
The necessary small-left domain is explicit; cleaning and edge-loss estimates
are later results, not endpoint hypotheses. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Internal finite selection yields an actual full covering bounded minor
with mate-free branches, exact vertex loss and the boundary budget. -/
theorem unmated_small_left_full_star_contraction (G : SimpleGraph V) (A B : Finset V)
    (ell d : ℕ) (K eps1 eps2 : ℝ)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hd : 0 < d)
    (he1 : 0 ≤ eps1) (he1' : eps1 < 1) (he2 : 0 < eps2)
    (hsize : ell*B.card ≤ A.card)
    (hsmall : ∀ x ∈ A, (G.degree x:ℝ) ≤ K*d)
    (hunmated : Unmated G K eps1 eps2 d)
    (hB : ∀ x ∈ A, d ≤ (B.filter fun b => G.Adj x b).card) :
    ∃ C : Finset V, ∃ L : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell L ∧
      (∀ b ∈ C, (L b).card = ell) ∧
      (∀ w ∈ C.biUnion L,
        (((B \ C).filter fun b => G.Adj w b).card:ℝ) ≤ eps1*d) ∧
      (A.Nonempty → C.Nonempty) ∧
      ∃ M : MinorModel (fullStarContraction G C L) G,
        M.IsBounded (ell+1) ∧
        (∀ i, MateFreeOn G (eps2*d) (M.branch i)) ∧
        (∀ x, ∃ i, x ∈ M.branch i) ∧
        Fintype.card (StarContractionVertex C L) + ell*C.card = Fintype.card V := by
  classical
  obtain ⟨C,L,hCB,hL,hfull,hfree,hboundary,hne⟩ :=
    unmated_small_left_star_selection G A B ell d K eps1 eps2 hG hd he1 he1' he2
      hsize hsmall hunmated hB
  have hAB : Disjoint A B := Finset.disjoint_coe.mp hG.disjoint
  have hAC : Disjoint A C := hAB.mono_right hCB
  refine ⟨C,L,hCB,hL,hfull,hboundary,hne,hL.fullMinorModel hAC,
    hL.fullMinorModel_bounded hAC,hL.fullMinorModel_mateFree hAC hfree,?_,
    hL.fullContraction_card hAC hfull⟩
  intro x
  exact fullStarBranch_cover C L x

end MinorFreeSpanners
