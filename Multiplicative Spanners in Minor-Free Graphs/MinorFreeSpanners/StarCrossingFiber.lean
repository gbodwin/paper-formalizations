import MinorFreeSpanners.FullStarEdgeAccounting
import MinorFreeSpanners.StarCrossingPairs

/-! Identify each actual selected-star quotient edge fiber with the literal
crossing host-edge set. This links local orientation counts to the exact
full-contraction loss identity. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Actual host-edge fibers between distinct selected star labels are
exactly their actual crossing edges, in both orientations. -/
theorem IsStarPacking.selected_edge_fiber {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (b c : C) (hbc : b ≠ c) :
    ((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e = s(Sum.inl b,Sum.inl c)) =
      starBetweenEdges G L b.val c.val := by
  classical
  have hlabels : (Sum.inl b : StarContractionVertex C L) ≠ Sum.inl c := by
    intro he
    exact hbc (Sum.inl.inj he)
  ext e
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hp : (G.Adj x y ∧ fullStarLabel C L x ≠ fullStarLabel C L y) ∧
          s(fullStarLabel C L x,fullStarLabel C L y) = s(Sum.inl b,Sum.inl c) := by
        simpa [quotientCrossEdges] using he
      rcases Sym2.eq_iff.mp hp.2 with ⟨hx,hy⟩|⟨hx,hy⟩
      · have hxb := (h.fullStarLabel_eq_iff hAC x (.inl b)).mp hx
        have hyc := (h.fullStarLabel_eq_iff hAC y (.inl c)).mp hy
        exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨by simpa only [fullStarBranch] using hxb,by simpa only [fullStarBranch] using hyc⟩,hp.1.1⟩,rfl⟩
      · have hxc := (h.fullStarLabel_eq_iff hAC x (.inl c)).mp hx
        have hyb := (h.fullStarLabel_eq_iff hAC y (.inl b)).mp hy
        exact Finset.mem_image.mpr ⟨(y,x),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨by simpa only [fullStarBranch] using hyb,by simpa only [fullStarBranch] using hxc⟩,hp.1.1.symm⟩,Sym2.eq_swap⟩
  · intro he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have hxb := (h.fullStarLabel_eq_iff hAC x (.inl b)).mpr (by simpa only [fullStarBranch] using hx)
    have hyc := (h.fullStarLabel_eq_iff hAC y (.inl c)).mpr (by simpa only [fullStarBranch] using hy)
    have hn : fullStarLabel C L x ≠ fullStarLabel C L y := by
      rw [hxb,hyc]
      exact hlabels
    simpa [quotientCrossEdges,hxb,hyc] using And.intro (And.intro he hn)
      (show s(fullStarLabel C L x,fullStarLabel C L y)=s(Sum.inl b,Sum.inl c) by rw [hxb,hyc])

/-- The exact fiber cardinality is the sum of the two actual crossing-leaf
counts. Bipartiteness is checked on the original host. -/
theorem IsStarPacking.selected_edge_fiber_card {G : SimpleGraph V} {A B C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (b c : C) (hbc : b ≠ c) :
    (((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e = s(Sum.inl b,Sum.inl c)).card) =
      (starCrossLeaves G L b.val c.val).card +
      (starCrossLeaves G L c.val b.val).card := by
  classical
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  rw [h.selected_edge_fiber hAC b c hbc]
  exact starBetweenEdges_card G A B L b.val c.val hG (hCB b.property) (hCB c.property)
    (fun he => hbc (Subtype.ext he)) (h.2.1 b.val) (h.2.1 c.val)

end MinorFreeSpanners
