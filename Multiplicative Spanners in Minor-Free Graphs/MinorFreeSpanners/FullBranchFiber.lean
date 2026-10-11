import MinorFreeSpanners.StarCrossingFiber

/-! Exact edge fibers between arbitrary actual branches of the covering
star quotient, including residual singleton vertices. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def branchBetweenEdges (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (i j : StarContractionVertex C L) : Finset (Sym2 V) :=
  (((fullStarBranch C L i).product (fullStarBranch C L j)).filter
    fun p => G.Adj p.1 p.2).image fun p => s(p.1,p.2)

/-- This uses the actual covering branch labels and real host edges. -/
theorem IsStarPacking.branch_edge_fiber {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (i j : StarContractionVertex C L) (hij : i ≠ j) :
    ((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e = s(i,j)) =
      branchBetweenEdges G C L i j := by
  classical
  ext e
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hp : (G.Adj x y ∧ fullStarLabel C L x ≠ fullStarLabel C L y) ∧
          s(fullStarLabel C L x,fullStarLabel C L y) = s(i,j) := by
        simpa [quotientCrossEdges] using he
      rcases Sym2.eq_iff.mp hp.2 with ⟨hx,hy⟩|⟨hx,hy⟩
      · have hxb := (h.fullStarLabel_eq_iff hAC x i).mp hx
        have hyc := (h.fullStarLabel_eq_iff hAC y j).mp hy
        exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hxb,hyc⟩,hp.1.1⟩,rfl⟩
      · have hxc := (h.fullStarLabel_eq_iff hAC x j).mp hx
        have hyb := (h.fullStarLabel_eq_iff hAC y i).mp hy
        exact Finset.mem_image.mpr ⟨(y,x),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hyb,hxc⟩,hp.1.1.symm⟩,Sym2.eq_swap⟩
  · intro he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have hxb := (h.fullStarLabel_eq_iff hAC x i).mpr hx
    have hyc := (h.fullStarLabel_eq_iff hAC y j).mpr hy
    have hn : fullStarLabel C L x ≠ fullStarLabel C L y := by
      rw [hxb,hyc]
      exact hij
    simpa [quotientCrossEdges,hxb,hyc] using And.intro (And.intro he hn)
      (show s(fullStarLabel C L x,fullStarLabel C L y)=s(i,j) by rw [hxb,hyc])

end MinorFreeSpanners
