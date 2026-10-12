import MinorFreeSpanners.UnitTreeGraphBudget
import MinorFreeSpanners.CanonicalScaleChoice

/-! A fully constructed unit-tree weight bound at the corrected greedy girth
threshold, with the literal scale determined by the requested slack. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem corrected_unit_tree_lightness {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r h : ℕ) (hr : 1≤r) (hh : 0<h)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h)
    (hG : WeightedGirthAbove G w ((1+eps)*(2*(r:ℝ)-1)+1))
    (hw : ∀ e∈G.edgeSet,0≤w e) :
    (∑ e∈G.edgeFinset,w e)≤
      (42*(Nat.log 2 (canonicalScale eps)+1:ℕ)+1)*
        canonicalPhaseCredit (canonicalScale eps) r h*(T.edgeFinset.card:ℝ) := by
  have hg : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(canonicalScale eps:ℝ))) := by
    intro a p hp e he
    exact (mul_le_mul_of_nonneg_right (canonicalScale_corrected_girth eps heps heps1 r hr)
      (hw e (p.edges_subset_edgeSet he))).trans_lt (hG a p hp e he)
  exact unit_tree_graph_budget (canonicalScale eps) r h
    (canonicalScale_bounds eps heps heps1).1 hr hh hT hTree hunit hfree hg hw

end MinorFreeSpanners
