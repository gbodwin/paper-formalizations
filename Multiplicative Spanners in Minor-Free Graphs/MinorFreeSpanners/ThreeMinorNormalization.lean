import MinorFreeSpanners.TriangleMinor
import MinorFreeSpanners.MinorNormalization
import MinorFreeSpanners.ConnectedLowerBound

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
universe u
attribute [local instance] Classical.propDecidable

/-- A spanning tree inside a forest is the whole graph. -/
theorem tree_eq_forest {V : Type*} {G T : SimpleGraph V}
    (hT : T.IsTree) (hTG : T ≤ G) (hG : G.IsAcyclic) : T = G := by
  have hconn := hT.connected.mono hTG
  have hm := (hconn.maximal_le_isAcyclic_iff_isTree hTG).mpr hT
  exact le_antisymm hTG (hm.2 ⟨le_rfl,hG⟩ hTG)

/-- The h=3 normalization boundary: the input is already a tree, so unit
weights on the same graph give the desired result without subdivision. -/
theorem three_minor_unit_tree_reduction_of_mst {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ)
    (hn : 2 ≤ Fintype.card U) (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) (hminor : CliqueMinorFree G 3) :
    ∃ (X : Type u) (instX : Fintype X),
      MinorUnitTreeReductionResult X instX (2*Fintype.card U-1) g (lightness G T w/2) 3 := by
  classical
  have hacyclic := hminor.isAcyclic
  have heq := tree_eq_forest hT.2.1 hT.1 hacyclic
  subst T
  have hGtree := hT.2.1
  have hpos := tree_totalWeight_pos hGtree hn w hw
  have hunit : IsMinimumSpanningTree G G (fun _ => 1) := by
    refine ⟨le_rfl,hGtree,?_⟩
    intro S hSG hS
    rw [unit_tree_weight hGtree,unit_tree_weight hS]
  have hunitpos : 0 < totalWeight G (fun _ => 1) := by
    rw [unit_tree_weight hGtree]
    have hnR : (2:ℝ) ≤ Fintype.card U := by exact_mod_cast hn
    linarith
  refine ⟨U,inferInstance,G,G,(fun _ => 1),hminor,hunit,by simp,by simp,?_,by omega,?_⟩
  · intro a p hp
    exact (hacyclic p hp).elim
  · simp only [lightness,div_self hpos.ne',div_self hunitpos.ne']
    norm_num

/-- Full minor-preserving unit-MST normalization for every nontrivial clique
order h≥3, with the original quantitative vertex and lightness bounds. -/
theorem minor_unit_tree_reduction_of_mst_all_h {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ) (h : ℕ) (hh : 3 ≤ h)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hminor : CliqueMinorFree G h) :
    ∃ (X : Type u) (instX : Fintype X),
      MinorUnitTreeReductionResult X instX (2*Fintype.card U-1) g (lightness G T w/2) h := by
  by_cases hh4 : 4 ≤ h
  · exact minor_unit_tree_reduction_of_mst w g h hh4 hn hg hT hw hG hminor
  · have he : h = 3 := by omega
    subst h
    exact three_minor_unit_tree_reduction_of_mst w g hn hT hw hminor

end MinorFreeSpanners
