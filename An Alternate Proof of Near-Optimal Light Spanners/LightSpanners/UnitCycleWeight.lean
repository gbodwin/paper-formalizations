import LightSpanners.UnitCycle
import LightSpanners.Weight

namespace LightSpanners
open SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

namespace UnitSpanningCycle
variable {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)
include C

theorem tree_weight_lower {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) :
    (Fintype.card V : ℝ) - 1 ≤ totalWeight T w := by
  have h := card_mul_le_totalWeight T w 1 (fun e he => C.lower e (edgeSet_mono hTG he))
  have hcard : (T.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
    exact_mod_cast hT.card_edgeFinset
  nlinarith

theorem exists_unit_tree : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    totalWeight T w = (Fintype.card V : ℝ) - 1 := by
  let l := C.cycle.edges
  let H := edgeGraph l.toFinset
  have hl : ∀ e ∈ l, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (C.cycle.edges_subset_edgeSet he)
  have hHG : H ≤ G := by
    intro u v huv
    apply (mem_edgeSet G).mp
    exact C.cycle.edges_subset_edgeSet (List.mem_toFinset.mp
      ((mem_edgeGraph _ _).mp ((mem_edgeSet H).mpr huv)).1)
  have hH : H.Connected := by
    let : Nonempty V := ⟨C.base⟩
    refine ⟨fun u v => ?_⟩
    obtain ⟨p, hp, _⟩ := C.exists_short_arc u v
    refine ⟨p.transfer H ?_⟩
    intro e he
    exact (mem_edgeGraph _ _).mpr ⟨List.mem_toFinset.mpr (hp e he), hl e (hp e he)⟩
  let T := edgeGraph (kruskalEdges l)
  have hTH : T ≤ H := edgeGraph_mono (kruskalEdges_subset l)
  have hT : T.IsTree := kruskal_isTree l hl hH
  refine ⟨T, hTH.trans hHG, hT, ?_⟩
  have hwT : ∀ e ∈ T.edgeSet, w e = 1 := by
    intro e he
    exact C.unit e (List.mem_toFinset.mp ((mem_edgeGraph _ _).mp (edgeSet_mono hTH he)).1)
  rw [totalWeight_eq_card_mul T w 1 hwT, mul_one]
  have hcard : (T.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
    exact_mod_cast hT.card_edgeFinset
  linarith

theorem exists_mst_weight : ∃ T : SimpleGraph V, IsMinimumSpanningTree G T w ∧
    totalWeight T w = (Fintype.card V : ℝ) - 1 := by
  obtain ⟨T, hTG, hT, hweight⟩ := C.exists_unit_tree
  exact ⟨T, ⟨hTG, hT, fun S hSG hS => hweight ▸ C.tree_weight_lower hSG hS⟩, hweight⟩

theorem mst_weight {T : SimpleGraph V} (hT : IsMinimumSpanningTree G T w) :
    totalWeight T w = (Fintype.card V : ℝ) - 1 := by
  obtain ⟨S, hS, hwS⟩ := C.exists_mst_weight
  exact (hT.weight_eq hS).trans hwS

theorem lightness_eq {T : SimpleGraph V} (hT : IsMinimumSpanningTree G T w) :
    lightness G T w = totalWeight G w / ((Fintype.card V : ℝ) - 1) := by
  rw [lightness, C.mst_weight hT]

end UnitSpanningCycle
end LightSpanners
