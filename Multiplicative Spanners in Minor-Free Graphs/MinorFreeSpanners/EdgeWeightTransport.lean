import MinorFreeSpanners.GreedyMinorPolylogLightness

/-! Changing weights outside the input edge set changes neither its walks,
subgraph weights, spanner inequalities nor minimum spanning trees. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

 theorem walkWeight_congr_edges {V : Type*} {G H : SimpleGraph V}
    {w z : Sym2 V → ℝ} (hH : H≤G) (heq : ∀ e∈G.edgeSet,w e=z e)
    {a b : V} (p : H.Walk a b) : walkWeight w p=walkWeight z p := by
  unfold walkWeight
  congr 1
  apply List.map_congr_left
  intro e he
  exact heq e (edgeSet_mono hH (p.edges_subset_edgeSet he))

 theorem totalWeight_congr_edges {V : Type*} [Fintype V] {G H : SimpleGraph V}
    {w z : Sym2 V → ℝ} (hH : H≤G) (heq : ∀ e∈G.edgeSet,w e=z e) :
    totalWeight H w=totalWeight H z := by
  apply Finset.sum_congr rfl
  intro e he
  exact heq e (edgeSet_mono hH (H.mem_edgeFinset.mp he))

 theorem mst_congr_edges {V : Type*} [Fintype V] {G T : SimpleGraph V}
    {w z : Sym2 V → ℝ} (heq : ∀ e∈G.edgeSet,w e=z e)
    (hT : IsMinimumSpanningTree G T w) : IsMinimumSpanningTree G T z := by
  refine ⟨hT.1,hT.2.1,?_⟩
  intro S hS htree
  rw [←totalWeight_congr_edges hT.1 heq,←totalWeight_congr_edges hS heq]
  exact hT.2.2 S hS htree

 theorem spanner_congr_edges {V : Type*} {G H : SimpleGraph V}
    {w z : Sym2 V → ℝ} {t : ℝ} (heq : ∀ e∈G.edgeSet,w e=z e)
    (hspan : IsSpanner G H w t) : IsSpanner G H z t := by
  refine ⟨hspan.1,?_⟩
  intro a b p
  obtain ⟨q,hq⟩ := hspan.2 a b p
  exact ⟨q,by simpa only [walkWeight_congr_edges hspan.1 heq q,
    walkWeight_congr_edges le_rfl heq p] using hq⟩

end MinorFreeSpanners
