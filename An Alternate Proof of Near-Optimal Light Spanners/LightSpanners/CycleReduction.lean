import LightSpanners.CopyWeights
import LightSpanners.TreeTour
import LightSpanners.TourCycle
import LightSpanners.TreeReduction

namespace LightSpanners
open SimpleGraph
universe u

/-- Choose representatives in the actual position cycle of the constructed tree tour. -/
theorem exists_tree_vertex_copies {V : Type u} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (hn : 3 ≤ Fintype.card V) :
    ∃ m : ℕ, m + 3 = 2 * (Fintype.card V - 1) ∧
      Nonempty (VertexCopies T (cycleGraph (m + 3))) := by
  classical
  obtain ⟨r, p, hlen, hcover⟩ := exists_tree_tour hT
  let m := 2 * (Fintype.card V - 1) - 3
  have hm : m + 3 = 2 * (Fintype.card V - 1) := by dsimp [m]; omega
  have hlen' : p.length = m + 3 := hlen.trans hm.symm
  let f := closedWalkCycleHom p hlen'
  have hsurj : Function.Surjective f := closedWalkCycleHom_surjective p hlen' hcover
  refine ⟨m, hm, ⟨?_⟩⟩
  exact { projection := f
          representative := ⟨Function.surjInv hsurj, Function.injective_surjInv hsurj⟩
          projection_representative := Function.surjInv_eq hsurj }

/-- A finite output graph with an actual unit spanning cycle and a reference MST. -/
def UnitCycleReductionResult (n vertexBound : ℕ) (g lowerLightness : ℝ) : Prop :=
  ∃ (G T : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ),
    IsMinimumSpanningTree G T w ∧ Nonempty (UnitSpanningCycle G w) ∧
    WeightedGirthAbove G w g ∧ n ≤ vertexBound ∧ lowerLightness ≤ lightness G T w

/-- The spanning-cycle half of Lemma 3.5. The tour, representative copies,
actual graph, girth transfer, vertex budget, and factor-two lightness transfer
are all constructed from a unit-weight spanning tree. -/
theorem unit_tree_to_spanning_cycle {V : Type u} [Fintype V]
    {G T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree)
    (w : Sym2 V → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hunit : ∀ e ∈ T.edgeSet, w e = 1) (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e)
    (hG : WeightedGirthAbove G w g) (hnon : ¬ G.IsAcyclic) :
    ∃ n : ℕ, UnitCycleReductionResult n (2 * Fintype.card V - 2) g (lightness G T w / 2) := by
  classical
  have hn := nonforest_three_le_card hnon
  obtain ⟨m, hm, ⟨D⟩⟩ := exists_tree_vertex_copies hT hn
  let B := canonicalUnitSpanningCycle m
  have hbelow : g < (m : ℝ) + 3 := by
    have hlt := hG.threshold_lt_card_of_nonforest
      (fun e he => zero_lt_one.trans_le (hw e he)) hnon
    have hc : (Fintype.card V : ℝ) ≤ m + 3 := by
      exact_mod_cast (show Fintype.card V ≤ m + 3 by omega)
    exact hlt.trans_le hc
  have hbase := D.base_weightedGirth w hunit (cycleGraph_weightedGirthAbove hbelow)
  have hnewg := D.weightedGirthAbove hTG w g hg hunit hw hG hbase
  have hsize : Fintype.card (Fin (m + 3)) ≤ 2 * Fintype.card V - 1 := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨S, hS, hlight⟩ := D.exists_mst_lightness hTG w hT hunit hw B (by omega) hsize
  refine ⟨m + 3, D.graph G, S, D.weight w, hS,
    ⟨D.unitSpanningCycle hTG w hunit hw B⟩, hnewg, ?_, hlight⟩
  omega

/-- Complete Lemma 3.5 reduction with explicit constants: at most `4n-4`
vertices, an actual unit spanning cycle and MST, preserved weighted-girth
threshold, and at least one quarter of the input lightness. -/
theorem unit_spanning_cycle_reduction_of_mst {V : Type u} [Fintype V]
    {G T : SimpleGraph V} (w : Sym2 V → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hnon : ¬ G.IsAcyclic) :
    ∃ n : ℕ, UnitCycleReductionResult n (4 * Fintype.card V - 4) g (lightness G T w / 4) := by
  classical
  have hn := nonforest_three_le_card hnon
  obtain ⟨X, instX, hX⟩ := unit_tree_reduction_of_mst w g (by omega) hg hT hw hG hnon
  let := instX
  obtain ⟨GX, TX, wX, hXmin, hXnon, hXlow, hXunit, hXg, hXcard, hXlight⟩ := hX
  obtain ⟨n, GY, TY, wY, hYmin, hYcycle, hYg, hYcard, hYlight⟩ :=
    unit_tree_to_spanning_cycle hXmin.1 hXmin.2.1 wX g hg hXunit hXlow hXg hXnon
  refine ⟨n, GY, TY, wY, hYmin, hYcycle, hYg, ?_, ?_⟩
  · omega
  · linarith

end LightSpanners
