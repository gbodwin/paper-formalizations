import LightSpanners.VertexCopies

namespace LightSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V W : Type*}

theorem totalWeight_mono_subgraph [Fintype V] {G H : SimpleGraph V} (hGH : G ≤ H)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ H.edgeSet, 0 ≤ w e) :
    totalWeight G w ≤ totalWeight H w := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (edgeFinset_mono hGH)
    (fun e he _ => hw e (by simpa using he))

theorem totalWeight_tree_add_chords [Fintype V] {G T : SimpleGraph V}
    (hTG : T ≤ G) (w : Sym2 V → ℝ) :
    totalWeight G w = totalWeight T w + totalWeight (G \ T) w := by
  classical
  unfold totalWeight
  have hedge (i : Fintype (G \ T).edgeSet) :
      @SimpleGraph.edgeFinset V (G \ T) i = G.edgeFinset \ T.edgeFinset := by
    ext e
    simp only [mem_edgeFinset, edgeSet_sdiff, Set.mem_sdiff, Finset.mem_sdiff]
  rw [hedge]
  simpa only [add_comm] using (Finset.sum_sdiff (edgeFinset_mono hTG) (f := w)).symm

namespace VertexCopies
variable [Fintype V] [Fintype W] {G T : SimpleGraph V} {C : SimpleGraph W}
    (D : VertexCopies T C)

theorem base_chords_disjoint :
    Disjoint C.edgeFinset ((G \ T).map D.representative).edgeFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heC heK
  have heC' : e ∈ C.edgeSet := by simpa using heC
  have heK' : e ∈ ((G \ T).map D.representative).edgeSet := mem_edgeFinset.mp heK
  rw [edgeSet_map] at heK'
  obtain ⟨d, hd, rfl⟩ := heK'
  have ht := D.projection.map_mem_edgeSet heC'
  rw [D.project_representative_edge] at ht
  have hn : d ∉ T.edgeSet := by
    exact (show d ∈ G.edgeSet ∧ d ∉ T.edgeSet from by
      simpa only [edgeSet_sdiff, Set.mem_sdiff] using hd).2
  exact hn ht

theorem totalWeight_chords (w : Sym2 V → ℝ) :
    totalWeight ((G \ T).map D.representative) (D.weight w) = totalWeight (G \ T) w := by
  classical
  unfold totalWeight
  have hedge (i : Fintype ((G \ T).map D.representative).edgeSet) :
      @SimpleGraph.edgeFinset W ((G \ T).map D.representative) i =
        (G \ T).edgeFinset.map D.representative.sym2Map := by
    ext e
    simp only [mem_edgeFinset, edgeSet_map, Set.mem_image, Finset.mem_map]
  rw [hedge, Finset.sum_map]
  apply Finset.sum_congr (by ext e; simp only [mem_edgeFinset])
  intro e _
  exact congrArg w (D.project_representative_edge e)

/-- The copied graph's total weight splits into its base and all old chords. -/
theorem totalWeight_graph (w : Sym2 V → ℝ) :
    totalWeight (D.graph G) (D.weight w) =
      totalWeight C (D.weight w) + totalWeight (G \ T) w := by
  classical
  calc
    _ = totalWeight C (D.weight w) +
        totalWeight ((G \ T).map D.representative) (D.weight w) := by
      unfold totalWeight graph
      have hedge (i : Fintype (C ⊔ (G \ T).map D.representative).edgeSet) :
          @SimpleGraph.edgeFinset W (C ⊔ (G \ T).map D.representative) i =
            C.edgeFinset ∪ ((G \ T).map D.representative).edgeFinset := by
        ext e
        simp only [mem_edgeFinset, edgeSet_sup, Set.mem_union, Finset.mem_union]
      rw [hedge, Finset.sum_union (D.base_chords_disjoint (G := G))]
      apply congrArg₂ (· + ·)
      all_goals
        apply Finset.sum_congr (by ext e; simp only [mem_edgeFinset])
        intro e _
        rfl
    _ = _ := by rw [D.totalWeight_chords]

/-- The base already weighs at least the original unit tree, because its
unit spanning tree has at least as many vertices as the original tree. -/
theorem base_weight_ge_tree [DecidableEq W] (w : Sym2 V → ℝ)
    (hT : T.IsTree) (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    (B : UnitSpanningCycle C (fun _ => 1)) :
    totalWeight T w ≤ totalWeight C (D.weight w) := by
  classical
  obtain ⟨S, hSC, hS, hweightS⟩ := B.exists_unit_tree
  have hsame : totalWeight S (D.weight w) = totalWeight S (fun _ => 1) := by
    apply Finset.sum_congr rfl
    intro e he
    exact D.weight_on_base w hunit (edgeSet_mono hSC (by simpa using he))
  have hle := totalWeight_mono_subgraph hSC (D.weight w) (fun e he => by
    rw [D.weight_on_base w hunit he]
    norm_num)
  rw [hsame, hweightS] at hle
  have htree : totalWeight T w = (Fintype.card V : ℝ) - 1 := by
    rw [totalWeight_eq_card_mul T w 1 hunit, mul_one]
    have hc : (T.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
      exact_mod_cast hT.card_edgeFinset
    linarith
  have hc : (Fintype.card V : ℝ) ≤ Fintype.card W := by
    exact_mod_cast Fintype.card_le_of_injective _ D.representative.injective
  rw [htree]
  linarith

/-- The actual copied graph never decreases total graph weight. -/
theorem totalWeight_le_graph [DecidableEq W] (hTG : T ≤ G)
    (w : Sym2 V → ℝ) (hT : T.IsTree) (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    (B : UnitSpanningCycle C (fun _ => 1)) :
    totalWeight G w ≤ totalWeight (D.graph G) (D.weight w) := by
  rw [D.totalWeight_graph, totalWeight_tree_add_chords hTG w]
  exact add_le_add (D.base_weight_ge_tree w hT hunit B) le_rfl

/-- A linear bound on copied vertices gives the second factor-two lightness
transfer, with an actual minimum spanning tree of the constructed graph. -/
theorem exists_mst_lightness [DecidableEq W] (hTG : T ≤ G)
    (w : Sym2 V → ℝ) (hT : T.IsTree) (hunit : ∀ e ∈ T.edgeSet, w e = 1)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e) (B : UnitSpanningCycle C (fun _ => 1))
    (hn : 2 ≤ Fintype.card V) (hsize : Fintype.card W ≤ 2 * Fintype.card V - 1) :
    ∃ S, IsMinimumSpanningTree (D.graph G) S (D.weight w) ∧
      lightness G T w / 2 ≤ lightness (D.graph G) S (D.weight w) := by
  classical
  let B' := D.unitSpanningCycle hTG w hunit hw B
  obtain ⟨S, hS, hweightS⟩ := B'.exists_mst_weight
  refine ⟨S, hS, ?_⟩
  have htree : totalWeight T w = (Fintype.card V : ℝ) - 1 := by
    rw [totalWeight_eq_card_mul T w 1 hunit, mul_one]
    have hc : (T.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
      exact_mod_cast hT.card_edgeFinset
    linarith
  have hnreal : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpositive : 0 < totalWeight T w := by rw [htree]; linarith
  have hW : (3 : ℝ) ≤ Fintype.card W := by exact_mod_cast B'.three_le_card
  have hnewpos : 0 < totalWeight S (D.weight w) := by rw [hweightS]; linarith
  have hbudget : totalWeight S (D.weight w) ≤ 2 * totalWeight T w := by
    have hc : (Fintype.card W : ℝ) ≤ ((2 * Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast hsize
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card V), Nat.cast_mul] at hc
    norm_num at hc
    rw [hweightS, htree]
    linarith
  have hgraph := D.totalWeight_le_graph hTG w hT hunit B
  have hnonneg : 0 ≤ totalWeight G w :=
    Finset.sum_nonneg (fun e he => zero_le_one.trans (hw e (by simpa using he)))
  simp only [lightness, div_div]
  apply (div_le_div_iff₀ (mul_pos hpositive (by norm_num)) hnewpos).mpr
  calc
    _ ≤ totalWeight G w * (2 * totalWeight T w) :=
      mul_le_mul_of_nonneg_left hbudget hnonneg
    _ ≤ _ := by
      rw [mul_comm 2 (totalWeight T w)]
      exact mul_le_mul_of_nonneg_right hgraph (mul_nonneg hpositive.le (by norm_num))

end VertexCopies
end LightSpanners
