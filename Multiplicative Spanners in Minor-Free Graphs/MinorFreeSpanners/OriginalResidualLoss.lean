import MinorFreeSpanners.GeneralResidualCoverage

/-! Actual original-host edge accounting for deletion of a residual set.
All edge sets contain genuine unordered simple edges. The boundary term is
bounded by the literal directed crossing sum; no density oracle is hidden. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def incidentEdges (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ x ∈ e.toFinset, x ∈ U)

@[simp] theorem mem_incidentEdges_mk (G : SimpleGraph V) (U : Finset V) (x y : V) :
    s(x,y) ∈ incidentEdges G U ↔ G.Adj x y ∧ (x∈U ∨ y∈U) := by
  simp [incidentEdges]

/-- Exact partition into retained induced edges and edges incident to U. -/
theorem edge_count_delete_partition (G : SimpleGraph V) (U : Finset V) :
    G.edgeFinset.card = (G.induce ((Finset.univ\U:Finset V):Set V)).edgeFinset.card+
      (incidentEdges G U).card := by
  classical
  rw [← G.card_filter_edgeFinset_toFinset_subset (Finset.univ\U)]
  have he : G.edgeFinset.filter (fun e => ¬ e.toFinset ⊆ Finset.univ\U)=incidentEdges G U := by
    ext e
    simp only [incidentEdges,Finset.mem_filter,Finset.subset_iff]
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_forall,not_not]
    tauto
  rw [← he]
  exact (Finset.card_filter_add_card_filter_not (s := G.edgeFinset) _).symm

noncomputable def crossingEdges (G : SimpleGraph V) (U Z : Finset V) : Finset (Sym2 V) :=
  U.biUnion (fun x => (Z.filter (G.Adj x)).image (fun y => s(x,y)))

omit [Fintype V] in
theorem crossingEdges_card_le (G : SimpleGraph V) (U Z : Finset V) :
    (crossingEdges G U Z).card ≤ graphCrossingCount G U Z := by
  calc
    _ ≤ ∑ x ∈ U, ((Z.filter (G.Adj x)).image (fun y => s(x,y))).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

/-- Every removed edge is internal to U union Y, or crosses from U into Z. -/
theorem incidentEdges_card_bound (G : SimpleGraph V) (U Y Z : Finset V)
    (hcover : ∀ x, x∈U ∨ x∈Y ∨ x∈Z) :
    (incidentEdges G U).card ≤ (G.induce ((U∪Y:Finset V):Set V)).edgeFinset.card+
      graphCrossingCount G U Z := by
  classical
  let A := G.edgeFinset.filter (fun e => e.toFinset ⊆ U∪Y)
  have haux : ∀ x y, G.Adj x y → x∈U → s(x,y)∈A ∪ crossingEdges G U Z := by
    intro x y hxy hx
    rcases hcover y with hy | hy | hy
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨by simpa using hxy,by
        rw [Sym2.toFinset_mk_eq]
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hx,
          Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ hy)⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨by simpa using hxy,by
        rw [Sym2.toFinset_mk_eq]
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hx,
          Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hy)⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩,rfl⟩⟩
  have hsub : incidentEdges G U ⊆ A ∪ crossingEdges G U Z := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨hxy,hx|hy⟩ := (mem_incidentEdges_mk G U x y).mp he
      · exact haux x y hxy hx
      · simpa only [Sym2.eq_swap] using haux y x hxy.symm hy
  calc
    _ ≤ (A ∪ crossingEdges G U Z).card := Finset.card_le_card hsub
    _ ≤ A.card+(crossingEdges G U Z).card := Finset.card_union_le _ _
    _ ≤ A.card+graphCrossingCount G U Z := Nat.add_le_add_left (crossingEdges_card_le G U Z) _
    _ = _ := by rw [G.card_filter_edgeFinset_toFinset_subset]

/-- A genuine universal induced-density bound pays the internal removed
edges; the remaining loss is exactly the actual crossing budget. -/
theorem incidentEdges_real_bound (G : SimpleGraph V) (U Y Z : Finset V)
    (d t : ℝ) (hd : 0 ≤ d)
    (hcover : ∀ x, x∈U ∨ x∈Y ∨ x∈Z)
    (hden : ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ))
    (hcross : (graphCrossingCount G U Z:ℝ) ≤ t) :
    ((incidentEdges G U).card:ℝ) ≤ d*((U.card:ℝ)+Y.card)+t := by
  have h := incidentEdges_card_bound G U Y Z hcover
  have hr : ((incidentEdges G U).card:ℝ) ≤
      ((G.induce ((U∪Y:Finset V):Set V)).edgeFinset.card:ℝ)+graphCrossingCount G U Z := by exact_mod_cast h
  have hc : ((U∪Y).card:ℝ) ≤ (U.card:ℝ)+Y.card := by exact_mod_cast Finset.card_union_le U Y
  have hm := mul_le_mul_of_nonneg_left hc hd
  have hdens := hden (U∪Y)
  linarith

end MinorFreeSpanners
