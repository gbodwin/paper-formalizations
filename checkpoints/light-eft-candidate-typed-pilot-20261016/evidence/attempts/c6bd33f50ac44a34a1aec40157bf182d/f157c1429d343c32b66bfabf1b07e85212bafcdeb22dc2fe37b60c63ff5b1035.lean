import LightEFTSpanners.NativeCenterSplit

namespace LightEFTSpanners.EvenSplitting
variable {V E : Type*}

/-- Literal original-edge expansion of a selected set after one split. The
fresh ID expands to both deleted IDs; every selected old ID keeps its identity. -/
def splitPullback (G : Graph (Option V) E) (i j : CenterInc G)
    (A : Set (Option E)) : Set E :=
  {e | some e∈A ∨ (none∈A ∧ (e=i.val ∨ e=j.val))}

/-- An old ID removed by the split is not an actual output edge, even when the
two other endpoints coincide and the fresh output edge is a loop. -/
theorem centerSplit_old_edge (G : Graph (Option V) E) (i j : CenterInc G) (e : E) :
    some e∈(centerSplit G i j).edgeSet ↔ e∈G.edgeSet ∧ e≠i.val ∧ e≠j.val := by
  constructor
  · intro he
    obtain ⟨x,y,h,hi,hj⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact ⟨h.edge_mem,hi,hj⟩
  · rintro ⟨he,hi,hj⟩
    obtain ⟨x,y,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact (show (centerSplit G i j).IsLink (some e) x y from ⟨h,hi,hj⟩).edge_mem

theorem splitPullback_subset (G : Graph (Option V) E) (i j : CenterInc G)
    {A : Set (Option E)} (hA : A⊆(centerSplit G i j).edgeSet) :
    splitPullback G i j A⊆G.edgeSet := by
  rintro e (he | ⟨_,rfl | rfl⟩)
  · exact ((centerSplit_old_edge G i j e).mp (hA he)).1
  · exact (centerEnd_link G i).edge_mem
  · exact (centerEnd_link G j).edge_mem

/-- Disjoint output edge sets expand to disjoint original edge sets. The
actual-output-subset hypotheses prevent a removed ID from appearing twice. -/
theorem splitPullback_disjoint (G : Graph (Option V) E) (i j : CenterInc G)
    {A B : Set (Option E)} (hA : A⊆(centerSplit G i j).edgeSet)
    (hB : B⊆(centerSplit G i j).edgeSet) (hAB : Disjoint A B) :
    Disjoint (splitPullback G i j A) (splitPullback G i j B) := by
  apply Set.disjoint_left.mpr
  intro e ha hb
  rcases ha with ha | ⟨hna,hi | hj⟩
  · rcases hb with hb | ⟨_,hi | hj⟩
    · exact Set.disjoint_left.mp hAB ha hb
    · exact ((centerSplit_old_edge G i j e).mp (hA ha)).2.1 hi
    · exact ((centerSplit_old_edge G i j e).mp (hA ha)).2.2 hj
  · rcases hb with hb | ⟨hnb,_⟩
    · exact ((centerSplit_old_edge G i j e).mp (hB hb)).2.1 hi
    · exact Set.disjoint_left.mp hAB hna hnb
  · rcases hb with hb | ⟨hnb,_⟩
    · exact ((centerSplit_old_edge G i j e).mp (hB hb)).2.2 hj
    · exact Set.disjoint_left.mp hAB hna hnb
end LightEFTSpanners.EvenSplitting
