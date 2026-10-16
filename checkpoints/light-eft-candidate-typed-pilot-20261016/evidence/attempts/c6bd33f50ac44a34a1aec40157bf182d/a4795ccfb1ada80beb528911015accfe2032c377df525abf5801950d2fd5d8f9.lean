import LightEFTSpanners.NativeSplitPullback

namespace LightEFTSpanners.EvenSplitting
open SimpleGraph
variable {V E : Type*}

/-- Actual restricted native reachability, with endpoint membership explicit. -/
def EdgeSetJoins (G : Graph V E) (A : Set E) (x y : V) : Prop :=
  ∃ (hx : x∈G.vertexSet) (hy : y∈G.vertexSet),
    (G.restrict A).toSimpleGraph.Reachable ⟨x,hx⟩ ⟨y,hy⟩

theorem restricted_link_reachable (G : Graph V E) (A : Set E)
    {e : E} {x y : G.vertexSet} (he : e∈A) (h : G.IsLink e x.val y.val) :
    (G.restrict A).toSimpleGraph.Reachable x y := by
  classical
  by_cases hxy : x=y
  · subst y; exact Reachable.rfl
  · exact (show (G.restrict A).toSimpleGraph.Adj x y from ⟨hxy,e,he,h⟩).reachable

/-- Every output adjacency expands to an actual old path: an unchanged link,
or the two removed links through the distinguished center. -/
theorem splitPullback_adj (G : Graph (Option V) E) (i j : CenterInc G)
    (A : Set (Option E)) {x y : G.vertexSet}
    (h : ((centerSplit G i j).restrict A).toSimpleGraph.Adj x y) :
    (G.restrict (splitPullback G i j A)).toSimpleGraph.Reachable x y := by
  obtain ⟨_,e,he,hlink⟩ := h
  cases e with
  | some e =>
    exact restricted_link_reachable G _ (Or.inl he) hlink.1
  | none =>
    let z : G.vertexSet := ⟨none,(centerEnd_link G i).left_mem⟩
    rcases hlink with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hi : G.IsLink i.val x.val z.val := by
        simpa only [hx] using (centerEnd_link G i).symm
      have hj : G.IsLink j.val z.val y.val := by
        simpa only [hy] using centerEnd_link G j
      exact (restricted_link_reachable G _ (Or.inr ⟨he,Or.inl rfl⟩) hi).trans
        (restricted_link_reachable G _ (Or.inr ⟨he,Or.inr rfl⟩) hj)
    · have hj : G.IsLink j.val x.val z.val := by
        simpa only [hx] using (centerEnd_link G j).symm
      have hi : G.IsLink i.val z.val y.val := by
        simpa only [hy] using centerEnd_link G i
      exact (restricted_link_reachable G _ (Or.inr ⟨he,Or.inr rfl⟩) hj).trans
        (restricted_link_reachable G _ (Or.inr ⟨he,Or.inl rfl⟩) hi)

/-- Literal path expansion preserves all output connections, including those
whose endpoints are the center. No cut or connectivity premise is assumed. -/
theorem splitPullback_reachable (G : Graph (Option V) E) (i j : CenterInc G)
    (A : Set (Option E)) {x y : G.vertexSet}
    (h : ((centerSplit G i j).restrict A).toSimpleGraph.Reachable x y) :
    (G.restrict (splitPullback G i j A)).toSimpleGraph.Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | cons h _ ih => exact (splitPullback_adj G i j A h).trans ih

theorem splitPullback_joins (G : Graph (Option V) E) (i j : CenterInc G)
    (A : Set (Option E)) {x y : Option V} (h : EdgeSetJoins (centerSplit G i j) A x y) :
    EdgeSetJoins G (splitPullback G i j A) x y := by
  obtain ⟨hx,hy,hr⟩ := h
  exact ⟨hx,hy,splitPullback_reachable G i j A hr⟩
end LightEFTSpanners.EvenSplitting
