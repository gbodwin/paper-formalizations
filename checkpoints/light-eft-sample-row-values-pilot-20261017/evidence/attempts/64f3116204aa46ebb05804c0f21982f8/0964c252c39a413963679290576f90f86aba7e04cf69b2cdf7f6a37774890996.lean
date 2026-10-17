import LightEFTSpanners.NativeDecompositionMaximum

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {X : Type*} {k : ℕ}
attribute [local instance] Classical.propDecidable

/-- Preserving actual within-block walks coarsens the component relation at
that same original partition. No relation between new iterates is assumed. -/
theorem componentRefinement_le_of_routes (H K : SimpleGraph X) (R : Setoid X)
    (hr : ∀ a b,(blockGraph H R).Reachable a b → (blockGraph K R).Reachable a b) :
    componentRefinement H R≤componentRefinement K R := by
  intro a b hab
  exact hr a b hab

/-- Coarsening every colored component relation can only remove splitting
colors, never create one. -/
theorem splitColors_subset_of_components_le (H K : Fin k → SimpleGraph X)
    (R : Setoid X) (hc : ∀ c,componentRefinement (H c) R≤componentRefinement (K c) R) :
    splitColors K R⊆splitColors H R := by
  intro c hcin
  have hne : componentRefinement (K c) R≠R := (mem_filter.mp hcin).2
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro heq
  apply hne
  apply le_antisymm (componentRefinement_le _ _)
  exact heq.symm.le.trans (hc c)

/-- The true minimum splitting-color priority increases when every original
within-block connection survives. The no-split sentinel is the color count. -/
theorem refinementPriority_le_of_components_le (H K : Fin k → SimpleGraph X)
    (R : Setoid X) (hc : ∀ c,componentRefinement (H c) R≤componentRefinement (K c) R) :
    refinementPriority H R≤refinementPriority K R := by
  classical
  have hsub := splitColors_subset_of_components_le H K R hc
  by_cases hK : (splitColors K R).Nonempty
  · have hH : (splitColors H R).Nonempty :=
      ⟨(splitColors K R).min' hK,hsub (min'_mem _ hK)⟩
    simp only [refinementPriority,dite_eq_left hH,dite_eq_left hK]
    exact min'_le _ _ (hsub (min'_mem _ hK))
  · simp only [refinementPriority,dite_eq_right hK]
    split
    · exact (splitColors H R).min' _ |>.isLt.le
    · exact le_rfl

/-- If the actual least-color priorities agree, the next real refinement step
can only become coarser under all-color within-block connection preservation. -/
theorem refinementStep_le_of_priority_eq (H K : Fin k → SimpleGraph X)
    (R : Setoid X) (hc : ∀ c,componentRefinement (H c) R≤componentRefinement (K c) R)
    (hp : refinementPriority H R=refinementPriority K R) :
    refinementStep H R≤refinementStep K R := by
  classical
  have hsub := splitColors_subset_of_components_le H K R hc
  by_cases hH : (splitColors H R).Nonempty
  · by_cases hK : (splitColors K R).Nonempty
    · have heq : (splitColors H R).min' hH=(splitColors K R).min' hK := by
        apply Fin.ext
        simpa only [refinementPriority,dite_eq_left hH,dite_eq_left hK] using hp
      simp only [refinementStep,dite_eq_left hH,dite_eq_left hK]
      rw [heq]
      exact hc _
    · have heq : ((splitColors H R).min' hH).val=k := by
        simpa only [refinementPriority,dite_eq_left hH,dite_eq_right hK] using hp
      exact False.elim (((splitColors H R).min' hH).isLt.ne heq)
  · have hK : ¬(splitColors K R).Nonempty := by
      rintro ⟨c,hc⟩
      exact hH ⟨c,hsub hc⟩
    simp only [refinementStep,dite_eq_right hH,dite_eq_right hK,le_refl]
/-- An actual color-valued priority identifies the exact selected component
refinement. The terminal sentinel cannot equal any genuine color value. -/
theorem refinementStep_eq_of_priority (H : Fin k → SimpleGraph X) (R : Setoid X)
    (c : Fin k) (hp : refinementPriority H R=c.val) :
    refinementStep H R=componentRefinement (H c) R := by
  classical
  by_cases hn : (splitColors H R).Nonempty
  · have hcolor : (splitColors H R).min' hn=c := by
      apply Fin.ext
      simpa only [refinementPriority,dite_eq_left hn] using hp
    simp only [refinementStep,dite_eq_left hn,hcolor]
  · have hh : k=c.val := by simpa only [refinementPriority,dite_eq_right hn] using hp
    exact False.elim (c.isLt.ne hh.symm)
end LightEFTSpanners.MultigraphCuts
