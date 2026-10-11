import MinorFreeSpanners.IntegerSelectedRegularization

namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Subtract the integer boundary budget, rather than rounding down a real
minimum-degree lower bound. The resulting regular degree loses no extra1. -/
theorem selected_regular_degree_bounds (d : ℕ) (eps : ℝ)
    (hd : 0 < d) (he0 : 0 ≤ eps) (he1 : eps < 1) :
    1 ≤ d-⌊eps*(d:ℝ)⌋₊ ∧ d-⌊eps*(d:ℝ)⌋₊ ≤ d ∧
      (1-eps)*d ≤ ((d-⌊eps*(d:ℝ)⌋₊:ℕ):ℝ) ∧
      (d-⌊eps*(d:ℝ)⌋₊)+⌊eps*(d:ℝ)⌋₊=d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hp : 0 ≤ eps*(d:ℝ) := by positivity
  have hf : ⌊eps*(d:ℝ)⌋₊ < d := (Nat.floor_lt hp).mpr (by nlinarith)
  refine ⟨by omega,Nat.sub_le _ _,?_,Nat.sub_add_cancel hf.le⟩
  rw [Nat.cast_sub hf.le]
  have hh := Nat.floor_le hp
  nlinarith

/-- The two literal selected domains cover their actual finite subtype. -/
theorem selected_star_domains_cover {V : Type*} (C : Finset V) (L : V → Finset V) :
    selectedStarLeaves C L ∪ selectedStarCenters C L=Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro x
  rcases Finset.mem_union.mp x.property with hc|hl
  · exact Finset.mem_union_right _ (Finset.mem_subtype.mpr hc)
  · exact Finset.mem_union_left _ (Finset.mem_subtype.mpr hl)

theorem selected_star_centers_nonempty {V : Type*} (C : Finset V) (L : V → Finset V)
    (hC : C.Nonempty) : (selectedStarCenters C L).Nonempty := by
  obtain ⟨c,hc⟩ := hC
  exact ⟨⟨c,Finset.mem_union_left _ hc⟩,Finset.mem_subtype.mpr hc⟩

end MinorFreeSpanners
