import MinorFreeSpanners.UnmatedBadIncidence
import MinorFreeSpanners.DirectedCrossingBudget

/-! Quantitative assembly from actual mate and unique-leaf incidences.
The local leaf bound remains an explicit input of this helper. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
theorem badStarPairCount_eq_center_sum (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) :
    badStarPairCount G C L = ∑ b ∈ C, (C.filter fun c => IsBadStarPair G L b c).card := by
  classical
  rw [badStarPairCount_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

/-- Count actual bad center pairs through either a literal mate incidence
or the disjoint unique-leaf classes. No bad-pair oracle is substituted. -/
theorem badStarPairCount_le_incidence_budget (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (ell : ℕ) (q a r : ℝ)
    (hfull : ∀ b ∈ C, (L b).card=ell)
    (hmated : ∀ b ∈ C, ((matedStarCenters G q C L b).card:ℝ) ≤ a)
    (hleaf : ∀ b ∈ C, ∀ u ∈ L b,
      ((unmatedBadLeafCenters G q C L b u).card:ℝ) ≤ r) :
    (badStarPairCount G C L:ℝ) ≤ C.card*(a+ell*r) := by
  classical
  have hcenter (b : V) (hb : b∈C) :
      ((C.filter fun c => IsBadStarPair G L b c).card:ℝ) ≤ a+ell*r := by
    have hsub : (C.filter fun c => IsBadStarPair G L b c) ⊆
        matedStarCenters G q C L b ∪ unmatedBadCenters G q C L b := by
      intro c hc
      obtain ⟨hc,hbad⟩ := Finset.mem_filter.mp hc
      by_cases hm : c ∈ matedStarCenters G q C L b
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc,hbad,hm⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hu : ((unmatedBadCenters G q C L b).card:ℝ) ≤ ell*r := by
      rw [unmatedBadCenters_card]
      push_cast
      calc
        _ ≤ ∑ u ∈ L b, r := Finset.sum_le_sum (fun u hu => hleaf b hb u hu)
        _ = _ := by simp [hfull b hb]
    have hc := Nat.cast_le (α:=ℝ).mpr hcard
    push_cast at hc
    linarith [hmated b hb]
  rw [badStarPairCount_eq_center_sum]
  push_cast
  calc
    _ ≤ ∑ b ∈ C, (a+ell*r) := Finset.sum_le_sum (fun b hb => hcenter b hb)
    _ = _ := by simp; ring

end MinorFreeSpanners
