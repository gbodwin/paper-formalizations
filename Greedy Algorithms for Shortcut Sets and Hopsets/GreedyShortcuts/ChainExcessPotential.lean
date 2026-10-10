import GreedyShortcuts.ChainEndpointFloor

/-! Remove only an immutable endpoint-label baseline from the raw potential.
Every insertion drop is exactly unchanged; the actual algorithm stays raw-sum
minimizing and retains its separate maximum-distance stopping predicate. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def floorPotential : ℕ :=
  ∑ st ∈ T.important,T.endpointFloor st.1 st.2

noncomputable def excessPotential (H : Finset (V × V)) : ℕ :=
  ∑ st ∈ T.important,(T.distance H st.1 st.2-T.endpointFloor st.1 st.2)

/-- Exact accounting identity, including covered, uncovered and equal-label
endpoints. No demand is discarded merely because its distance is small. -/
theorem potential_eq_floor_add_excess (H : Finset (V × V)) :
    T.potential H = T.floorPotential+T.excessPotential H := by
  classical
  unfold potential floorPotential excessPotential
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro st hst
  have hl := T.endpointFloor_le_distance H (T.important_spec hst).1
  omega

/-- Baseline removal leaves the exact marginal of every insertion unchanged.
This is an identity between two numerical accounts of the same state. -/
theorem excess_drop_eq (H J : Finset (V × V)) :
    T.excessPotential H-T.excessPotential J = T.potential H-T.potential J := by
  rw [T.potential_eq_floor_add_excess H,T.potential_eq_floor_add_excess J]
  omega

theorem excessPotential_antitone : Antitone T.excessPotential := by
  intro H J hHJ
  exact Finset.sum_le_sum (fun st _ => Nat.sub_le_sub_right
    (T.distance_antitone st.1 st.2 hHJ) _)

noncomputable def unsaturated (H : Finset (V × V)) : Finset (V × V) := by
  classical
  exact T.important.filter (fun st => T.endpointFloor st.1 st.2 < T.distance H st.1 st.2)

theorem unsaturated_antitone : Antitone T.unsaturated := by
  classical
  intro H J hHJ st hst
  obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hst
  exact Finset.mem_filter.mpr ⟨hp,hd.trans_le (T.distance_antitone st.1 st.2 hHJ)⟩

theorem excess_eq_sum_unsaturated (H : Finset (V × V)) :
    T.excessPotential H =
      ∑ st ∈ T.unsaturated H,(T.distance H st.1 st.2-T.endpointFloor st.1 st.2) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro st hst hout
  have hle : T.distance H st.1 st.2 ≤ T.endpointFloor st.1 st.2 := by
    by_contra hn
    exact hout (Finset.mem_filter.mpr ⟨hst,by omega⟩)
  exact Nat.sub_eq_zero_of_le hle

/-- Only initially unsaturated demands can contribute to future excess.
The coefficient does not count rows that are already at their endpoint floor. -/
theorem excess_le_initial_card_mul (H : Finset (V × V)) (L : ℕ)
    (hmax : ∀ st ∈ T.important,T.distance H st.1 st.2 ≤ L) :
    T.excessPotential H ≤ (T.unsaturated ∅).card*L := by
  classical
  rw [T.excess_eq_sum_unsaturated H]
  calc
    _ ≤ ∑ _st ∈ T.unsaturated H,L := by
      apply Finset.sum_le_sum
      intro st hst
      exact (Nat.sub_le _ _).trans (hmax st (Finset.mem_filter.mp hst).1)
    _ = (T.unsaturated H).card*L := by simp
    _ ≤ (T.unsaturated ∅).card*L := Nat.mul_le_mul_right _
      (Finset.card_le_card (T.unsaturated_antitone (Finset.empty_subset H)))

end GreedyShortcuts.ChainDistance.Context
