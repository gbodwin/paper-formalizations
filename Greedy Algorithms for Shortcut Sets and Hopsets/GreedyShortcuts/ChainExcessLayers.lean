import GreedyShortcuts.ChainExcessPotential

/-! Exact integer layer accounting for the unchanged raw potential.
The individual layer counts are not asserted to be greedily maximized. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def excessLayer (H : Finset (V × V)) (k : ℕ) : Finset (V × V) := by
  classical
  exact T.important.filter (fun st => k < T.distance H st.1 st.2-T.endpointFloor st.1 st.2)

noncomputable def layerPotential (H : Finset (V × V)) (k : ℕ) : ℕ :=
  ∑ st∈T.important,(T.distance H st.1 st.2-T.endpointFloor st.1 st.2-k)

theorem excessLayer_antitone (k : ℕ) : Antitone (fun H => T.excessLayer H k) := by
  classical
  intro H J hHJ st hst
  obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hst
  apply Finset.mem_filter.mpr
  exact ⟨hp,hd.trans_le (Nat.sub_le_sub_right (T.distance_antitone st.1 st.2 hHJ) _)⟩

theorem layerPotential_antitone (k : ℕ) : Antitone (fun H => T.layerPotential H k) := by
  intro H J hHJ
  exact Finset.sum_le_sum (fun st _ => Nat.sub_le_sub_right
    (Nat.sub_le_sub_right (T.distance_antitone st.1 st.2 hHJ) _) _)

theorem layerPotential_zero (H : Finset (V × V)) :
    T.layerPotential H 0 = T.excessPotential H := by
  simp only [layerPotential,excessPotential,Nat.sub_zero]

theorem excessLayer_zero (H : Finset (V × V)) : T.excessLayer H 0 = T.unsaturated H := by
  classical
  unfold excessLayer unsaturated
  apply Finset.filter_congr
  intro st _
  omega

/-- One layer removes exactly one unit from every demand still above it. -/
theorem layerPotential_step (H : Finset (V × V)) (k : ℕ) :
    T.layerPotential H k = (T.excessLayer H k).card + T.layerPotential H (k+1) := by
  classical
  unfold layerPotential
  calc
    _ = ∑ st∈T.important,((if k < T.distance H st.1 st.2-T.endpointFloor st.1 st.2 then 1 else 0)+
        (T.distance H st.1 st.2-T.endpointFloor st.1 st.2-(k+1))) := by
      apply Finset.sum_congr rfl
      intro st _
      split_ifs <;> omega
    _ = _ := by simp [Finset.sum_add_distrib,excessLayer]

/-- Every actual insertion splits its kth excess marginal exactly into
layer depletion and the next layer's marginal. Neither term is a surrogate
objective for the actual greedy choice. -/
theorem layer_drop_split {H J : Finset (V × V)} (hHJ : H ⊆ J) (k : ℕ) :
    T.layerPotential H k-T.layerPotential J k =
      ((T.excessLayer H k).card-(T.excessLayer J k).card)+
      (T.layerPotential H (k+1)-T.layerPotential J (k+1)) := by
  have hL := Finset.card_le_card (T.excessLayer_antitone k hHJ)
  have hP := T.layerPotential_antitone (k+1) hHJ
  change (T.excessLayer J k).card ≤ (T.excessLayer H k).card at hL
  change T.layerPotential J (k+1) ≤ T.layerPotential H (k+1) at hP
  rw [T.layerPotential_step H k,T.layerPotential_step J k]
  omega

/-- The original raw marginal is the sum of newly saturated demand count
and the exact marginal above the first excess layer. -/
theorem raw_drop_eq_saturation_add_layer {H J : Finset (V × V)} (hHJ : H ⊆ J) :
    T.potential H-T.potential J =
      ((T.unsaturated H).card-(T.unsaturated J).card)+
      (T.layerPotential H 1-T.layerPotential J 1) := by
  have h := T.layer_drop_split hHJ 0
  simpa only [T.layerPotential_zero,T.excessLayer_zero,Nat.zero_add,T.excess_drop_eq] using h

/-- No normalized route can use more than the finite number of chains. -/
theorem layerPotential_at_chain_count (H : Finset (V × V)) :
    T.layerPotential H (Fintype.card I) = 0 := by
  apply Finset.sum_eq_zero
  intro st _
  have h := T.distance_le_chains H st.1 st.2
  omega

/-- Exact telescoping across any finite prefix of the excess layers. -/
theorem layer_drop_prefix {H J : Finset (V × V)} (hHJ : H ⊆ J) (m : ℕ) :
    T.layerPotential H 0-T.layerPotential J 0 =
      (∑ k∈Finset.range m,((T.excessLayer H k).card-(T.excessLayer J k).card))+
      (T.layerPotential H m-T.layerPotential J m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih,T.layer_drop_split hHJ m,Finset.sum_range_succ]
    omega

/-- The unchanged raw marginal is exactly the number of crossed integer
excess levels, with each actual demand charged once at each level it crosses. -/
theorem raw_drop_eq_sum_layer_depletion {H J : Finset (V × V)} (hHJ : H ⊆ J) :
    T.potential H-T.potential J =
      ∑ k∈Finset.range (Fintype.card I),
        ((T.excessLayer H k).card-(T.excessLayer J k).card) := by
  have h := T.layer_drop_prefix hHJ (Fintype.card I)
  simpa only [T.layerPotential_zero,T.excess_drop_eq,T.layerPotential_at_chain_count,
    Nat.sub_self,Nat.add_zero] using h

end GreedyShortcuts.ChainDistance.Context
