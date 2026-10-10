import GreedyShortcuts.ChainShortcutChoices
import GreedyShortcuts.ChainGreedy

/-! Dense-demand cubic moment progress for the unchanged raw greedy.
The averaging choices are actual important pairs, not all n² vertex pairs.
This does not imply a cubic saving from one long demand alone. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def importantChoices : Finset (V × V) := by
  classical
  exact T.important.filter (fun e => e.1≠e.2)

theorem importantChoices_legal : T.importantChoices ⊆ candidates T.G := by
  classical
  intro e he
  obtain ⟨hp,hne⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,(T.important_spec hp).1⟩

theorem importantChoices_card : T.importantChoices.card ≤ T.important.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- One demand's cubic tail charges distinct actual important edge choices.
Small distances contribute zero, without discarding any raw marginal. -/
theorem pair_cubic_choice_charge {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {s t : V} (hst : (s,t)∈T.important) :
    (T.distance H s t-3)^3 ≤ 32*∑ e∈T.importantChoices,
      (T.distance H s t-T.distance (insert e H) s t) := by
  classical
  let L := T.distance H s t
  by_cases hsmall : L<4
  · have hz : T.distance H s t-3=0 := by dsimp [L] at hsmall;omega
    rw [hz]
    simp only [zero_pow (by decide : 3≠0),Nat.zero_le]
  · let k := L/4
    have hk : 0<k := by dsimp [k];omega
    have hL : 4*k≤T.distance H s t := by change 4*(L/4)≤L;omega
    obtain ⟨sources,targets,hsc,htc,hsave⟩ := T.many_important_shortcut_choices hH hst k hk hL
    have hsub : sources ×ˢ targets ⊆ T.importantChoices := by
      intro e he
      have hh := Finset.mem_product.mp he
      have hd := hsave e.1 hh.1 e.2 hh.2
      exact Finset.mem_filter.mpr ⟨hd.2.1,(Finset.mem_filter.mp hd.1).2.1⟩
    have hs : 2*k^3 ≤ ∑ e∈T.importantChoices,
        (T.distance H s t-T.distance (insert e H) s t) := by
      calc
        _ = ∑ _e∈sources ×ˢ targets,2*k := by simp [hsc,htc];ring
        _ ≤ ∑ e∈sources ×ˢ targets,
            (T.distance H s t-T.distance (insert e H) s t) := by
          apply Finset.sum_le_sum
          intro e he
          have hh := Finset.mem_product.mp he
          exact (hsave e.1 hh.1 e.2 hh.2).2.2
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    have htail : L-3≤4*k := by dsimp [k];omega
    have hp := Nat.pow_le_pow_left htail 3
    change (L-3)^3≤_
    nlinarith

/-- The exact raw minimizer dominates a cubic moment averaged over the
important-choice set. One long demand yields a diluted, not universal, cube. -/
theorem step_cubic_moment (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    ∑ st∈T.important,(T.distance S.1 st.1 st.2-3)^3 ≤
      32*T.important.card*(T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by
  classical
  let A := T.algorithm D hD
  have hbadA : ¬A.stopped S.1 := hbad
  have hstep : T.potential (A.step S).1 =
      T.potential (insert (A.bestEdge S hbad).1 S.1) := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  have hb : ∀ e∈T.importantChoices,T.potential S.1-T.potential (insert e S.1) ≤
      T.potential S.1-T.potential (A.step S).1 := by
    intro e he
    rw [hstep]
    exact A.bestEdge_max_drop S hbad e (T.importantChoices_legal he)
  calc
    _ ≤ ∑ st∈T.important,32*∑ e∈T.importantChoices,
        (T.distance S.1 st.1 st.2-T.distance (insert e S.1) st.1 st.2) :=
      Finset.sum_le_sum (fun _ hst => T.pair_cubic_choice_charge S.2 hst)
    _ = 32*∑ e∈T.importantChoices,(T.potential S.1-T.potential (insert e S.1)) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro e he
      exact (T.potential_drop_sum S.1 e).symm
    _ ≤ 32*(T.importantChoices.card*(T.potential S.1-T.potential (A.step S).1)) := by
      apply Nat.mul_le_mul_left
      exact (Finset.sum_le_sum hb).trans_eq (by simp)
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (T.potential S.1-T.potential (A.step S).1)
        T.importantChoices_card
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 32 hh

noncomputable def farDemands (H : Finset (V × V)) (L : ℕ) : Finset (V × V) := by
  classical
  exact T.important.filter (fun st => L≤T.distance H st.1 st.2)

/-- A density-sensitive cubic saving, with the exact long-demand count. -/
theorem step_far_demand_bound (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) (L : ℕ) :
    (T.farDemands S.1 L).card*(L-3)^3 ≤
      32*T.important.card*(T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by
  classical
  calc
    _ = ∑ _st∈T.farDemands S.1 L,(L-3)^3 := by simp
    _ ≤ ∑ st∈T.farDemands S.1 L,(T.distance S.1 st.1 st.2-3)^3 := by
      apply Finset.sum_le_sum
      intro st hst
      exact Nat.pow_le_pow_left (Nat.sub_le_sub_right (Finset.mem_filter.mp hst).2 3) 3
    _ ≤ ∑ st∈T.important,(T.distance S.1 st.1 st.2-3)^3 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := T.step_cubic_moment D hD S hbad

/-- A fixed fraction of long demands recovers a genuine cubic scale. The
fraction premise is explicit; one longest demand does not discharge it. -/
theorem step_dense_cubic (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) (L q : ℕ)
    (hpos : 0<(T.farDemands S.1 L).card)
    (hdense : T.important.card≤q*(T.farDemands S.1 L).card) :
    (L-3)^3 ≤ 32*q*(T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by
  have h := T.step_far_demand_bound D hD S hbad L
  have hh : (T.farDemands S.1 L).card*(L-3)^3 ≤
      (T.farDemands S.1 L).card*
        (32*q*(T.potential S.1-T.potential ((T.algorithm D hD).step S).1)) := by
    calc
      _ ≤ _ := h
      _ ≤ 32*(q*(T.farDemands S.1 L).card)*
          (T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh hpos

end GreedyShortcuts.ChainDistance.Context
