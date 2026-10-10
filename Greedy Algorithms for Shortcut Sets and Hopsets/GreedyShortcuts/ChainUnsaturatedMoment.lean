import GreedyShortcuts.ChainUnsaturatedChoices
import GreedyShortcuts.ChainMomentProgress

/-! The same raw marginal moment, averaged over currently unsaturated choices.
The charge uses only unsaturated important edges; the raw algorithm is unchanged. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem unsaturated_legal (H : Finset (V × V)) : T.unsaturated H ⊆ candidates T.G := by
  classical
  intro e he
  obtain ⟨hp,hs⟩ := Finset.mem_filter.mp he
  have hne : e.1≠e.2 := by
    intro heq
    have hd := T.distance_le_walk H (reachable_refl T.G e.1)
      (SimpleGraph.Walk.nil : DWalk e.1 e.1) (allowed_nil _ _)
    have hf : T.count (SimpleGraph.Walk.nil : DWalk e.1 e.1)=T.endpointFloor e.1 e.1 := by
      simp [count,chainSet,endpointFloor]
    rw [← heq] at hs
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,(T.important_spec hp).1⟩

/-- One demand's cubic tail charges distinct actual important edge choices.
Small distances contribute zero, without discarding any raw marginal. -/
theorem pair_unsaturated_cubic_charge {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {s t : V} (hst : (s,t)∈T.important) :
    (T.distance H s t-3)^3 ≤ 32*∑ e∈T.unsaturated H,
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
    obtain ⟨sources,targets,hsc,htc,hsave⟩ := T.many_unsaturated_shortcut_choices hH hst k hk hL
    have hsub : sources ×ˢ targets ⊆ T.unsaturated H := by
      intro e he
      have hh := Finset.mem_product.mp he
      have hd := hsave e.1 hh.1 e.2 hh.2
      exact hd.2.1
    have hs : 2*k^3 ≤ ∑ e∈T.unsaturated H,
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
theorem step_unsaturated_cubic_moment (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    ∑ st∈T.important,(T.distance S.1 st.1 st.2-3)^3 ≤
      32*(T.unsaturated S.1).card*(T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by
  classical
  let A := T.algorithm D hD
  have hbadA : ¬A.stopped S.1 := hbad
  have hstep : T.potential (A.step S).1 =
      T.potential (insert (A.bestEdge S hbad).1 S.1) := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  have hb : ∀ e∈T.unsaturated S.1,T.potential S.1-T.potential (insert e S.1) ≤
      T.potential S.1-T.potential (A.step S).1 := by
    intro e he
    rw [hstep]
    exact A.bestEdge_max_drop S hbad e (T.unsaturated_legal S.1 he)
  calc
    _ ≤ ∑ st∈T.important,32*∑ e∈T.unsaturated S.1,
        (T.distance S.1 st.1 st.2-T.distance (insert e S.1) st.1 st.2) :=
      Finset.sum_le_sum (fun _ hst => T.pair_unsaturated_cubic_charge S.2 hst)
    _ = 32*∑ e∈T.unsaturated S.1,(T.potential S.1-T.potential (insert e S.1)) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro e he
      exact (T.potential_drop_sum S.1 e).symm
    _ ≤ 32*((T.unsaturated S.1).card*(T.potential S.1-T.potential (A.step S).1)) := by
      apply Nat.mul_le_mul_left
      exact (Finset.sum_le_sum hb).trans_eq (by simp)
    _ = _ := by ring

end GreedyShortcuts.ChainDistance.Context
