import GreedyShortcuts.ChainUnsaturatedMoment
import Mathlib.Algebra.Order.Chebyshev

/-! A cubic recurrence for the exact excess account of the same raw greedy.
Its coefficient counts only currently unsaturated important demands. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem excess_cube_le_tail (d f : ℕ) : (d-f)^3≤108+4*(d-3)^3 := by
  have hd : d≤3+(d-3) := by omega
  have hp := Nat.pow_le_pow_left hd 3
  have hs := add_pow_le (show (0:ℕ)≤3 by omega) (Nat.zero_le (d-3)) 3
  have he := Nat.pow_le_pow_left (Nat.sub_le d f) 3
  norm_num at hs
  nlinarith

/-- Endpoint-floor removal preserves every raw marginal exactly. -/
theorem step_excess_cubed (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    (T.excessPotential S.1)^3 ≤256*(T.unsaturated S.1).card^3*
      (T.excessPotential S.1-T.excessPotential ((T.algorithm D hD).step S).1) := by
  classical
  let A := T.algorithm D hD
  let U := (T.unsaturated S.1).card
  let Δ := T.potential S.1-T.potential (A.step S).1
  have hpos : 1≤Δ := by
    have hp := A.step_potential_lt S hbad
    dsimp only [Δ,A]
    change T.potential ((T.algorithm D hD).step S).1<T.potential S.1 at hp
    omega
  have ht := T.step_unsaturated_cubic_moment D hD S hbad
  have htail : ∑ st∈T.unsaturated S.1,(T.distance S.1 st.1 st.2-3)^3 ≤
      ∑ st∈T.important,(T.distance S.1 st.1 st.2-3)^3 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hs : ∑ st∈T.unsaturated S.1,
      (T.distance S.1 st.1 st.2-T.endpointFloor st.1 st.2)^3 ≤
      108*U+4*∑ st∈T.unsaturated S.1,(T.distance S.1 st.1 st.2-3)^3 := by
    calc
      _ ≤ ∑ st∈T.unsaturated S.1,(108+4*(T.distance S.1 st.1 st.2-3)^3) :=
        Finset.sum_le_sum (fun st _ => excess_cube_le_tail _ _)
      _ = _ := by simp [U,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]
  have hb : ∑ st∈T.unsaturated S.1,
      (T.distance S.1 st.1 st.2-T.endpointFloor st.1 st.2)^3 ≤256*U*Δ := by
    change _ ≤32*U*Δ at ht
    have hh := Nat.mul_le_mul_left (108*U) hpos
    nlinarith
  have hj := pow_sum_le_card_mul_sum_pow (s := T.unsaturated S.1)
    (f := fun st => T.distance S.1 st.1 st.2-T.endpointFloor st.1 st.2)
    (fun _ _ => Nat.zero_le _) 2
  rw [←T.excess_eq_sum_unsaturated S.1] at hj
  have hm := Nat.mul_le_mul_left (U^2) hb
  rw [T.excess_drop_eq]
  change _ ≤256*U^3*Δ
  change (T.excessPotential S.1)^3≤U^2*∑ st∈T.unsaturated S.1,
    (T.distance S.1 st.1 st.2-T.endpointFloor st.1 st.2)^3 at hj
  nlinarith

/-- A uniform coefficient for the original run, including U=0. -/
theorem step_excess_cubed_initial (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    (T.excessPotential S.1)^3 ≤256*(T.unsaturated ∅).card^3*
      (T.excessPotential S.1-T.excessPotential ((T.algorithm D hD).step S).1) := by
  have hu := Finset.card_le_card (T.unsaturated_antitone (Finset.empty_subset S.1))
  exact (T.step_excess_cubed D hD S hbad).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hu 3)))

end GreedyShortcuts.ChainDistance.Context
