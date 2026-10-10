import GreedyShortcuts.ChainMomentProgress
import Mathlib.Algebra.Order.Chebyshev

/-! A cubic recurrence for the actual raw potential at active states. This is
an averaged recurrence, not the missing cube of the maximum distance. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem cube_le_tail_cube (d : ℕ) : d^3≤108+4*(d-3)^3 := by
  have hd : d≤3+(d-3) := by omega
  have hp := Nat.pow_le_pow_left hd 3
  have hs := add_pow_le (show (0:ℕ)≤3 by omega) (Nat.zero_le (d-3)) 3
  norm_num at hs
  nlinarith

/-- The literal raw objective satisfies cubic average decay whenever active.
The constant baseline is absorbed using actual strict positive progress. -/
theorem step_potential_cubed (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    (T.potential S.1)^3 ≤ 256*T.important.card^3*
      (T.potential S.1-T.potential ((T.algorithm D hD).step S).1) := by
  classical
  let A := T.algorithm D hD
  let M := T.important.card
  let Δ := T.potential S.1-T.potential (A.step S).1
  have hpos : 1≤Δ := by
    have hp := A.step_potential_lt S hbad
    dsimp only [Δ,A]
    change T.potential ((T.algorithm D hD).step S).1<T.potential S.1 at hp
    omega
  have ht := T.step_cubic_moment D hD S hbad
  have hs : ∑ st∈T.important,(T.distance S.1 st.1 st.2)^3 ≤
      108*M+4*∑ st∈T.important,(T.distance S.1 st.1 st.2-3)^3 := by
    calc
      _ ≤ ∑ st∈T.important,(108+4*(T.distance S.1 st.1 st.2-3)^3) :=
        Finset.sum_le_sum (fun st _ => cube_le_tail_cube _)
      _ = _ := by simp [M,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]
  have hb : ∑ st∈T.important,(T.distance S.1 st.1 st.2)^3 ≤ 256*M*Δ := by
    change _ ≤ 32*M*Δ at ht
    have hh := Nat.mul_le_mul_left (108*M) hpos
    nlinarith
  have hj := pow_sum_le_card_mul_sum_pow (s := T.important)
    (f := fun st => T.distance S.1 st.1 st.2) (fun _ _ => Nat.zero_le _) 2
  have hm := Nat.mul_le_mul_left (M^2) hb
  change (T.potential S.1)^3≤M^2*∑ st∈T.important,(T.distance S.1 st.1 st.2)^3 at hj
  change _ ≤256*M^3*Δ
  nlinarith

end GreedyShortcuts.ChainDistance.Context
