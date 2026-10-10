import GreedyShortcuts.ChainUnsaturatedPotential
import GreedyShortcuts.ChainExcessSharp
import GreedyShortcuts.FiniteCubicDecay

/-! An unsaturated-demand moment bound for the unchanged raw greedy.
The numerical R parameter supplies no graph-progress hypothesis. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Initially minimal rows never inflate this stopping-time coefficient.
The run and selected edges are still those of the original raw-sum system. -/
theorem stopped_unsaturated_moment (D R : ℕ) (hD : 3 ≤ D) (hR : 0<R) (hscale : R^3≤D^2) :
    T.stopped D ((T.algorithm D (by omega)).run (2*(256*(T.unsaturated ∅).card/R^2+1))).1 := by
  classical
  let A := T.algorithm D (by omega)
  let E := T.liveExcess D (by omega)
  have hcube : ∀ i,(E i)^3 ≤ 256*(T.unsaturated ∅).card^3*(E i-E (i+1)) := by
    intro i
    by_cases hs : T.stopped D (A.run i).1
    · dsimp only [A] at hs
      simp only [E,liveExcess,ite_eq_left hs,zero_pow (by decide : 3≠0),Nat.zero_le]
    · dsimp only [A] at hs
      have hl : E i=T.excessPotential (A.run i).1 := by
        simp only [E,liveExcess,A,ite_eq_right hs]
      rw [hl]
      exact (T.step_excess_cubed_initial D (by omega) (A.run i) hs).trans
        (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (T.liveExcess_le D (by omega) (i+1)) _))
  have hfloor : ∀ i,0 < E i → D^2 ≤ 25*(E i-E (i+1)) := by
    intro i hp
    have hs : ¬ T.stopped D (A.run i).1 := by
      intro hh
      dsimp only [A] at hh
      simp only [E,liveExcess,ite_eq_left hh] at hp
      omega
    dsimp only [A] at hs
    have hl : E i=T.excessPotential (A.run i).1 := by
      simp only [E,liveExcess,A,ite_eq_right hs]
    rw [hl]
    have hh := (T.step_squared_bounds D hD (A.run i) hs).2
    rw [← T.excess_drop_eq] at hh
    exact hh.trans (Nat.mul_le_mul_left _
      (Nat.sub_le_sub_left (T.liveExcess_le D (by omega) (i+1)) _))
  have hz := FinitePotential.zero_after_cubic_floor E (T.unsaturated ∅).card D R
    hR hscale (T.liveExcess_antitone D (by omega)) hcube hfloor
  by_contra hs
  have hp := A.step_potential_lt (A.run (2*(256*(T.unsaturated ∅).card/R^2+1))) hs
  change T.potential (A.step (A.run (2*(256*(T.unsaturated ∅).card/R^2+1)))).1 <
    T.potential (A.run (2*(256*(T.unsaturated ∅).card/R^2+1))).1 at hp
  rw [T.potential_eq_floor_add_excess,T.potential_eq_floor_add_excess] at hp
  simp only [E,liveExcess,ite_eq_right hs] at hz
  dsimp only [A] at hp
  omega

/-- A data-sensitive size bound for the same final greedy output. -/
theorem output_card_unsaturated_moment (D R : ℕ) (hD : 3 ≤ D) (hR : 0<R) (hscale : R^3≤D^2) :
    (T.output D (by omega)).card ≤ 2*(256*(T.unsaturated ∅).card/R^2+1) :=
  (T.algorithm D (by omega)).final_card_of_stopped_at _ (T.stopped_unsaturated_moment D R hD hR hscale)

end GreedyShortcuts.ChainDistance.Context
