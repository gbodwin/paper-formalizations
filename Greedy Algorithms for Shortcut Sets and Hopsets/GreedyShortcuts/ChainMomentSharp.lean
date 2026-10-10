import GreedyShortcuts.ChainCubicPotential
import GreedyShortcuts.FiniteCubicDecay
import GreedyShortcuts.ChainQuadraticSharp

/-! A sharper unconditional finite stopping bound from cubic average decay.
The literal raw objective and maximum-distance stopping rule are unchanged. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem stopped_moment_sharp (D R : ℕ) (hD : 3≤D) (hR : 0<R)
    (hscale : R^3≤D^2) :
    T.stopped D ((T.algorithm D (by omega)).run (2*(256*T.important.card/R^2+1))).1 := by
  classical
  let A := T.algorithm D (by omega)
  change A.stopped (A.run (2*(256*T.important.card/R^2+1))).1
  have hcube : ∀ i,(A.livePotential i)^3 ≤ 256*T.important.card^3*
      (A.livePotential i-A.livePotential (i+1)) := by
    intro i
    by_cases hs : A.stopped (A.run i).1
    · simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_left hs,zero_pow (by decide : 3≠0),Nat.zero_le]
    · have hl : A.livePotential i=A.potential (A.run i).1 := by
        simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_right hs]
      rw [hl]
      exact (T.step_potential_cubed D (by omega) (A.run i) hs).trans
        (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (A.livePotential_le (i+1)) _))
  have hfloor : ∀ i,0<A.livePotential i →
      D^2≤25*(A.livePotential i-A.livePotential (i+1)) := by
    intro i hp
    have hs : ¬A.stopped (A.run i).1 := by
      intro h
      simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_left h] at hp
      omega
    have hl : A.livePotential i=A.potential (A.run i).1 := by
      simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_right hs]
    rw [hl]
    exact (T.step_squared_bounds D hD (A.run i) hs).2.trans
      (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (A.livePotential_le (i+1)) _))
  have hz := FinitePotential.zero_after_cubic_floor A.livePotential T.important.card D R
    hR hscale A.livePotential_antitone hcube hfloor
  by_contra hs
  have hp := A.step_potential_lt (A.run (2*(256*T.important.card/R^2+1))) hs
  simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_right hs] at hz
  omega

/-- No graph-progress premise is supplied: R is a numerical scale only. -/
theorem output_card_moment_sharp (D R : ℕ) (hD : 3≤D) (hR : 0<R)
    (hscale : R^3≤D^2) :
    (T.output D (by omega)).card ≤ 2*(256*(Fintype.card V*Fintype.card I)/R^2+1) := by
  have hstop := T.stopped_moment_sharp D R hD hR hscale
  have hc := (T.algorithm D (by omega)).final_card_of_stopped_at _ hstop
  have hnum := Nat.mul_le_mul_left 256 T.important_card
  exact hc.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right
    (Nat.div_le_div_right hnum) 1))

theorem shortcuts_card_moment_sharp (D R : ℕ) (hD : 3≤D) (hR : 0<R)
    (hscale : R^3≤D^2) :
    (T.shortcuts D (by omega)).card ≤ T.K*Fintype.card V+
      2*(256*(Fintype.card V*Fintype.card I)/R^2+1) := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (ChainNormalization.union_card_le T.chains T.disjoint T.witnesses)
    (T.output_card_moment_sharp D R hD hR hscale))

end GreedyShortcuts.ChainDistance.Context
