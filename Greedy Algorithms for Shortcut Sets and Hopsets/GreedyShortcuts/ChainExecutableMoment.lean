import GreedyShortcuts.ChainExecutableGreedy
import GreedyShortcuts.ExecutableTraceBounds
import GreedyShortcuts.ChainMomentSharp

/-! The existing unconditional moment bound for the deterministic executable
raw-greedy output. This uses equality of one-step minimum values, never equality
of arbitrary tie-chosen states, and does not assert universal cubic progress. -/
namespace GreedyShortcuts.ChainExecutableGreedy
open Finset DirectedPaths ChainExecutableObjective FiniteExecutableGreedy
variable {n m : ℕ}
variable (T : ChainDistance.Context (Fin n) (Fin m))
  (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
  (D : ℕ) (hD : 3≤D)

private abbrev trace (k : ℕ) := run (choices edge) (potential T edge) (stopped T edge D) k

include he hD

/-- The executable output has the same proved moment-scale size guarantee,
without assuming its tie choices agree with the earlier canonical run. -/
theorem output_card_moment (R : ℕ) (hR : 0<R) (hscale : R^3≤D^2) :
    (output T edge D).card≤2*(256*(n*m)/R^2+1) := by
  classical
  let A := T.algorithm D (by omega)
  let impl := represents T edge he D (by omega)
  let H : ℕ → Finset (Fin n×Fin n) := trace T edge D
  have hlegal (i : ℕ) : H i⊆A.candidates := impl.run_legal i
  let P : ℕ → ℕ := fun i => if A.stopped (H i) then 0 else A.potential (H i)
  have hle (i : ℕ) : P i≤A.potential (H i) := by dsimp [P];split_ifs <;> omega
  have hstep (i : ℕ) : A.potential (H (i+1))=A.potential (A.step ⟨H i,hlegal i⟩).1 :=
    impl.step_potential_eq ⟨H i,hlegal i⟩
  have hpzero (i : ℕ) (hs : A.stopped (H i)) : P (i+1)=0 := by
    have hh : H (i+1)=H i := impl.step_of_stopped _ (hlegal i) hs
    simp only [P,hh,ite_eq_left hs]
  have hmono : Antitone P := by
    apply antitone_nat_of_succ_le
    intro i
    by_cases hs : A.stopped (H i)
    · rw [hpzero i hs]
      exact Nat.zero_le _
    · have hold : P i=A.potential (H i) := by simp only [P,ite_eq_right hs]
      rw [hold]
      exact (hle (i+1)).trans (by rw [hstep];exact A.step_potential_le ⟨H i,hlegal i⟩)
  have hcube (i : ℕ) : (P i)^3≤256*T.important.card^3*(P i-P (i+1)) := by
    by_cases hs : A.stopped (H i)
    · simp only [P,ite_eq_left hs,zero_pow (by decide : 3≠0),Nat.zero_le]
    · have hold : P i=T.potential (H i) := by
        simp only [P,ite_eq_right hs]
        rfl
      rw [hold]
      have hc := T.step_potential_cubed D (by omega) ⟨H i,hlegal i⟩ hs
      have hnext : P (i+1)≤T.potential (A.step ⟨H i,hlegal i⟩).1 := by
        have hn := hle (i+1)
        rw [hstep] at hn
        simpa only [A,ChainDistance.Context.algorithm] using hn
      exact hc.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hnext _))
  have hfloor (i : ℕ) (hp : 0<P i) : D^2≤25*(P i-P (i+1)) := by
    have hs : ¬A.stopped (H i) := by
      intro hs
      simp only [P,ite_eq_left hs] at hp
      omega
    have hold : P i=T.potential (H i) := by
        simp only [P,ite_eq_right hs]
        rfl
    rw [hold]
    have hf := (T.step_squared_bounds D hD ⟨H i,hlegal i⟩ hs).2
    have hnext : P (i+1)≤T.potential (A.step ⟨H i,hlegal i⟩).1 := by
      have hn := hle (i+1)
      rw [hstep] at hn
      simpa only [A,ChainDistance.Context.algorithm] using hn
    exact hf.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hnext _))
  let k := 2*(256*T.important.card/R^2+1)
  have hz : P k=0 := FinitePotential.zero_after_cubic_floor P T.important.card D R
    hR hscale hmono hcube hfloor
  have hs : A.stopped (H k) := by
    by_contra hs
    have hd := A.step_potential_lt ⟨H k,hlegal k⟩ hs
    simp only [P,ite_eq_right hs] at hz
    change A.potential (H k)=0 at hz
    change A.potential (A.step ⟨H k,hlegal k⟩).1<A.potential (H k) at hd
    omega
  have hc := impl.final_card_of_stopped_at k hs
  have hnum : T.important.card≤n*m := by simpa using T.important_card
  exact hc.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right
    (Nat.div_le_div_right (Nat.mul_le_mul_left 256 hnum)) 1))

theorem shortcuts_card_moment (R : ℕ) (hR : 0<R) (hscale : R^3≤D^2) :
    (T.base∪output T edge D).card≤T.K*n+2*(256*(n*m)/R^2+1) := by
  have hb : T.base.card≤T.K*n := by
    simpa only [ChainDistance.Context.base,Fintype.card_fin] using
      ChainNormalization.union_card_le T.chains T.disjoint T.witnesses
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hb
    (output_card_moment T edge he D hD R hR hscale))

end GreedyShortcuts.ChainExecutableGreedy
