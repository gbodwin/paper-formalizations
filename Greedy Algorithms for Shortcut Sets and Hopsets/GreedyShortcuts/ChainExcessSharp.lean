import GreedyShortcuts.ChainExcessPotential
import GreedyShortcuts.ChainQuadraticSharp

/-! A data-sensitive refinement for the same literal raw-potential greedy.
The coefficient counts only initially unsaturated demands. This remains a
quadratic-derived bound, not the open universal cubic progress theorem. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem step_excess_squared (D : ℕ) (hD : 3 ≤ D)
    (S : (T.algorithm D (by omega)).State) (hbad : ¬ T.stopped D S.1) :
    (T.excessPotential S.1)^2 ≤ 25*(T.unsaturated ∅).card^2*
      (T.excessPotential S.1-T.excessPotential ((T.algorithm D (by omega)).step S).1) := by
  classical
  let A := T.algorithm D (by omega)
  have hb := hbad
  simp only [stopped,not_forall,not_le] at hb
  obtain ⟨st,hst,hfar⟩ := hb
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image T.important
    (fun st => T.distance S.1 st.1 st.2) ⟨st,hst⟩
  let L := T.distance S.1 m.1 m.2
  have hlarge : 4 ≤ L := by have := hmax st hst;dsimp [L];omega
  obtain ⟨e,he,hdrop⟩ := T.exists_quadratic_drop_for_pair S.2 hm hlarge
  have hbest := A.bestEdge_max_drop S hbad e he
  have hbadA : ¬ A.stopped S.1 := hbad
  have hstep : T.potential (A.step S).1 =
      T.potential (insert (A.bestEdge S hbad).1 S.1) := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  have hquad : L^2 ≤ 25*(T.potential S.1-T.potential (A.step S).1) := by
    rw [hstep]
    exact hdrop.trans (Nat.mul_le_mul_left 25 hbest)
  have hphi := T.excess_le_initial_card_mul S.1 L hmax
  have hs := Nat.mul_self_le_mul_self hphi
  have hq := Nat.mul_le_mul_left ((T.unsaturated ∅).card^2) hquad
  rw [T.excess_drop_eq]
  nlinarith

noncomputable def liveExcess (D : ℕ) (hD : 2 ≤ D) (i : ℕ) : ℕ := by
  classical
  exact if T.stopped D ((T.algorithm D hD).run i).1 then 0 else
    T.excessPotential ((T.algorithm D hD).run i).1

theorem liveExcess_le (D : ℕ) (hD : 2 ≤ D) (i : ℕ) :
    T.liveExcess D hD i ≤ T.excessPotential ((T.algorithm D hD).run i).1 := by
  classical
  unfold liveExcess
  split_ifs <;> omega

theorem liveExcess_antitone (D : ℕ) (hD : 2 ≤ D) : Antitone (T.liveExcess D hD) := by
  classical
  apply antitone_nat_of_succ_le
  intro i
  let A := T.algorithm D hD
  by_cases hs : T.stopped D (A.run i).1
  · have hn : T.stopped D (A.run (i+1)).1 := by
      rw [A.run_succ,A.step_of_stopped _ hs]
      exact hs
    dsimp only [A] at hs hn
    simp only [liveExcess,ite_eq_left hs,ite_eq_left hn,Nat.le_refl]
  · dsimp only [A] at hs
    have hl : T.liveExcess D hD i=T.excessPotential (A.run i).1 := by
      simp only [liveExcess,A,ite_eq_right hs]
    rw [hl]
    exact (T.liveExcess_le D hD (i+1)).trans
      (T.excessPotential_antitone (A.subset_step (A.run i)))

/-- Initially minimal rows never inflate this stopping-time coefficient.
The run and selected edges are still those of the original raw-sum system. -/
theorem stopped_unsaturated_sharp (D : ℕ) (hD : 3 ≤ D) :
    T.stopped D ((T.algorithm D (by omega)).run (2*(25*(T.unsaturated ∅).card/D+1))).1 := by
  classical
  let A := T.algorithm D (by omega)
  let E := T.liveExcess D (by omega)
  have hquad : ∀ i,(E i)^2 ≤ 25*(T.unsaturated ∅).card^2*(E i-E (i+1)) := by
    intro i
    by_cases hs : T.stopped D (A.run i).1
    · dsimp only [A] at hs
      simp only [E,liveExcess,ite_eq_left hs,pow_two,Nat.mul_zero,Nat.zero_le]
    · dsimp only [A] at hs
      have hl : E i=T.excessPotential (A.run i).1 := by
        simp only [E,liveExcess,A,ite_eq_right hs]
      rw [hl]
      exact (T.step_excess_squared D hD (A.run i) hs).trans
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
  have hz := FinitePotential.zero_after_quadratic E (T.unsaturated ∅).card D
    (by omega) (T.liveExcess_antitone D (by omega)) hquad hfloor
  by_contra hs
  have hp := A.step_potential_lt (A.run (2*(25*(T.unsaturated ∅).card/D+1))) hs
  change T.potential (A.step (A.run (2*(25*(T.unsaturated ∅).card/D+1)))).1 <
    T.potential (A.run (2*(25*(T.unsaturated ∅).card/D+1))).1 at hp
  rw [T.potential_eq_floor_add_excess,T.potential_eq_floor_add_excess] at hp
  simp only [E,liveExcess,ite_eq_right hs] at hz
  dsimp only [A] at hp
  omega

/-- A data-sensitive size bound for the same final greedy output. -/
theorem output_card_unsaturated_sharp (D : ℕ) (hD : 3 ≤ D) :
    (T.output D (by omega)).card ≤ 2*(25*(T.unsaturated ∅).card/D+1) :=
  (T.algorithm D (by omega)).final_card_of_stopped_at _ (T.stopped_unsaturated_sharp D hD)

end GreedyShortcuts.ChainDistance.Context
