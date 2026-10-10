import GreedyShortcuts.ChainQuadraticProgress
import GreedyShortcuts.ChainGreedy

/-! Instantiating a relative rate for the actual raw-sum chain greedy.
The rate is quadratic-derived; no cubic or near-linear bound is assumed. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem step_relative_progress (D : ℕ) (hD : 3 ≤ D)
    (S : (T.algorithm D (by omega)).State)
    (hbad : ¬ T.stopped D S.1) :
    T.potential S.1 ≤ (25*T.important.card/D+1)*
      (T.potential S.1-T.potential ((T.algorithm D (by omega)).step S).1) := by
  classical
  let A := T.algorithm D (by omega)
  have hex : ∃ st ∈ T.important,D < T.distance S.1 st.1 st.2 := by
    have hb := hbad
    simp only [stopped,not_forall,not_le] at hb
    obtain ⟨st,hst,hfar⟩ := hb
    exact ⟨st,hst,hfar⟩
  obtain ⟨st,hst,hfar⟩ := hex
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
  have hphi : T.potential S.1 ≤ T.important.card*L := by
    calc
      _ ≤ ∑ _st ∈ T.important,L := Finset.sum_le_sum (fun st hst => hmax st hst)
      _ = _ := by simp
  have hDL : D ≤ L := by have := hmax st hst;dsimp [L];omega
  have hDLphi : D*T.potential S.1 ≤ 25*T.important.card*
      (T.potential S.1-T.potential (A.step S).1) := by
    calc
      _ ≤ D*(T.important.card*L) := Nat.mul_le_mul_left D hphi
      _ ≤ T.important.card*L^2 := by nlinarith [Nat.mul_le_mul_left (T.important.card*L) hDL]
      _ ≤ _ := by nlinarith [Nat.mul_le_mul_left T.important.card hquad]
  have hceil : 25*T.important.card ≤ (25*T.important.card/D+1)*D := by
    have := Nat.mod_lt (25*T.important.card) (by omega : 0 < D)
    have := Nat.mod_add_div (25*T.important.card) D
    nlinarith
  have hscaled := hDLphi.trans (Nat.mul_le_mul_right
    (T.potential S.1-T.potential (A.step S).1) hceil)
  exact Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hscaled) (by omega : 0 < D)

end GreedyShortcuts.ChainDistance.Context
