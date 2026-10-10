import GreedyShortcuts.ChainQuadraticOutput
import GreedyShortcuts.FiniteQuadraticDecay

/-! Removing the logarithm from the weaker quadratic-derived size bound.
The original raw-potential greedy and stopping rule remain unchanged. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Two simultaneous consequences of the same actual maximum-distance pair
and the same raw greedy choice. -/
theorem step_squared_bounds (D : ℕ) (hD : 3≤D)
    (S : (T.algorithm D (by omega)).State) (hbad : ¬T.stopped D S.1) :
    (T.potential S.1)^2 ≤ 25*T.important.card^2*
      (T.potential S.1-T.potential ((T.algorithm D (by omega)).step S).1) ∧
    D^2 ≤ 25*(T.potential S.1-T.potential ((T.algorithm D (by omega)).step S).1) := by
  classical
  let A := T.algorithm D (by omega)
  have hb := hbad
  simp only [stopped,not_forall,not_le] at hb
  obtain ⟨st,hst,hfar⟩ := hb
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image T.important
    (fun st => T.distance S.1 st.1 st.2) ⟨st,hst⟩
  let L := T.distance S.1 m.1 m.2
  have hlarge : 4≤L := by have := hmax st hst;dsimp [L];omega
  obtain ⟨e,he,hdrop⟩ := T.exists_quadratic_drop_for_pair S.2 hm hlarge
  have hbest := A.bestEdge_max_drop S hbad e he
  have hbadA : ¬A.stopped S.1 := hbad
  have hstep : T.potential (A.step S).1 =
      T.potential (insert (A.bestEdge S hbad).1 S.1) := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  have hquad : L^2≤25*(T.potential S.1-T.potential (A.step S).1) := by
    rw [hstep]
    exact hdrop.trans (Nat.mul_le_mul_left 25 hbest)
  have hphi : T.potential S.1≤T.important.card*L := by
    calc
      _ ≤ ∑ _st ∈ T.important,L := Finset.sum_le_sum (fun st hst => hmax st hst)
      _ = _ := by simp
  have hDL : D≤L := by have := hmax st hst;dsimp [L];omega
  constructor
  · have hs := Nat.mul_self_le_mul_self hphi
    have hq := Nat.mul_le_mul_left (T.important.card^2) hquad
    nlinarith
  · exact (Nat.pow_le_pow_left hDL 2).trans hquad

/-- Actual stopping after two rounded reciprocal-decay blocks. -/
theorem stopped_quadratic_sharp (D : ℕ) (hD : 3≤D) :
    T.stopped D ((T.algorithm D (by omega)).run (2*(25*T.important.card/D+1))).1 := by
  classical
  let A := T.algorithm D (by omega)
  change A.stopped (A.run (2*(25*T.important.card/D+1))).1
  have hquad : ∀ i,(A.livePotential i)^2 ≤ 25*T.important.card^2*
      (A.livePotential i-A.livePotential (i+1)) := by
    intro i
    by_cases hs : A.stopped (A.run i).1
    · simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_left hs,pow_two,Nat.mul_zero,Nat.zero_le]
    · have hl : A.livePotential i=A.potential (A.run i).1 := by
        simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_right hs]
      rw [hl]
      exact (T.step_squared_bounds D hD (A.run i) hs).1.trans
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
  have hz := FinitePotential.zero_after_quadratic A.livePotential T.important.card D
    (by omega) A.livePotential_antitone hquad hfloor
  by_contra hs
  have hp := A.step_potential_lt (A.run (2*(25*T.important.card/D+1))) hs
  simp only [FiniteThresholdGreedy.System.livePotential,ite_eq_right hs] at hz
  omega

/-- No logarithmic factor or caller-supplied progress premise remains. -/
theorem output_card_quadratic_sharp (D : ℕ) (hD : 3≤D) :
    (T.output D (by omega)).card ≤ 2*(25*(Fintype.card V*Fintype.card I)/D+1) := by
  have hstop := T.stopped_quadratic_sharp D hD
  have hc := (T.algorithm D (by omega)).final_card_of_stopped_at _ hstop
  have hnum := Nat.mul_le_mul_left 25 T.important_card
  exact hc.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right
    (Nat.div_le_div_right hnum) 1))

theorem shortcuts_card_quadratic_sharp (D : ℕ) (hD : 3≤D) :
    (T.shortcuts D (by omega)).card ≤ T.K*Fintype.card V+
      2*(25*(Fintype.card V*Fintype.card I)/D+1) := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (ChainNormalization.union_card_le T.chains T.disjoint T.witnesses)
    (T.output_card_quadratic_sharp D hD))

/-- The same full output has K*n+100*n*r+2 edges and 7*r+4 ordinary hops
at the supplied integer cover scale. This remains weaker than linear size. -/
theorem quadratic_scaled_output_sharp (r : ℕ) (hr : 3≤r)
    (hcover : IsCover T r) (hI : Fintype.card I≤2*r^2) :
    (T.shortcuts r (by omega)).card ≤ T.K*Fintype.card V+100*Fintype.card V*r+2 ∧
    ∀ s t,Reachable T.G s t → ∃ q : DWalk s t,
      Allowed (augment T.G (T.shortcuts r (by omega))) q ∧ q.length≤7*r+4 := by
  have hnum : 25*(Fintype.card V*Fintype.card I)≤(50*Fintype.card V*r)*r := by
    nlinarith [Nat.mul_le_mul_left (25*Fintype.card V) hI]
  have hdiv : 25*(Fintype.card V*Fintype.card I)/r≤50*Fintype.card V*r := by
    simpa only [Nat.mul_div_cancel _ (by omega : 0<r)] using Nat.div_le_div_right (c:=r) hnum
  constructor
  · have hc := T.shortcuts_card_quadratic_sharp r hr
    nlinarith
  · intro s t hst
    obtain ⟨q,hq,hlen⟩ := T.shortcuts_hop_bound hcover r (by omega) hst
    exact ⟨q,hq,by omega⟩

end GreedyShortcuts.ChainDistance.Context
