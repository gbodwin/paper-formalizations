import GreedyShortcuts.ChainCanonicalTraceSummation
import GreedyShortcuts.ChainGreedy

/-! SOURCE ONLY, UNCOMPILED. The FULL cap at an ACTUAL active raw-greedy
state is its own selected marginal, not a cap transported from another time.
A real attaining maximum important demand supplies a normalized trace caller.
This is a same-state record bound, not an incidence-to-insertion payment map. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The unchanged native bestEdge really dominates every legal edge at THIS
state. Its strict progress makes its own natural-subtraction marginal positive.
No supplied cap, future state or new maximum-choice rule occurs here. -/
theorem actualGreedyState_drop_cap (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1) :
    0<T.potential S.1-T.potential ((T.algorithm D hD).step S).1 ∧
      ∀ e∈candidates T.G,T.potential S.1-T.potential (insert e S.1)≤
        T.potential S.1-T.potential ((T.algorithm D hD).step S).1 := by
  let A := T.algorithm D hD
  have hbadA : ¬A.stopped S.1 := hbad
  have hstrict := A.step_potential_lt S hbadA
  change T.potential (A.step S).1<T.potential S.1 at hstrict
  refine ⟨Nat.sub_pos_of_lt hstrict,?_⟩
  intro e he
  have hstep : (A.step S).1=insert (A.bestEdge S hbadA).1 S.1 := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  change T.potential S.1-T.potential (insert e S.1)≤
    T.potential S.1-T.potential (A.step S).1
  rw [hstep]
  exact A.bestEdge_max_drop S hbadA e he

/-- ANY already fixed actual maximum important demand normalizes its own
root-head cone. ANY fixed permitted selector policy is retained literally.
The trace cap is derived from this actual state's selected greedy drop. -/
theorem greedy_maximum_canonical_budget (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1)
    {k : ℕ} (hk : 1≤k) (hscale : 16*k≤D) {root W : V}
    (hpair : (root,W)∈T.important) (hfar : D<T.distance S.1 root W)
    (hmax : ∀ st∈T.important,T.distance S.1 st.1 st.2≤T.distance S.1 root W)
    (policy : T.OriginalSelectorPolicy S.1 root k) :
    T.RootConeMaximizer S.1 root W W ∧
      ∃ Z,∃ tr : T.OriginalSelectorTrace S.1 root k W Z,
        T.originalTraceFollows policy tr ∧ T.originalTraceLinked tr ∧
        k≤T.distance S.1 root Z ∧ T.distance S.1 root Z<16*k ∧
        0<T.originalTraceLength tr ∧
        k*T.originalCanonicalTraceMarkerSum tr≤T.originalCanonicalTracePopulationLower tr ∧
        T.originalCanonicalTracePopulationLower tr≤T.originalCanonicalTraceWeight tr ∧
        T.originalCanonicalTraceWeight tr≤
          ((T.rootHeadCone root W).card-(T.rootHeadCone root Z).card-T.originalTraceLength tr)*
            (T.potential S.1-T.potential ((T.algorithm D hD).step S).1) ∧
        (T.originalTraceNonWCenters tr).card+T.originalTraceLength tr+
          (T.rootHeadCone root Z).card=(T.rootHeadCone root W).card := by
  have hW : T.RootConeMaximizer S.1 root W W := by
    refine ⟨T.rootCone_self_mem hpair,?_⟩
    intro v hv
    exact hmax (root,v) (T.mem_rootHeadCone_iff.mp hv).1
  have hactive : 16*k≤T.distance S.1 root W := by omega
  obtain ⟨Z,tr,hstop,hfollow⟩ :=
    T.exists_finite_original_history_with_policy S.2 hk policy hW
  obtain ⟨hlen,hfloor,_hstop,_hdrop,_hlower⟩ :=
    T.original_active_history_terminal_bounds S.2 hk hW hactive tr hstop
  have hcap := (T.actualGreedyState_drop_cap D hD S hbad).2
  obtain ⟨hcoef,hpop,hupper,hcenters⟩ := T.originalCanonicalTrace_sandwich S.2 hk tr hW
    (T.potential S.1-T.potential ((T.algorithm D hD).step S).1) hcap
  exact ⟨hW,Z,tr,hfollow,T.originalTrace_linked S.2 hk tr hW,
    hfloor,hstop,hlen,hcoef,hpop,hupper,hcenters⟩

/-- Genuine past-state caller: H is literally algorithm.run n, and the
attaining maximum is taken from its original important-demand set. No trace,
normalized endpoint, positive drop window or FULL cap is assumed as an oracle.
An already fixed permitted policy family may be passed for every possible root;
one exists from originalSelectorPolicy using the run state's actual legality. -/
theorem exists_run_maximum_canonical_budget (D : ℕ) (hD : 2≤D) (n : ℕ)
    (hbad : ¬T.stopped D ((T.algorithm D hD).run n).1)
    {k : ℕ} (hk : 1≤k) (hscale : 16*k≤D)
    (policy : ∀ root : V,T.OriginalSelectorPolicy ((T.algorithm D hD).run n).1 root k) :
    ∃ p∈T.important,
      (∀ st∈T.important,T.distance ((T.algorithm D hD).run n).1 st.1 st.2≤
        T.distance ((T.algorithm D hD).run n).1 p.1 p.2) ∧
      D<T.distance ((T.algorithm D hD).run n).1 p.1 p.2 ∧
      T.RootConeMaximizer ((T.algorithm D hD).run n).1 p.1 p.2 p.2 ∧
      ∃ Z,∃ tr : T.OriginalSelectorTrace ((T.algorithm D hD).run n).1 p.1 k p.2 Z,
        T.originalTraceFollows (policy p.1) tr ∧ T.originalTraceLinked tr ∧
        k≤T.distance ((T.algorithm D hD).run n).1 p.1 Z ∧
        T.distance ((T.algorithm D hD).run n).1 p.1 Z<16*k ∧
        0<T.originalTraceLength tr ∧
        k*T.originalCanonicalTraceMarkerSum tr≤T.originalCanonicalTracePopulationLower tr ∧
        T.originalCanonicalTracePopulationLower tr≤T.originalCanonicalTraceWeight tr ∧
        T.originalCanonicalTraceWeight tr≤
          ((T.rootHeadCone p.1 p.2).card-(T.rootHeadCone p.1 Z).card-T.originalTraceLength tr)*
            (T.potential ((T.algorithm D hD).run n).1-
              T.potential ((T.algorithm D hD).step ((T.algorithm D hD).run n)).1) ∧
        (T.originalTraceNonWCenters tr).card+T.originalTraceLength tr+
          (T.rootHeadCone p.1 Z).card=(T.rootHeadCone p.1 p.2).card := by
  classical
  let S := (T.algorithm D hD).run n
  have hex : ∃ st∈T.important,D<T.distance S.1 st.1 st.2 := by
    have hb := hbad
    simp only [stopped,not_forall,not_le] at hb
    obtain ⟨q,hq,hqfar⟩ := hb
    exact ⟨q,hq,hqfar⟩
  obtain ⟨st,hst,hfarst⟩ := hex
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image T.important
    (fun q => T.distance S.1 q.1 q.2) ⟨st,hst⟩
  have hfar : D<T.distance S.1 p.1 p.2 := hfarst.trans_le (hmax st hst)
  have hbudget := T.greedy_maximum_canonical_budget D hD S hbad hk hscale hp hfar hmax (policy p.1)
  exact ⟨p,hp,hmax,hfar,hbudget⟩

end GreedyShortcuts.ChainDistance.Context
