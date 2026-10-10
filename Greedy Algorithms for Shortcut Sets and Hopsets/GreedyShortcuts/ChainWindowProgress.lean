import GreedyShortcuts.ChainStableRectangle
import GreedyShortcuts.ChainGreedy

/-! Explicit cone-sensitive progress from actual guard descent and the
constructed stable-path rectangle. The universal cubic claim remains open. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem exists_window_drop_for_pair {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (L k : ℕ)
    (hL : 0<L) (hk : 0<k) (hdist : L≤T.distance H s t)
    (hscale : 64*(T.coneChains s t).card*k≤L^2) :
    ∃ e ∈ candidates T.G,2*k^3≤T.potential H-T.potential (insert e H) := by
  obtain ⟨z,hz,_,hlong,hgood⟩ := T.exists_stable_window_target hH hst L k hL hk hdist hscale
  obtain ⟨p,hp,hmin⟩ := T.distance_spec H (T.important_spec hz).1
  have hLK : L≤(T.coneChains s t).card := by
    obtain ⟨q,hq,hqc⟩ := T.distance_spec H (T.important_spec hst).1
    have hc := Finset.card_le_card (T.chainSet_subset_cone hH q hq)
    change T.count q≤_ at hc
    omega
  have hkL : 64*k≤L := by
    have hm := Nat.mul_le_mul_right (64*k) hLK
    nlinarith
  exact T.stable_path_rectangle hH p hp hmin k hk (by omega) hgood

/-- An exact natural-number form of the cone-sensitive L^6/K^3 bound.
The cone is defined from the original graph and fixed source, not supplied. -/
theorem exists_sixth_power_drop_for_pair {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (L : ℕ)
    (hL : 0<L) (hdist : L≤T.distance H s t)
    (hscale : 128*(T.coneChains s t).card≤L^2) :
    ∃ e ∈ candidates T.G,L^6≤1048576*(T.coneChains s t).card^3*
      (T.potential H-T.potential (insert e H)) := by
  let K := (T.coneChains s t).card
  have hLK : L≤K := by
    obtain ⟨p,hp,hpc⟩ := T.distance_spec H (T.important_spec hst).1
    have hc := Finset.card_le_card (T.chainSet_subset_cone hH p hp)
    change T.count p≤K at hc
    omega
  have hK : 0<K := by omega
  let k := L^2/(64*K)
  have hk : 0<k := Nat.div_pos (by dsimp [K];omega) (by omega)
  have hkbound : 64*K*k≤L^2 := by
    calc
      64*K*k=k*(64*K) := Nat.mul_comm _ _
      _≤L^2 := Nat.div_mul_le_self (L^2) (64*K)
  obtain ⟨e,he,hdrop⟩ := T.exists_window_drop_for_pair hH hst L k hL hk hdist hkbound
  have hbound : L^2≤128*K*k := by
    have hrem := Nat.mod_lt (L^2) (by omega : 0<64*K)
    have hdiv := Nat.mod_add_div (L^2) (64*K)
    change L^2%(64*K)+64*K*k=L^2 at hdiv
    have hm := Nat.mul_le_mul_left (64*K) (show 1≤k by omega)
    nlinarith
  have hcube := Nat.pow_le_pow_left hbound 3
  have hmul := Nat.mul_le_mul_left (1048576*K^3) hdrop
  refine ⟨e,he,?_⟩
  change L^6≤1048576*K^3*(T.potential H-T.potential (insert e H))
  calc
    L^6=(L^2)^3 := by ring
    _≤(128*K*k)^3 := hcube
    _=1048576*K^3*(2*k^3) := by ring
    _≤1048576*K^3*(T.potential H-T.potential (insert e H)) := hmul

/-- The literal raw-potential minimizer earns the constructed window saving
whenever its separate stopping predicate is false. -/
theorem step_window_drop (D : ℕ) (hD : 2≤D)
    (S : (T.algorithm D hD).State) (hbad : ¬T.stopped D S.1)
    {s t : V} (hst : (s,t) ∈ T.important) (L k : ℕ)
    (hL : 0<L) (hk : 0<k) (hdist : L≤T.distance S.1 s t)
    (hscale : 64*(T.coneChains s t).card*k≤L^2) :
    2*k^3≤T.potential S.1-T.potential ((T.algorithm D hD).step S).1 := by
  classical
  let A := T.algorithm D hD
  obtain ⟨e,he,hd⟩ := T.exists_window_drop_for_pair S.2 hst L k hL hk hdist hscale
  have hbest := A.bestEdge_max_drop S hbad e he
  have hbadA : ¬A.stopped S.1 := hbad
  have hstep : T.potential (A.step S).1=
      T.potential (insert (A.bestEdge S hbad).1 S.1) := by
    simp only [FiniteThresholdGreedy.System.step,dite_eq_left hbadA]
  change 2*k^3≤T.potential S.1-T.potential (A.step S).1
  rw [hstep]
  exact hd.trans hbest

end GreedyShortcuts.ChainDistance.Context
