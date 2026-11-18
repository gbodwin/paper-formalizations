import OnlineReachabilityPreservers.OfflineBound
import OnlineReachabilityPreservers.OfflineIndependence

/-! The Appendix B graph application with the rounded paper exponents. -/

namespace OnlineReachabilityPreservers

open Finset

universe u

section Graph

variable {V : Type u} [LinearOrder V] [Fintype V]

private theorem offlinePrune_rate {b B : ℝ} (prior : OfflineIncidenceBound.{u,0} b B)
    {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    ((offlinePrune G D).card : ℝ) ≤ B*offlineRate b (Fintype.card V) D.length := by
  let H := offlinePrune G D
  let paths := topologicalPaths H (criticalCompressed H D)
  let W := Set.range (reverseTopologicalKey H)
  let : Fintype (Set.range (reverseTopologicalKey H)) := Fintype.ofEquiv V (topologicalEquiv H)
  obtain ⟨_, _, count, free⟩ := theorem14_dag_compression dag D
  have h := prior W (Fin D.length) paths (free 4)
  change (∑ i : Fin D.length, (paths i).card) = H.card + D.length at count
  rw [← Nat.cast_sum, count, ← Fintype.card_congr (topologicalEquiv H), Fintype.card_fin] at h
  calc
    _ ≤ ((H.card + D.length : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_right H.card D.length)
    _ ≤ _ := h.trans_eq (mul_comm _ _)

private theorem offlinePreserver_rate {b B : ℝ} (prior : OfflineIncidenceBound.{u,0} b B)
    (G : Arcs V) (D : List (V × V)) :
    let H := offlinePreserver G D
    H ⊆ G ∧ Preserves G H D ∧
      (H.card : ℝ) ≤ (B+2)*offlineRate b (Fintype.card V) D.length := by
  obtain ⟨sub, correct, overhead⟩ := theorem9_lift offlinePrune G D
    (fun K _ P => (offlinePrune_spec K P).1) (fun K _ P => (offlinePrune_spec K P).2)
  have bound := offlinePrune_rate prior (condensation_dag G) (D.map (projectDemand G))
  rw [List.length_map] at bound
  let H := offlinePreserver G D
  let n := Fintype.card V
  let F := offlineRate b (n:ℝ) D.length
  have hN : (n:ℝ) ≤ F := le_max_left _ _
  have e : (H.card : ℝ) ≤ (offlinePrune (condensation G) (D.map (projectDemand G))).card + 2*n := by
    exact_mod_cast overhead
  exact ⟨sub, correct, by nlinarith only [e, bound, hN]⟩

end Graph

private theorem demand_term_le_mixed {b n p : ℝ} (hb : b ≤ 1) (hn : 0 ≤ n)
    (hp : 0 < p) (hpn : p ≤ n^2) : p ≤ n^(2-2*b)*p^b := by
  have h := Real.rpow_le_rpow hp.le hpn (sub_nonneg.mpr hb)
  rw [← Real.rpow_natCast_mul hn 2] at h
  calc
    p = p^(1-b)*p^b := by rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
    _ ≤ n^(2*(1-b))*p^b := by push_cast at h; exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [show (2:ℝ)*(1-b)=2-2*b by ring]

private theorem offline_rounded_rate {n p : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n^2) :
    offlineRate (12/17) n p ≤ n+n^(3/4:ℝ)*p^(1/2:ℝ)+n^(59/100:ℝ)*p^(71/100:ℝ) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have mixed : n^(2-2*(12/17:ℝ))*p^(12/17:ℝ) ≤ n^(59/100:ℝ)*p^(71/100:ℝ) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hp (by norm_num)) (by positivity) (by positivity)
  have dem := demand_term_le_mixed (b := 12/17) (by norm_num) hn0 hp0 hpn
  have hF : 0 ≤ n^(3/4:ℝ)*p^(1/2:ℝ) := by positivity
  have hG : 0 ≤ n^(59/100:ℝ)*p^(71/100:ℝ) := by positivity
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

private theorem offline_rounded_cap {n p : ℝ} (hn : 1 ≤ n) (hp : n^2 ≤ p) :
    n^2 ≤ n^(59/100:ℝ)*p^(71/100:ℝ) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hn' := zero_lt_one.trans_le hn
  have pow := Real.rpow_le_rpow (sq_nonneg n) hp (by norm_num : (0:ℝ) ≤ 71/100)
  rw [← Real.rpow_natCast_mul hn0 2] at pow
  calc
    _ = n^(2:ℝ) := (Real.rpow_two n).symm
    _ ≤ n^(59/100 + 2*(71/100) : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    _ = n^(59/100:ℝ)*n^(2*(71/100:ℝ)) := Real.rpow_add hn' _ _
    _ ≤ _ := by
      push_cast at pow
      exact mul_le_mul_of_nonneg_left pow (by positivity)

/-- The rounded edge bound of Theorem 4 for the constructed offline preserver
on any finite directed graph. The bound holds for an arbitrary demand list. -/
theorem theorem4_rounded :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)),
      let H := offlinePreserver G D
      let n : ℝ := Fintype.card V
      let p : ℝ := D.length
      H ⊆ G ∧ Preserves G H D ∧
        (H.card : ℝ) ≤ K*(n+n^(3/4:ℝ)*p^(1/2:ℝ)+n^(59/100:ℝ)*p^(71/100:ℝ)) := by
  obtain ⟨B, hB, bound⟩ := theorem43_acyclic_iteration.{u,0} 2
  have eq : offlineExponent 2 = (12/17:ℝ) := by
    norm_num [offlineExponent, Function.iterate_succ_apply', offlineExponentStep]
  rw [eq] at bound
  refine ⟨B+2, by linarith, ?_⟩
  intro V _ _ G D
  obtain ⟨sub, correct, hbound⟩ := offlinePreserver_rate bound G D
  refine ⟨sub, correct, ?_⟩
  let H := offlinePreserver G D
  let n : ℝ := Fintype.card V
  let p : ℝ := D.length
  let F := n+n^(3/4:ℝ)*p^(1/2:ℝ)+n^(59/100:ℝ)*p^(71/100:ℝ)
  change (H.card : ℝ) ≤ (B+2)*F
  have hB' : 1 ≤ B+2 := by linarith
  have cap : (H.card : ℝ) ≤ n^2 := by
    have h := card_le_univ H
    rw [Fintype.card_prod, ← pow_two] at h
    change (H.card:ℝ) ≤ (Fintype.card V : ℝ)^2
    exact_mod_cast h
  by_cases n0 : Fintype.card V = 0
  · have z : n = 0 := by dsimp [n]; exact_mod_cast n0
    rw [z] at cap
    exact cap.trans (by rw [zero_pow (by decide : 2 ≠ 0)]; unfold F; positivity)
  have n1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ Fintype.card V from Nat.pos_of_ne_zero n0)
  by_cases p0 : D = []
  · have he : H = ∅ := by simp [H, offlinePreserver, liftedRun, p0]
    rw [he, card_empty, Nat.cast_zero]
    unfold F
    positivity
  have p1 : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (show 1 ≤ D.length from List.length_pos_iff.mpr p0)
  by_cases hpn : p ≤ n^2
  · exact hbound.trans (mul_le_mul_of_nonneg_left (offline_rounded_rate n1 p1 hpn) (by linarith))
  · have mix := offline_rounded_cap n1 (le_of_not_ge hpn)
    have hf : n^(59/100:ℝ)*p^(71/100:ℝ) ≤ F :=
      le_add_of_nonneg_left (by positivity : 0 ≤ n+n^(3/4:ℝ)*p^(1/2:ℝ))
    exact cap.trans (mix.trans (hf.trans ((one_mul F).symm.le.trans
      (mul_le_mul_of_nonneg_right hB' (by unfold F; positivity)))))

end OnlineReachabilityPreservers
