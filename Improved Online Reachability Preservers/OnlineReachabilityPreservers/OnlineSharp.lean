import OnlineReachabilityPreservers.OnlineBound

/-! The graph application of the acyclic Appendix A bounds. -/

namespace OnlineReachabilityPreservers

open Finset

universe u

section Graph

variable {V : Type u} [LinearOrder V] [Fintype V]

private theorem forwardRun_rate {a b C : ℝ} (prior : OnlineIncidenceBound.{u,0} a b C)
    {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    ((forwardRun G D).card:ℝ) ≤ C*onlineRate a b (Fintype.card V) D.length := by
  let paths := topologicalPaths G (compressed G D)
  let W := Set.range (reverseTopologicalKey G)
  let : Fintype (Set.range (reverseTopologicalKey G)) := Fintype.ofEquiv V (topologicalEquiv G)
  have bound := prior W (Fin D.length) paths (orderedCompression_free dag D)
  have count : (∑ i : Fin D.length, (paths i).card) = (forwardRun G D).card+D.length := by
    simpa only [paths, topologicalPaths, card_map] using compressed_total dag D
  rw [← Nat.cast_sum, count, ← Fintype.card_congr (topologicalEquiv G), Fintype.card_fin] at bound
  exact (Nat.cast_le.mpr (Nat.le_add_right _ _)).trans bound

private theorem sinkPreserver_rate {a b C : ℝ} (prior : OnlineIncidenceBound.{u,0} a b C)
    (G : Arcs V) (D : List (V × V)) :
    let H := sinkPreserver G D
    H ⊆ G ∧ Preserves G H D ∧
      (H.card:ℝ) ≤ (C+2)*onlineRate a b (Fintype.card V) D.length := by
  obtain ⟨sub, correct, overhead⟩ := sinkPreserver_spec G D
  have m := forwardRun_rate prior (condensation_dag G) (D.map (projectDemand G))
  rw [List.length_map] at m
  let H := sinkPreserver G D
  let n := Fintype.card V
  let F := onlineRate a b (n:ℝ) D.length
  have nF : (n:ℝ) ≤ F := le_max_left _ _
  have o : (H.card:ℝ) ≤ ((forwardRun (condensation G) (D.map (projectDemand G))).card:ℝ)+2*(n:ℝ) := by
    exact_mod_cast overhead
  exact ⟨sub, correct, by nlinarith only [o,m,nF]⟩

end Graph

private theorem leading_rate_le {a A n p : ℝ} (ha : A ≤ a) (ha' : a ≤ 1)
    (hn : 0 < n) (hp : 0 < p) : n^a*p^(2-2*a) ≤ max n (n^A*p^(2-2*A)) := by
  by_cases h : p ≤ Real.sqrt n
  · apply le_max_of_le_left
    have pow := Real.rpow_le_rpow hp.le h (show 0 ≤ 2-2*a by linarith)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le] at pow
    calc
      _ ≤ n^a*n^((1/2)*(2-2*a)) := mul_le_mul_of_nonneg_left pow (by positivity)
      _ = _ := by rw [← Real.rpow_add hn, show a+(1/2)*(2-2*a)=1 by ring, Real.rpow_one]
  · apply le_max_of_le_right
    have square : n ≤ p^2 := by
      rw [← Real.sq_sqrt hn.le]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hp.le).mpr (le_of_not_ge h)
    let e := a-A
    have pow := Real.rpow_le_rpow hn.le square (sub_nonneg.mpr ha)
    rw [← Real.rpow_natCast_mul hp.le 2] at pow
    push_cast at pow
    calc
      _ = (n^A*p^(2-2*a))*n^e := by
        rw [show (n^A*p^(2-2*a))*n^e = (n^A*n^e)*p^(2-2*a) by ring,
          ← Real.rpow_add hn, show A+e=a by dsimp [e]; ring]
      _ ≤ (n^A*p^(2-2*a))*p^(2*e) := mul_le_mul_of_nonneg_left pow (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hp, show (2-2*a)+2*e=2-2*A by dsimp [e]; ring]

private theorem pairs_le_mixed {b n p : ℝ} (hb : b ≤ 1) (hn : 0 ≤ n)
    (hp : 0 < p) (hpn : p ≤ n^2) : p ≤ n^(2-2*b)*p^b := by
  have h := Real.rpow_le_rpow hp.le hpn (sub_nonneg.mpr hb)
  rw [← Real.rpow_natCast_mul hn 2] at h
  push_cast at h
  calc
    p = p^(1-b)*p^b := by rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
    _ ≤ n^(2*(1-b))*p^b := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [show (2:ℝ)*(1-b)=2-2*b by ring]

private theorem cap_le_mixed {b n p : ℝ} (hb : 0 ≤ b) (hn : 0 < n) (hp : n^2 ≤ p) :
    n^2 ≤ n^(2-2*b)*p^b := by
  have h := Real.rpow_le_rpow (sq_nonneg n) hp hb
  rw [← Real.rpow_natCast_mul hn.le 2] at h
  push_cast at h
  calc
    _ = n^(2:ℝ) := (Real.rpow_two n).symm
    _ = n^(2-2*b)*n^(2*b) := by rw [← Real.rpow_add hn, show 2-2*b+2*b=2 by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

private theorem online_second_iterate :
    onlineFirstExponent 2 = (62/85:ℝ) ∧ onlineSecondExponent 2 = (1006/1437:ℝ) := by
  change (2+onlineSecondExponent 1)/(3+onlineSecondExponent 1) = (62/85:ℝ) ∧ _
  norm_num [onlineSecondExponent, Function.iterate_succ_apply', onlineExponentStep]

/-- The rounded edge bound in Theorem 1 on the executable forward-growth
preserver, on general digraphs and at every prefix of an arbitrary demand list. -/
theorem theorem1_rounded :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V),
      (∀ D E : List (V × V), D <+: E → sinkPreserver G D ⊆ sinkPreserver G E) ∧
      ∀ D : List (V × V),
        let H := sinkPreserver G D
        let n : ℝ := Fintype.card V
        let p : ℝ := D.length
        H ⊆ G ∧ Preserves G H D ∧
          (H.card:ℝ) ≤ K*(n+n^(18/25:ℝ)*p^(14/25:ℝ)+n^(3/5:ℝ)*p^(7/10:ℝ)) := by
  obtain ⟨C, hC, prior⟩ := theorem38_acyclic_iteration.{u,0} 2
  obtain ⟨a, b⟩ := online_second_iterate
  rw [a,b] at prior
  refine ⟨C+2, by linarith, ?_⟩
  intro V _ _ G
  refine ⟨fun D E h => sinkPreserver_prefix G h, ?_⟩
  intro D
  obtain ⟨sub, correct, size⟩ := sinkPreserver_rate prior G D
  refine ⟨sub, correct, ?_⟩
  let H := sinkPreserver G D
  let n : ℝ := Fintype.card V
  let p : ℝ := D.length
  let F := n+n^(18/25:ℝ)*p^(14/25:ℝ)+n^(3/5:ℝ)*p^(7/10:ℝ)
  change (H.card:ℝ) ≤ (C+2)*F
  have hK : 1 ≤ C+2 := by linarith
  have F0 : 0 ≤ F := by dsimp only [F]; positivity
  have cap : (H.card:ℝ) ≤ n^2 := by
    have h := card_le_univ H
    rw [Fintype.card_prod, ← pow_two] at h
    change (H.card:ℝ) ≤ (Fintype.card V:ℝ)^2
    exact_mod_cast h
  by_cases n0 : Fintype.card V = 0
  · have z : n = 0 := by change (Fintype.card V:ℝ)=0; exact_mod_cast n0
    rw [z, zero_pow (by decide : 2 ≠ 0)] at cap
    exact cap.trans (mul_nonneg (zero_le_one.trans hK) F0)
  have hn : 0 < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero n0)
  by_cases p0 : D = []
  · have z : H = ∅ := by simp [H, sinkPreserver, liftedRun, p0]
    rw [z, card_empty, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hK) F0
  have hp : 0 < p := Nat.cast_pos.mpr (List.length_pos_iff.mpr p0)
  have nF : n ≤ F := by
    have q₁ : 0 ≤ n^(18/25:ℝ)*p^(14/25:ℝ) := by positivity
    have q₂ : 0 ≤ n^(3/5:ℝ)*p^(7/10:ℝ) := by positivity
    dsimp only [F]
    linarith only [q₁,q₂]
  have fF : n^(18/25:ℝ)*p^(14/25:ℝ) ≤ F := by
    have q₂ : 0 ≤ n^(3/5:ℝ)*p^(7/10:ℝ) := by positivity
    dsimp only [F]
    linarith only [hn,q₂]
  have gF : n^(3/5:ℝ)*p^(7/10:ℝ) ≤ F := le_add_of_nonneg_left (by positivity)
  have hlead : n^(62/85:ℝ)*p^(2-2*(62/85:ℝ)) ≤ F := by
    have m := leading_rate_le (show (18/25:ℝ) ≤ 62/85 by norm_num) (by norm_num) hn hp
    have ex : (2:ℝ)-2*(18/25) = 14/25 := by norm_num
    rw [ex] at m
    exact m.trans (max_le nF fF)
  have ex : (2:ℝ)-2*(7/10) = 3/5 := by norm_num
  by_cases hpn : p ≤ n^2
  · have pF : p ≤ F := by
      have m := pairs_le_mixed (b := (7/10:ℝ)) (by norm_num) hn.le hp hpn
      rw [ex] at m
      exact m.trans gF
    have hmix : n^(2-2*(1006/1437:ℝ))*p^(1006/1437:ℝ) ≤ F := by
      have m := mixed_term_le (show (7/10:ℝ) ≤ 1006/1437 by norm_num) (by norm_num) hn hp
      rw [ex] at m
      exact m.trans (max_le gF pF)
    exact size.trans (mul_le_mul_of_nonneg_left (max_le nF (max_le hlead (max_le hmix pF)))
      (zero_le_one.trans hK))
  · have m := cap_le_mixed (b := (7/10:ℝ)) (by norm_num) hn (le_of_not_ge hpn)
    rw [ex] at m
    exact cap.trans (m.trans (gF.trans ((one_mul F).symm.le.trans
      (mul_le_mul_of_nonneg_right hK F0))))

end OnlineReachabilityPreservers
