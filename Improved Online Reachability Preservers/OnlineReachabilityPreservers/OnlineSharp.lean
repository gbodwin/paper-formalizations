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

/-- In the middle range of demand counts the mixed term dominates the count itself. -/
theorem pairs_le_mixed {b n p : ℝ} (hb : b ≤ 1) (hn : 0 ≤ n)
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


open Filter Set
open scoped Topology

/-- Transfer perturbations of both leading exponents to vertex slack. -/
theorem leading_rate_slack {a A n p ε : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hpn : p ≤ n^2) (he : 0 < ε)
    (head : a ≤ A+ε/5) (tail : A-ε/5 ≤ a) :
    n^a*p^(2-2*a) ≤ n^(A+ε)*p^(2-2*A) := by
  have np := zero_lt_one.trans_le hn
  have pp := zero_lt_one.trans_le hp
  have h := Real.rpow_le_rpow (zero_le_one.trans hp) hpn (show 0 ≤ 2*(ε/5) by linarith)
  rw [← Real.rpow_natCast_mul np.le 2] at h
  push_cast at h
  have pShift : p^(2*(A-a)) ≤ n^(4*(ε/5)) := calc
    _ ≤ p^(2*(ε/5)) := Real.rpow_le_rpow_of_exponent_le hp (by linarith)
    _ ≤ _ := h.trans_eq (by congr 1; ring)
  calc
    _ = (n^a*p^(2*(A-a)))*p^(2-2*A) := by
      rw [mul_assoc, ← Real.rpow_add pp, show 2*(A-a)+(2-2*A)=2-2*a by ring]
    _ ≤ (n^(A+ε/5)*n^(4*(ε/5)))*p^(2-2*A) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn head)
        pShift (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add np, show A+ε/5+4*(ε/5)=A+ε by ring]

/-- Each positive vertex-exponent slack in Theorem 1 admits a single
coefficient for all graphs and prefixes. -/
theorem theorem1_epsilon {α ε : ℝ} (ha : α ∈ Ioo (7/10:ℝ) (701/1000))
    (hz : onlineCubic α = 0) (he : 0 < ε) :
    ∃ K ≥ 1, ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)),
      let A := (2+α)/(3+α)
      let n : ℝ := Fintype.card V
      let p : ℝ := D.length
      ((sinkPreserver G D).card:ℝ) ≤
        K*(n+n^(A+ε)*p^(2-2*A)+n^(2-2*α+ε)*p^α) := by
  let A := (2+α)/(3+α)
  obtain ⟨_, sec, _, clim, alim⟩ := theorem38_exponent_limits ha hz
  have aClose : ∀ᶠ k in atTop, onlineFirstExponent k ∈ Ioo (A-ε/5) (A+ε/5) :=
    alim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have bClose : ∀ᶠ k in atTop, α-ε/2 < onlineSecondExponent k :=
    clim.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨k, ak, bk⟩ := (aClose.and bClose).exists
  let a := onlineFirstExponent k
  let b := onlineSecondExponent k
  obtain ⟨C,hC,prior⟩ := theorem38_acyclic_iteration.{u,0} k
  refine ⟨C+2,by linarith,?_⟩
  intro V _ _ G D
  let H := sinkPreserver G D
  let n : ℝ := Fintype.card V
  let p : ℝ := D.length
  let F := n+n^(A+ε)*p^(2-2*A)+n^(2-2*α+ε)*p^α
  change (H.card:ℝ) ≤ (C+2)*F
  have hK : 1 ≤ C+2 := by linarith
  have F0 : 0 ≤ F := by dsimp only [F]; positivity
  have s₁ : 0 ≤ n^(A+ε)*p^(2-2*A) := by positivity
  have s₂ : 0 ≤ n^(2-2*α+ε)*p^α := by positivity
  have cap : (H.card:ℝ) ≤ n^2 := by
    have h := card_le_univ H
    rw [Fintype.card_prod, ← pow_two] at h
    change (H.card:ℝ) ≤ (Fintype.card V:ℝ)^2
    exact_mod_cast h
  by_cases n0 : Fintype.card V = 0
  · have z : n = 0 := by change (Fintype.card V:ℝ)=0; exact_mod_cast n0
    rw [z, zero_pow (by decide : 2 ≠ 0)] at cap
    exact cap.trans (mul_nonneg (zero_le_one.trans hK) F0)
  have hn : 1 ≤ n := by
    change (1:ℝ) ≤ (Fintype.card V:ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card V from Nat.pos_of_ne_zero n0)
  by_cases p0 : D = []
  · have z : H = ∅ := by simp [H, sinkPreserver, liftedRun, p0]
    rw [z, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hK) F0
  have hp : 1 ≤ p := by
    change (1:ℝ) ≤ (D.length:ℝ)
    exact_mod_cast (show 1 ≤ D.length from List.length_pos_iff.mpr p0)
  have np := zero_lt_one.trans_le hn
  have pp := zero_lt_one.trans_le hp
  obtain ⟨_, _, size⟩ := sinkPreserver_rate prior G D
  have g : n^(2-2*α)*p^α ≤ n^(2-2*α+ε)*p^α := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) (Real.rpow_nonneg pp.le _)
  have gF : n^(2-2*α+ε)*p^α ≤ F := le_add_of_nonneg_left (by positivity)
  by_cases small : p ≤ n^2
  · have nF : n ≤ F := by dsimp only [F]; linarith only [s₁,s₂]
    have pF : p ≤ F :=
      (pairs_le_mixed (b := α) (by linarith [ha.2]) np.le pp small).trans (g.trans gF)
    have fF : n^a*p^(2-2*a) ≤ F :=
      (leading_rate_slack hn hp small he ak.2.le ak.1.le).trans
        (by dsimp only [F]; linarith only [np,s₂])
    have mF₀ : n^(2-2*b)*p^b ≤ n^(2-2*α+ε)*p^α :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [bk]))
        (Real.rpow_le_rpow_of_exponent_le hp (sec k).2.le)
        (Real.rpow_nonneg pp.le _) (Real.rpow_nonneg np.le _)
    exact size.trans (mul_le_mul_of_nonneg_left (max_le nF (max_le fF (max_le (mF₀.trans gF) pF)))
      (zero_le_one.trans hK))
  · have m := cap_le_mixed (b := α) (by linarith [ha.1]) np (le_of_not_ge small)
    exact cap.trans (m.trans (g.trans (gF.trans ((one_mul F).symm.le.trans
      (mul_le_mul_of_nonneg_right hK F0)))))

private theorem sinkPreserver_small_pairs {V : Type u} [LinearOrder V] [Fintype V]
    (G : Arcs V) (D : List (V × V))
    (few : (D.length:ℝ) ≤ Real.sqrt (Fintype.card V:ℝ)) :
    ((sinkPreserver G D).card:ℝ) ≤ 18*(Fintype.card V:ℝ) := by
  let n := Fintype.card V
  let p := D.length
  let H := sinkPreserver G D
  have n0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have p0 : 0 ≤ (p:ℝ) := Nat.cast_nonneg _
  obtain ⟨_, _, base⟩ := pairwise_initial G D
  rcases base with small | dense
  · exact_mod_cast small
  let e := H.card-2*n
  have hr : (e:ℝ)^3 ≤ 2048*((n:ℝ)*p)^2 := by exact_mod_cast dense
  have hp : (p:ℝ)^2 ≤ n := ((sq_le_sq₀ p0 (Real.sqrt_nonneg _)).mpr few).trans_eq (Real.sq_sqrt n0)
  have cube : (e:ℝ)^3 ≤ (16*(n:ℝ))^3 := calc
    _ ≤ _ := hr
    _ = (2048*(n:ℝ)^2)*(p:ℝ)^2 := by ring
    _ ≤ (2048*(n:ℝ)^2)*n := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (by norm_num : (2048:ℝ) ≤ 4096) (pow_nonneg n0 3)
      nlinarith only [h]
  have root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg e)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) n0) (by decide : (3:ℕ) ≠ 0)).mp cube
  have h : H.card ≤ e+2*n := by dsimp only [e]; omega
  have h' : (H.card:ℝ) ≤ (e:ℝ)+2*(n:ℝ) := by exact_mod_cast h
  linarith only [root,h']

/-- Absorb a fixed coefficient into any positive vertex power above a threshold. -/
theorem threshold_for_power {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → K ≤ (n:ℝ)^δ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (K^(1/δ))
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn
  have h := hN.trans (Nat.cast_le.mpr ((le_max_left N 1).trans hn))
  have pw := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hK) _) h hδ.le
  rw [← Real.rpow_mul (zero_le_one.trans hK), one_div_mul_cancel hδ.ne', Real.rpow_one] at pw
  exact pw

/-- The positive-slack estimate with coefficients independent of the chosen
slack, once the graph size crosses a slack-dependent threshold. -/
theorem theorem1_eventually_uniform {α ε : ℝ} (ha : α ∈ Ioo (7/10:ℝ) (701/1000))
    (hz : onlineCubic α = 0) (he : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)),
      N ≤ Fintype.card V →
      let A := (2+α)/(3+α)
      let n : ℝ := Fintype.card V
      let p : ℝ := D.length
      ((sinkPreserver G D).card:ℝ) ≤
        18*n + 2*(n^(A+ε)*p^(2-2*A)+n^(2-2*α+ε)*p^α) := by
  let δ := ε/2
  let A := (2+α)/(3+α)
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hA : A ≤ 1 := (div_le_iff₀ (by linarith [ha.1] : 0 < 3+α)).mpr (by linarith)
  obtain ⟨K,hK,relax⟩ := theorem1_epsilon.{u} ha hz hδ
  obtain ⟨N,hN,threshold⟩ := threshold_for_power hK hδ
  refine ⟨N,?_⟩
  intro V _ _ G D size
  let n : ℝ := Fintype.card V
  let p : ℝ := D.length
  let f := n^(A+ε)*p^(2-2*A)
  let g := n^(2-2*α+ε)*p^α
  let F := n^(A+δ)*p^(2-2*A)
  let G' := n^(2-2*α+δ)*p^α
  let H := sinkPreserver G D
  have hn : 1 ≤ n := by
    change (1:ℝ) ≤ (Fintype.card V:ℝ)
    exact_mod_cast hN.trans size
  have np := zero_lt_one.trans_le hn
  have f0 : 0 ≤ f := by dsimp only [f]; positivity
  have g0 : 0 ≤ g := by dsimp only [g]; positivity
  change (H.card:ℝ) ≤ 18*n+2*(f+g)
  by_cases few : p ≤ Real.sqrt n
  · exact (sinkPreserver_small_pairs G D few).trans (by linarith only [f0,g0])
  have pp : 0 < p := (Real.sqrt_pos.mpr np).trans (lt_of_not_ge few)
  have nF : n ≤ F := by
    have q := Real.rpow_le_rpow (Real.sqrt_nonneg n) (le_of_not_ge few) (sub_nonneg.mpr (by linarith : 2*A ≤ 2))
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul np.le, show (1/2:ℝ)*(2-2*A)=1-A by ring] at q
    calc
      _ = n^A*n^(1-A) := by rw [← Real.rpow_add np, show A+(1-A)=1 by ring, Real.rpow_one]
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) q
        (Real.rpow_nonneg np.le _) (Real.rpow_nonneg np.le _)
  have positiveF : 0 ≤ F := np.le.trans nF
  have positiveG : 0 ≤ G' := by dsimp only [G']; positivity
  have Kbound : K ≤ n^δ := threshold _ size
  have expandF : n^δ*F = f := by
    dsimp only [F,f]
    rw [← mul_assoc, ← Real.rpow_add np, show δ+(A+δ)=A+ε by dsimp only [δ]; ring]
  have expandG : n^δ*G' = g := by
    dsimp only [G',g]
    rw [← mul_assoc, ← Real.rpow_add np, show δ+(2-2*α+δ)=2-2*α+ε by dsimp only [δ]; ring]
  calc
    _ ≤ K*(n+F+G') := relax V G D
    _ ≤ K*(2*F+G') := mul_le_mul_of_nonneg_left (by linarith only [nF]) (zero_le_one.trans hK)
    _ ≤ n^δ*(2*F+G') := mul_le_mul_of_nonneg_right Kbound (by linarith only [positiveF,positiveG])
    _ = 2*f+g := by rw [mul_add, ← mul_assoc, mul_comm (n^δ) 2, mul_assoc, expandF, expandG]
    _ ≤ _ := by linarith only [g0,np]

/-- The unrounded edge bound of Theorem 1. The slack tends to zero with n
and depends on the vertex count alone. The algorithm is the same at every
prefix. -/
theorem theorem1_limiting_rate {α : ℝ} (ha : α ∈ Ioo (7/10:ℝ) (701/1000))
    (hz : onlineCubic α = 0) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V),
        (∀ D E : List (V × V), D <+: E → sinkPreserver G D ⊆ sinkPreserver G E) ∧
        ∀ D : List (V × V),
          let H := sinkPreserver G D
          let a := (2+α)/(3+α)
          let n : ℝ := Fintype.card V
          let p : ℝ := D.length
          let e := ε (Fintype.card V)
          H ⊆ G ∧ Preserves G H D ∧
            (H.card:ℝ) ≤ K*(n+n^(a+e)*p^(2/(3+α))+n^(2-2*α+e)*p^α) := by
  classical
  let δ (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have δpos (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have δlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have uniform (k : ℕ) := theorem1_eventually_uniform.{u} ha hz (δpos k)
  choose N valid using uniform
  let eligible (n : ℕ) := (range (n+1)).filter fun k => N k ≤ n
  let index (n : ℕ) := if h : (eligible n).Nonempty then (eligible n).max' h else 0
  have choose_mem {n : ℕ} (h : (eligible n).Nonempty) : index n ∈ eligible n := by
    dsimp only [index]
    rw [dite_eq_left h]
    exact max'_mem _ _
  have eventually_ge : Tendsto index atTop atTop := by
    refine tendsto_atTop.2 fun k => eventually_atTop.2 ⟨max k (N k),?_⟩
    intro n hn
    have eligibleK : k ∈ eligible n := mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le ((le_max_left k (N k)).trans hn)),
        (le_max_right k (N k)).trans hn⟩
    have ne : (eligible n).Nonempty := ⟨k,eligibleK⟩
    dsimp only [index]
    rw [dite_eq_left ne]
    exact le_max' _ _ eligibleK
  let ε (n : ℕ) := δ (index n)
  let K := max (18:ℝ) (N 0:ℝ)
  have hK : (18:ℝ) ≤ K := le_max_left _ _
  have N0K : (N 0:ℝ) ≤ K := le_max_right _ _
  have Kp : 0 < K := (by norm_num : (0:ℝ) < 18).trans_le hK
  refine ⟨ε, fun n => (δpos _).le, δlim.comp eventually_ge, K, Kp, ?_⟩
  intro V _ _ G
  refine ⟨fun D E h => sinkPreserver_prefix G h,?_⟩
  intro D
  obtain ⟨sub,correct,_⟩ := sinkPreserver_spec G D
  refine ⟨sub,correct,?_⟩
  let m := Fintype.card V
  let H := sinkPreserver G D
  let n : ℝ := m
  let p : ℝ := D.length
  let a := (2+α)/(3+α)
  let f := n^(a+ε m)*p^(2-2*a)
  let g := n^(2-2*α+ε m)*p^α
  have aEq : (2:ℝ)/(3+α)=2-2*a := by
    have h : (3+α:ℝ) ≠ 0 := (show 0 < 3+α by linarith [ha.1]).ne'
    dsimp only [a]
    field_simp [h]
    ring
  rw [aEq]
  change (H.card:ℝ) ≤ K*(n+f+g)
  have np : 0 ≤ n := Nat.cast_nonneg m
  have f0 : 0 ≤ f := by dsimp only [f]; positivity
  have g0 : 0 ≤ g := by dsimp only [g]; positivity
  by_cases large : N 0 ≤ m
  · have zeroEligible : 0 ∈ eligible m :=
      mem_filter.mpr ⟨mem_range.mpr (Nat.succ_pos _), large⟩
    have indexValid : N (index m) ≤ m :=
      (mem_filter.mp (choose_mem ⟨0,zeroEligible⟩)).2
    have bound : (H.card:ℝ) ≤ 18*n+2*(f+g) := valid (index m) V G D indexValid
    calc
      _ ≤ _ := bound
      _ ≤ K*n+K*(f+g) := add_le_add (mul_le_mul_of_nonneg_right hK np)
        (mul_le_mul_of_nonneg_right ((by norm_num : (2:ℝ) ≤ 18).trans hK) (add_nonneg f0 g0))
      _ = _ := by ring
  · have cap : (H.card:ℝ) ≤ n^2 := by
      have h := card_le_univ H
      rw [Fintype.card_prod, ← pow_two] at h
      change (H.card:ℝ) ≤ (Fintype.card V:ℝ)^2
      exact_mod_cast h
    have nm : n ≤ (N 0:ℝ) := Nat.cast_le.mpr (le_of_not_ge large)
    calc
      _ ≤ n^2 := cap
      _ ≤ K*n := by rw [pow_two]; exact mul_le_mul_of_nonneg_right (nm.trans N0K) np
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [f0,g0]) Kp.le


end OnlineReachabilityPreservers
