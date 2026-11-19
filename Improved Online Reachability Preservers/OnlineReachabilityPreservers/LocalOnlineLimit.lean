import OnlineReachabilityPreservers.LocalOnlineBound
import OnlineReachabilityPreservers.OnlineSharp

/-! The limiting Appendix A rate on arbitrary finite families of simple paths. -/

namespace OnlineReachabilityPreservers

open Finset Filter
open scoped Topology

universe u

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem list_initial_sparse {n p M : ℕ}
    (base : M ≤ 32*n ∨ M ≤ 16*p ∨ M^3 ≤ 32768*(n*p)^2)
    (sparse : (p:ℝ)^2 ≤ n ∨ (n:ℝ)^2 ≤ p) :
    (M:ℝ) ≤ 32*((n:ℝ)+p) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ (p:ℝ) := Nat.cast_nonneg _
  rcases base with bound | bound | bound
  · have h : (M:ℝ) ≤ 32*(n:ℝ) := by exact_mod_cast bound
    linarith
  · have h : (M:ℝ) ≤ 16*(p:ℝ) := by exact_mod_cast bound
    linarith
  · have h : (M:ℝ)^3 ≤ 32768*((n:ℝ)*p)^2 := by exact_mod_cast bound
    have product : ((n:ℝ)*p)^2 ≤ ((n:ℝ)+p)^3 := by
      rw [mul_pow]
      rcases sparse with few | many
      · calc
          _ ≤ (n:ℝ)^2*n := mul_le_mul_of_nonneg_left few (sq_nonneg _)
          _ = (n:ℝ)^3 := by ring
          _ ≤ _ := pow_le_pow_left₀ hn (by linarith) 3
      · calc
          _ ≤ (p:ℝ)*(p:ℝ)^2 := mul_le_mul_of_nonneg_right many (sq_nonneg _)
          _ = (p:ℝ)^3 := by ring
          _ ≤ _ := pow_le_pow_left₀ hp (by linarith) 3
    have cube : (M:ℝ)^3 ≤ (32*((n:ℝ)+p))^3 := h.trans ((mul_le_mul_of_nonneg_left product (by norm_num : (0:ℝ) ≤ 32768)).trans_eq (by ring))
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg M) (by positivity : 0 ≤ 32*((n:ℝ)+p))
      (by decide : (3:ℕ) ≠ 0)).mp cube

/-- Coefficients in the positive-slack bound are uniform above a
slack-dependent vertex threshold and uniform over all path counts. -/
theorem theorem38_list_eventually_uniform {α ε : ℝ} (ha : α ∈ Set.Ioo (7/10:ℝ) (701/1000))
    (hz : onlineCubic α = 0) (he : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type u) [LinearOrder V] [Fintype V] (p : ℕ)
      (paths : Fin p → List V), (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
      N ≤ Fintype.card V →
      let A := (2+α)/(3+α)
      let n : ℝ := Fintype.card V
      (∑ i, ((paths i).length:ℝ)) ≤
        32*(n+p)+n^(A+ε)*(p:ℝ)^(2-2*A)+n^(2-2*α+ε)*(p:ℝ)^α := by
  let δ := ε/2
  let A := (2+α)/(3+α)
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hA : A ≤ 1 := (div_le_iff₀ (by linarith [ha.1] : 0 < 3+α)).mpr (by linarith)
  obtain ⟨_, sec, _, blim, alim⟩ := theorem38_exponent_limits ha hz
  have aClose : ∀ᶠ k in atTop, onlineFirstExponent k ∈ Set.Ioo (A-δ/5) (A+δ/5) :=
    alim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have bClose : ∀ᶠ k in atTop, α-δ/2 < onlineSecondExponent k :=
    blim.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨k, ak, bk⟩ := (aClose.and bClose).exists
  let a := onlineFirstExponent k
  let b := onlineSecondExponent k
  obtain ⟨C, hC, bound⟩ := theorem38_list_iteration.{u} k
  obtain ⟨N, hN, threshold⟩ := threshold_for_power hC hδ
  refine ⟨N, ?_⟩
  intro V _ _ p' paths simple free size
  let n : ℝ := Fintype.card V
  let p : ℝ := p'
  let f := n^(A+ε)*p^(2-2*A)
  let g := n^(2-2*α+ε)*p^α
  let F := n^(A+δ)*p^(2-2*A)
  let G := n^(2-2*α+δ)*p^α
  change (∑ i, ((paths i).length:ℝ)) ≤ 32*(n+p)+f+g
  have hn : 1 ≤ n := by
    change (1:ℝ) ≤ (Fintype.card V:ℝ)
    exact_mod_cast hN.trans size
  have np := zero_lt_one.trans_le hn
  have p0 : 0 ≤ p := Nat.cast_nonneg _
  have f0 : 0 ≤ f := by dsimp only [f]; positivity
  have g0 : 0 ≤ g := by dsimp only [g]; positivity
  by_cases few : p ≤ Real.sqrt n
  · have sq : p^2 ≤ n := ((sq_le_sq₀ p0 (Real.sqrt_nonneg _)).mpr few).trans_eq (Real.sq_sqrt np.le)
    have small := list_initial_sparse (lemma27_list paths simple free) (Or.inl sq)
    rw [← Nat.cast_sum]
    exact small.trans (by linarith only [f0,g0])
  by_cases many : n^2 ≤ p
  · have large := list_initial_sparse (lemma27_list paths simple free) (Or.inr many)
    rw [← Nat.cast_sum]
    exact large.trans (by linarith only [f0,g0])
  have pp : 0 < p := (Real.sqrt_pos.mpr np).trans (lt_of_not_ge few)
  have hp : 1 ≤ p := by
    change (1:ℝ) ≤ (p':ℝ)
    exact_mod_cast (show 1 ≤ p' from Nat.cast_pos.mp pp)
  have square : p ≤ n^2 := le_of_not_ge many
  have nF : n ≤ F := by
    have q := Real.rpow_le_rpow (Real.sqrt_nonneg n) (le_of_not_ge few)
      (show 0 ≤ 2-2*A by linarith)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul np.le, show (1/2:ℝ)*(2-2*A)=1-A by ring] at q
    calc
      _ = n^A*n^(1-A) := by rw [← Real.rpow_add np, show A+(1-A)=1 by ring, Real.rpow_one]
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) q
        (Real.rpow_nonneg np.le _) (Real.rpow_nonneg np.le _)
  have pG : p ≤ G :=
    (pairs_le_mixed (b := α) (by linarith [ha.2]) np.le pp square).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) (Real.rpow_nonneg pp.le _))
  have fF : n^a*p^(2-2*a) ≤ F :=
    leading_rate_slack hn hp square hδ ak.2.le ak.1.le
  have gG : n^(2-2*b)*p^b ≤ G :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [bk]))
      (Real.rpow_le_rpow_of_exponent_le hp (sec k).2.le)
      (Real.rpow_nonneg pp.le _) (Real.rpow_nonneg np.le _)
  have F0 : 0 ≤ F := np.le.trans nF
  have G0 : 0 ≤ G := p0.trans pG
  have both : onlineRate a b n p ≤ F+G := max_le (nF.trans (le_add_of_nonneg_right G0))
    (max_le (fF.trans (le_add_of_nonneg_right G0)) (max_le
      (gG.trans (le_add_of_nonneg_left F0)) (pG.trans (le_add_of_nonneg_left F0))))
  have expandF : n^δ*F = f := by
    dsimp only [F,f]
    rw [← mul_assoc, ← Real.rpow_add np, show δ+(A+δ)=A+ε by dsimp only [δ]; ring]
  have expandG : n^δ*G = g := by
    dsimp only [G,g]
    rw [← mul_assoc, ← Real.rpow_add np, show δ+(2-2*α+δ)=2-2*α+ε by dsimp only [δ]; ring]
  calc
    _ ≤ C*onlineRate a b n p := bound V p' paths simple free
    _ ≤ C*(F+G) := mul_le_mul_of_nonneg_left both (zero_le_one.trans hC)
    _ ≤ n^δ*(F+G) := mul_le_mul_of_nonneg_right (threshold _ size) (add_nonneg F0 G0)
    _ = f+g := by rw [mul_add, expandF, expandG]
    _ ≤ _ := by linarith only [np, p0]

/-- Theorem 38 for arbitrary finite simple paths, with a single
vertex-dependent slack tending to zero and a uniform coefficient. -/
theorem theorem38_list_limit {α : ℝ} (ha : α ∈ Set.Ioo (7/10:ℝ) (701/1000)) (hz : onlineCubic α = 0) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ K ≥ 1, ∀ (V : Type u) [LinearOrder V] [Fintype V] (p : ℕ)
        (paths : Fin p → List V), (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
        let A := (2+α)/(3+α)
        let n : ℝ := Fintype.card V
        let e := ε (Fintype.card V)
        (∑ i, ((paths i).length:ℝ)) ≤ K*(n+n^(A+e)*(p:ℝ)^(2/(3+α))+n^(2-2*α+e)*(p:ℝ)^α+p) := by
  classical
  let δ (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have δpos (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have δlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have uniform (k : ℕ) := theorem38_list_eventually_uniform.{u} ha hz (δpos k)
  choose N valid using uniform
  let eligible (n : ℕ) := (range (n+1)).filter fun k => N k ≤ n
  let index (n : ℕ) := if h : (eligible n).Nonempty then (eligible n).max' h else 0
  have choose_mem {n : ℕ} (h : (eligible n).Nonempty) : index n ∈ eligible n := by
    dsimp only [index]
    rw [dite_eq_left h]
    exact max'_mem _ _
  have eventually_ge : Tendsto index atTop atTop := by
    refine tendsto_atTop.2 fun k => eventually_atTop.2 ⟨max k (N k), ?_⟩
    intro n hn
    have eligibleK : k ∈ eligible n := mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le ((le_max_left k (N k)).trans hn)),
        (le_max_right k (N k)).trans hn⟩
    have ne : (eligible n).Nonempty := ⟨k,eligibleK⟩
    dsimp only [index]
    rw [dite_eq_left ne]
    exact le_max' _ _ eligibleK
  let ε (n : ℕ) := δ (index n)
  let K := max (32:ℝ) (N 0:ℝ)
  have hK : (32:ℝ) ≤ K := le_max_left _ _
  have N0K : (N 0:ℝ) ≤ K := le_max_right _ _
  have K1 : 1 ≤ K := (by norm_num : (1:ℝ) ≤ 32).trans hK
  refine ⟨ε, fun n => (δpos _).le, δlim.comp eventually_ge, K, K1, ?_⟩
  intro V _ _ p paths simple free
  let m := Fintype.card V
  let n : ℝ := m
  let a := (2+α)/(3+α)
  let f := n^(a+ε m)*(p:ℝ)^(2-2*a)
  let g := n^(2-2*α+ε m)*(p:ℝ)^α
  have aEq : (2:ℝ)/(3+α)=2-2*a := by
    have h : (3+α:ℝ) ≠ 0 := (show 0 < 3+α by linarith [ha.1]).ne'
    dsimp only [a]
    field_simp [h]
    ring
  rw [aEq]
  change (∑ i, ((paths i).length:ℝ)) ≤ K*(n+f+g+p)
  have np : 0 ≤ n := Nat.cast_nonneg m
  have pp : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
  have f0 : 0 ≤ f := by dsimp only [f]; positivity
  have g0 : 0 ≤ g := by dsimp only [g]; positivity
  by_cases large : N 0 ≤ m
  · have zeroEligible : 0 ∈ eligible m :=
      mem_filter.mpr ⟨mem_range.mpr (Nat.succ_pos _), large⟩
    have indexValid : N (index m) ≤ m :=
      (mem_filter.mp (choose_mem ⟨0,zeroEligible⟩)).2
    have bound : (∑ i, ((paths i).length:ℝ)) ≤ 32*(n+p)+f+g :=
      valid (index m) V p paths simple free indexValid
    calc
      _ ≤ _ := bound
      _ ≤ K*(n+p)+K*(f+g) := by
        rw [add_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_right hK (add_nonneg np pp))
          ((one_mul (f+g)).symm.le.trans (mul_le_mul_of_nonneg_right K1 (add_nonneg f0 g0)))
      _ = _ := by ring
  · have cap : (∑ i, ((paths i).length:ℝ)) ≤ n*p := by
      calc
        _ ≤ ∑ _ : Fin p, n := sum_le_sum fun i _ => by
          rw [← List.toFinset_card_of_nodup (simple i)]
          exact Nat.cast_le.mpr (card_le_univ _)
        _ = _ := by simp [mul_comm]
    have nm : n ≤ (N 0:ℝ) := Nat.cast_le.mpr (le_of_not_ge large)
    calc
      _ ≤ _ := cap
      _ ≤ K*p := mul_le_mul_of_nonneg_right (nm.trans N0K) pp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [np,f0,g0]) (zero_le_one.trans K1)

end OnlineReachabilityPreservers
