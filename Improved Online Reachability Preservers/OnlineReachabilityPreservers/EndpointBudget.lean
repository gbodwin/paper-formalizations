import Mathlib.Data.Nat.Sqrt
import OnlineReachabilityPreservers.IndexSensitive
import OnlineReachabilityPreservers.Restricted

/-! A computable envelope for the endpoint-restricted case and its dyadic growth. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Integer budget for a graph on n vertices with σ allowed sinks. -/
def endpointBudget (n σ p : ℕ) : ℕ := n + Nat.sqrt (2 * n * σ * p)

/-- Start the doubling schedule near the point at which the square-root term reaches n. -/
def endpointBase (n σ : ℕ) : ℕ := max 1 (n / σ)

private noncomputable def endpointRoot (n σ p : ℕ) : ℝ := Real.sqrt (2 * (n : ℝ) * σ * p)

private theorem endpointRoot_nonneg (n σ p : ℕ) : 0 ≤ endpointRoot n σ p :=
  Real.sqrt_nonneg _

private theorem endpointRoot_sq (n σ p : ℕ) :
    (endpointRoot n σ p) ^ 2 = 2 * (n : ℝ) * σ * p := by
  unfold endpointRoot
  exact Real.sq_sqrt (by positivity)

private theorem endpointRoot_mono (n σ : ℕ) : Monotone (endpointRoot n σ) := by
  intro a b hab
  unfold endpointRoot
  apply Real.sqrt_le_sqrt
  gcongr

theorem endpointBudget_le (n σ p : ℕ) :
    (endpointBudget n σ p : ℝ) ≤ n + Real.sqrt (2 * (n : ℝ) * σ * p) := by
  have h := Nat.sqrt_le' (2 * n * σ * p)
  have hs : (Nat.sqrt (2 * n * σ * p) : ℝ)^2 ≤ 2 * (n : ℝ) * σ * p := by exact_mod_cast h
  have hroot : (Nat.sqrt (2 * n * σ * p) : ℝ) ≤ endpointRoot n σ p := by
    unfold endpointRoot
    exact Real.le_sqrt_of_sq_le hs
  simpa [endpointBudget, endpointRoot, Nat.cast_add] using add_le_add_left hroot (n : ℝ)

private theorem endpointRoot_le_budget {n : ℕ} (hn : 0 < n) (σ p : ℕ) :
    endpointRoot n σ p ≤ (endpointBudget n σ p : ℝ) := by
  let x := Nat.sqrt (2 * n * σ * p)
  have h : (2 * (n : ℝ) * σ * p) ≤ ((x : ℝ) + 1)^2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' (2 * n * σ * p)).le
  have h' := (Real.sqrt_le_iff).mpr
    ⟨by positivity, h⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  unfold endpointRoot endpointBudget
  push_cast
  change Real.sqrt (2 * (n : ℝ) * σ * p) ≤ n + (x : ℝ)
  linarith only [h', hn']

private theorem endpointBudget_ge_n (n σ p : ℕ) :
    (n : ℝ) ≤ (endpointBudget n σ p : ℝ) := by
  unfold endpointBudget
  push_cast
  exact le_add_of_nonneg_right (by positivity)

private theorem endpointBase_spec {n σ : ℕ} (hσ : 0 < σ) (hs : σ ≤ n) :
    0 < endpointBase n σ ∧ σ * endpointBase n σ ≤ n ∧ n ≤ 2 * (σ * endpointBase n σ) := by
  have hd : 0 < n / σ := Nat.div_pos hs hσ
  rw [endpointBase, max_eq_right (by omega : 1 ≤ n / σ)]
  have hdiv := Nat.mod_add_div n σ
  have hm := Nat.mod_lt n hσ
  have hσd : σ ≤ σ * (n / σ) := by
    conv_lhs => rw [← Nat.mul_one σ]
    exact Nat.mul_le_mul_left σ (by omega)
  omega

private theorem endpointRoot_succ_ge (n σ base k : ℕ) :
    (4 : ℝ) * endpointRoot n σ (dyadicQuota base k) ≤
      3 * endpointRoot n σ (dyadicQuota base (k + 1)) := by
  have h0 := endpointRoot_nonneg n σ (dyadicQuota base k)
  have h1 := endpointRoot_nonneg n σ (dyadicQuota base (k + 1))
  have t0 := endpointRoot_sq n σ (dyadicQuota base k)
  have t1 := endpointRoot_sq n σ (dyadicQuota base (k + 1))
  apply (sq_le_sq₀ (mul_nonneg (by norm_num) h0) (mul_nonneg (by norm_num) h1)).mp
  rw [dyadicQuota_succ] at t1 ⊢
  push_cast at t1
  have hrad : 0 ≤ (2 : ℝ) * n * σ * (dyadicQuota base k : ℝ) := by positivity
  nlinarith only [t0, t1, hrad]

theorem endpointBudget_dyadic_sum {n σ : ℕ} (hσ : 0 < σ) (hs : σ ≤ n) (k : ℕ) :
    (∑ j ∈ range (k + 1), endpointBudget n σ (dyadicQuota (endpointBase n σ) j)) ≤
      8 * endpointBudget n σ (dyadicQuota (endpointBase n σ) k) := by
  let B := endpointBase n σ
  let R := fun j => endpointRoot n σ (dyadicQuota B j)
  have hn : 0 < n := hσ.trans_le hs
  have hbase := (endpointBase_spec hσ hs).2.2
  have n_le_R (j : ℕ) : (n : ℝ) ≤ R j := by
    have hq : B ≤ dyadicQuota B j := by
      unfold dyadicQuota
      conv_lhs => rw [← Nat.mul_one B]
      exact Nat.mul_le_mul_left B (Nat.one_le_pow _ 2 (by decide))
    have hR : (n : ℝ) ≤ endpointRoot n σ B := by
      have hbase' : (n : ℝ) ≤ 2 * ((σ : ℝ) * B) := by exact_mod_cast hbase
      unfold endpointRoot
      apply Real.le_sqrt_of_sq_le
      nlinarith only [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
        (sub_nonneg.mpr hbase')]
    exact hR.trans (endpointRoot_mono n σ hq)
  have hsum (j : ℕ) : (∑ i ∈ range (j + 1), R i) ≤ 4 * R j := by
    induction j with
    | zero =>
      have hr : 0 ≤ R 0 := endpointRoot_nonneg _ _ _
      have hs : (∑ i ∈ range (0 + 1), R i) = R 0 := by simp
      rw [hs]
      linarith only [hr]
    | succ j ih =>
      rw [sum_range_succ]
      have hr : 4 * R j ≤ 3 * R (j + 1) := endpointRoot_succ_ge n σ B j
      linarith only [ih, hr]
  have hterm : ∀ j, (endpointBudget n σ (dyadicQuota B j) : ℝ) ≤ 2 * R j := by
    intro j
    have hu := endpointBudget_le n σ (dyadicQuota B j)
    change (endpointBudget n σ (dyadicQuota B j) : ℝ) ≤ n + R j at hu
    linarith only [hu, n_le_R j]
  have result :
      (∑ j ∈ range (k + 1), (endpointBudget n σ (dyadicQuota B j) : ℝ)) ≤
        8 * endpointBudget n σ (dyadicQuota B k) := calc
    _ ≤ ∑ j ∈ range (k + 1), (2 * R j) := sum_le_sum (fun j _ => hterm j)
    _ = 2 * ∑ j ∈ range (k + 1), R j := by rw [mul_sum]
    _ ≤ _ := by
      have hr : R k ≤ (endpointBudget n σ (dyadicQuota B k) : ℝ) :=
        endpointRoot_le_budget hn _ _
      linarith only [hsum k, hr]
  exact_mod_cast result

theorem endpointBudget_final_quota {n σ p : ℕ} (hσ : 0 < σ) (hs : σ ≤ n)
    (hp : 0 < p) :
    endpointBudget n σ (dyadicQuota (endpointBase n σ) (indexLevel (endpointBase n σ) (p - 1))) ≤
      3 * endpointBudget n σ p := by
  let B := endpointBase n σ
  let q := dyadicQuota B (indexLevel B (p - 1))
  have hn : 0 < n := hσ.trans_le hs
  obtain ⟨h0, hb, _⟩ := endpointBase_spec hσ hs
  have hq : q ≤ max B (2 * p) := finalQuota_le h0 hp
  have hq' : q ≤ B ∨ q ≤ 2 * p := le_max_iff.mp hq
  have hu := endpointBudget_le n σ q
  change (endpointBudget n σ q : ℝ) ≤ n + endpointRoot n σ q at hu
  have hmin := endpointBudget_ge_n n σ p
  have result : (endpointBudget n σ q : ℝ) ≤ 3 * endpointBudget n σ p := by
    rcases hq' with hq' | hq'
    · have hBR : endpointRoot n σ B ≤ 2 * (n : ℝ) := by
        have hb' : (σ : ℝ) * B ≤ n := by exact_mod_cast hb
        unfold endpointRoot
        apply (Real.sqrt_le_iff).mpr
        constructor
        · positivity
        · nlinarith only [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
             (sub_nonneg.mpr hb'), sq_nonneg (n : ℝ)]
      have hr := (endpointRoot_mono n σ hq').trans hBR
      linarith only [hu, hmin, hr]
    · have h2 : endpointRoot n σ (2 * p) ≤ 2 * endpointRoot n σ p := by
        apply (sq_le_sq₀ (endpointRoot_nonneg _ _ _) (by unfold endpointRoot; positivity)).mp
        have he := endpointRoot_sq n σ (2 * p)
        have he' := endpointRoot_sq n σ p
        push_cast at he
        nlinarith only [he, he', sq_nonneg (endpointRoot n σ p)]
      have hr := (endpointRoot_mono n σ hq').trans h2
      have hR := endpointRoot_le_budget hn σ p
      linarith only [hu, hmin, hr, hR]
  exact_mod_cast result

variable {V : Type*} [LinearOrder V] [Fintype V]

theorem forwardRun_endpointBudget {G : Arcs V} (dag : IsDAG G) (T : List (V × V))
    (S : Finset V) (sinks : ∀ d ∈ T, d.2 ∈ S) :
    (forwardRun G T).card ≤ endpointBudget (Fintype.card V) S.card T.length := by
  let n := Fintype.card V
  let m := (forwardRun G T).card
  let q := T.length * S.card
  have h : m ^ 2 ≤ n * (m + 2 * q) := forwardRun_card_square dag T S sinks
  change m ≤ n + Nat.sqrt (2 * n * S.card * T.length)
  rw [mul_right_comm (2 * n), mul_assoc (2 * n) T.length S.card]
  change m ≤ n + Nat.sqrt (2 * n * q)
  by_cases hm : m ≤ n
  · omega
  let x := m - n
  have em : n + x = m := Nat.add_sub_of_le (by omega)
  have h' : (n + x)^2 ≤ n * ((n + x) + 2*q) := by rwa [em]
  have hx : x^2 ≤ 2*n*q := by
    nlinarith only [h', Nat.zero_le (n*x)]
  have hx' := Nat.le_sqrt'.mpr hx
  omega

end OnlineReachabilityPreservers
