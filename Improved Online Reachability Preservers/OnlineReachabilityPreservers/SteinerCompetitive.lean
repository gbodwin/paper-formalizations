import OnlineReachabilityPreservers.SteinerOnlineRounding
import OnlineReachabilityPreservers.SteinerRate

/-! Converting the early algorithm's explicit estimate to the paper's rate. -/

namespace OnlineReachabilityPreservers

universe u

open Finset
open scoped BigOperators

private theorem forestScale_polynomial {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    (G : Arcs V) (height : ℕ) :
    forestScale G height ≤
      Fintype.card V * (2 * (height + 1) * Fintype.card V ^ (height + 1)) ^ 2 := by
  let n := Fintype.card V
  have nPos : 0 < n := Fintype.card_pos
  have bound : Fintype.card (HeightForestVertex V height) ≤ 2 * (height + 1) * n ^ (height + 1) := by
    calc
      _ ≤ (n * 2) * ((height + 1) * n ^ height) := heightForestVertex_card_le V height
      _ = _ := by rw [pow_succ]; ring
  exact (forestNetworkScale_le G height).trans
    (max_le (Nat.succ_le_of_lt (by positivity)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)))

private theorem forestScale_log {height : ℕ} :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (V : Type u) [LinearOrder V] [Fintype V] [Nonempty V] (G : Arcs V),
      ((forestScale G height).log2 : ℝ) + 2 ≤ C * (1 + Real.log (Fintype.card V : ℝ)) := by
  let K : ℝ := 2 * (height + 1)
  let a := 2 * Real.log K / Real.log 2 + 2
  let b := (2 * (height : ℝ) + 3) / Real.log 2
  have K1 : 1 ≤ K := by
    dsimp [K]
    have nonneg : (0 : ℝ) ≤ height := Nat.cast_nonneg _
    linarith
  have la := Real.log_nonneg K1
  have den := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have a1 : 1 ≤ a := by
    dsimp [a]
    have : 0 ≤ 2 * Real.log K / Real.log 2 := by positivity
    linarith
  have b0 : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨a + b, by linarith, ?_⟩
  intro V _ _ _ G
  let n := Fintype.card V
  let W := forestScale G height
  let L := Real.log (n : ℝ)
  have hn : 0 < n := Fintype.card_pos
  have nPos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have L0 : 0 ≤ L := Real.log_nonneg n1
  have wPos : 0 < W := forestScale_pos G height
  have size : (W : ℝ) ≤ (n : ℝ) * (K * (n : ℝ) ^ (height + 1)) ^ 2 := by
    dsimp [W, n, K]
    exact_mod_cast forestScale_polynomial G height
  have shape : Real.log ((n : ℝ) * (K * (n : ℝ) ^ (height + 1)) ^ 2) =
      2 * Real.log K + (2 * (height : ℝ) + 3) * L := by
    rw [Real.log_mul nPos.ne' (by positivity), Real.log_pow,
      Real.log_mul (zero_lt_one.trans_le K1).ne' (by positivity), Real.log_pow]
    push_cast
    dsimp only [L]
    ring
  have logBound := (Real.log_le_log (Nat.cast_pos.mpr wPos) size).trans_eq shape
  have lo := (nat_log2_le_log wPos).trans (div_le_div_of_nonneg_right logBound den.le)
  change (W.log2 : ℝ) + 2 ≤ (a + b) * (1 + L)
  have mid : (W.log2 : ℝ) + 2 ≤ a + b * L := by
    calc
      _ ≤ (2 * Real.log K + (2 * (height : ℝ) + 3) * L) / Real.log 2 + 2 :=
        add_le_add lo le_rfl
      _ = _ := by dsimp [a, b]; ring
  exact mid.trans (by nlinarith only [mul_nonneg (zero_le_one.trans a1) L0, b0])

private theorem earlyRoundingFactor_polylog {height : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Type u) [LinearOrder V] [Fintype V] [Nonempty V] (G : Arcs V),
      ((forestScale G height).log2 : ℝ) + 2 ≤ C * (1 + Real.log (Fintype.card V : ℝ)) ∧
      (earlyRoundingFactor G height : ℝ) ≤ C * (1 + Real.log (Fintype.card V : ℝ)) ^ (height + 3) := by
  obtain ⟨A, A1, logBound⟩ := forestScale_log.{u} (height := height)
  let B : ℝ := 16 * (height + 1 : ℝ) ^ 2 * (1 / Real.log 2 + 1)
  have den := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have A0 : 0 ≤ A := zero_le_one.trans A1
  have B0 : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := A + 2 * B * A ^ (height + 2)
  have AC : A ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C, A0.trans AC, ?_⟩
  intro V _ _ _ G
  let n := Fintype.card V
  let W := forestScale G height
  let Y := 1 + Real.log (n : ℝ)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (Fintype.card_pos (α := V))
  have Y1 : 1 ≤ Y := le_add_of_nonneg_right (Real.log_nonneg n1)
  have Y0 : 0 ≤ Y := zero_le_one.trans Y1
  have wb : (W.log2 : ℝ) + 2 ≤ A * Y := logBound V G
  refine ⟨wb.trans (mul_le_mul_of_nonneg_right AC Y0), ?_⟩
  have reps : (earlyTrialCount V height : ℝ) ≤ B * Y := by
    have ll : (n.log2 : ℝ) + 1 ≤ (1 / Real.log 2 + 1) * Y := by
      have log := nat_log2_le_log (Fintype.card_pos (α := V))
      have extra : 0 ≤ 1 / Real.log 2 + Real.log (n : ℝ) :=
        add_nonneg (by positivity) (Real.log_nonneg n1)
      calc
        _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 := add_le_add log le_rfl
        _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 + (1 / Real.log 2 + Real.log (n : ℝ)) :=
          le_add_of_nonneg_right extra
        _ = _ := by dsimp only [Y]; ring
    simp only [earlyTrialCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    dsimp only [B, n] at *
    calc
      _ ≤ (16 * (height + 1 : ℝ) ^ 2) * ((1 / Real.log 2 + 1) * Y) :=
        mul_le_mul_of_nonneg_left ll (by positivity)
      _ = _ := by ring
  change (earlyRoundingFactor G height : ℝ) ≤ C * Y ^ (height + 3)
  simp only [earlyRoundingFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_pow]
  change 2 * (earlyTrialCount V height : ℝ) * ((W.log2 : ℝ) + 1) * ((W.log2 : ℝ) + 2) ^ (height + 1) ≤ _
  calc
    _ ≤ 2 * (B * Y) * (A * Y) * (A * Y) ^ (height + 1) := by
      have w1 : (W.log2 : ℝ) + 1 ≤ A * Y := by linarith only [wb]
      gcongr
    _ = (2 * B * A ^ (height + 2)) * Y ^ (height + 3) := by
      rw [mul_pow, show height + 2 = (height + 1) + 1 from rfl,
        show height + 3 = (height + 1) + 2 from rfl, pow_succ A, pow_add Y]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left A0) (by positivity)

private theorem early_pairs_power_le {p : ℕ} (pPos : 0 < p) (height : ℕ) :
    (p : ℝ) ^ (1/(height : ℝ)) * ((Nat.sqrt p : ℝ)+1) ≤ 2*(p : ℝ) ^ (1/(height : ℝ)+1/2) := by
  have p1 : (1 : ℝ) ≤ p := by exact_mod_cast pPos
  have sq : (Nat.sqrt p : ℝ) ≤ (p : ℝ) ^ (1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' p)
  have sq1 : 1 ≤ (p : ℝ) ^ (1/2 : ℝ) := Real.one_le_rpow p1 (by norm_num)
  calc
    _ ≤ (p : ℝ) ^ (1/(height : ℝ)) * (2*(p : ℝ) ^ (1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [sq,sq1]) (by positivity)
    _ = _ := by rw [Real.rpow_add (by positivity : 0 < (p : ℝ))]; ring

private theorem early_pairs_term {n p height : ℕ} {ε : ℝ}
    (nPos : 0 < n) (pPos : 0 < p) (hPos : 0 < height) (pBound : p ≤ steinerEarlyCutoff n)
    (slack : (6 : ℝ) / (5 * (height : ℝ)) ≤ ε / 2) :
    (p : ℝ) ^ (1 / (height : ℝ)) * ((Nat.sqrt p : ℝ) + 1) ≤
      8 * (n : ℝ) ^ (3/5 + ε / 2) := by
  let ζ : ℝ := 1 / (height : ℝ)
  let θ : ℝ := ζ + 1/2
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast nPos
  have h1 : (1 : ℝ) ≤ height := by exact_mod_cast hPos
  have ζ1 : ζ ≤ 1 := (div_le_iff₀ (zero_lt_one.trans_le h1)).mpr (by simpa using h1)
  have nonnegative : 0 ≤ θ := by dsimp [θ, ζ]; positivity
  have θ2 : θ ≤ 2 := by dsimp [θ]; linarith
  have power : (6/5 : ℝ) * θ ≤ 3/5 + ε / 2 := by
    change (6 : ℝ) / (5 * (height : ℝ)) ≤ ε/2 at slack
    have eq : (6/5 : ℝ) * ζ = 6 / (5 * (height : ℝ)) := by dsimp [ζ]; ring
    dsimp [θ]
    linarith only [eq, slack]
  have hP : (p : ℝ) ≤ 2 * (n : ℝ) ^ (6/5 : ℝ) :=
    (Nat.cast_le.mpr pBound).trans (steinerEarlyCutoff_bounds nPos).2
  have hTwo : (2 : ℝ) ^ θ ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) θ2
      _ = 4 := by rw [Real.rpow_two]; norm_num
  calc
    _ ≤ 2 * (p : ℝ) ^ θ := early_pairs_power_le pPos height
    _ ≤ 2 * (2 * (n : ℝ) ^ (6/5 : ℝ)) ^ θ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hP nonnegative) (by positivity)
    _ = 2 * ((2 : ℝ) ^ θ * (n : ℝ) ^ ((6/5 : ℝ) * θ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ _ := by
      have lim := Real.rpow_le_rpow_of_exponent_le n1 power
      nlinarith only [mul_le_mul hTwo lim (by positivity) (by positivity)]

/-- At a fixed positive exponent slack, choose a fixed-height template.
Its early cost fits the cutoff contribution of Theorem 21. -/
theorem earlyRoundedGraph_rate {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [LinearOrder V] [Fintype V] [Nonempty V] {G Z : Arcs V}
        (D : List (V × V)), D.Nodup → D.length ≤ steinerEarlyCutoff (Fintype.card V) →
        0 < Z.card → Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (𝔼 sample : EarlyRoundSample G height, ((earlyRoundedGraph G height D sample).card : ℝ)) ≤
          K * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨h, hBig⟩ := exists_nat_gt (max (1 : ℝ) (12 / (5 * ε)))
  have hReal : (1 : ℝ) < h := (le_max_left _ _).trans_lt hBig
  have hPositiveReal : (0 : ℝ) < h := zero_lt_one.trans hReal
  have hPos : 0 < h := Nat.cast_pos.mp hPositiveReal
  have slack : (6 : ℝ) / (5 * (h : ℝ)) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have bound := (div_lt_iff₀ (show 0 < 5 * ε by positivity)).mp ((le_max_right _ _).trans_lt hBig)
    nlinarith only [bound]
  obtain ⟨C, C0, polylogs⟩ := earlyRoundingFactor_polylog.{u} (height := h)
  obtain ⟨A, A1, absorb⟩ := log_power_absorption (show 0 < ε/2 by positivity) (h+4)
  have A0 := zero_le_one.trans A1
  let F : ℝ := 2 + 96 * (h : ℝ) * C
  let K := C * F * A + 2
  have F0 : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨h, hPos, K, by dsimp [K]; positivity, ?_⟩
  intro V _ _ _ G Z D distinct cutoff Zpos sub feasible
  let n := Fintype.card V
  let W := forestScale G h
  let Y := 1 + Real.log (n : ℝ)
  let X := (n : ℝ) ^ (3/5 + ε / 2)
  let X' := (n : ℝ) ^ (3/5 + ε)
  let p := D.length
  have npos : 0 < n := Fintype.card_pos
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast npos
  have n0 : (0 : ℝ) < n := zero_lt_one.trans_le n1
  have Z1 : (1 : ℝ) ≤ Z.card := by exact_mod_cast Zpos
  have Y1 : 1 ≤ Y := le_add_of_nonneg_right (Real.log_nonneg n1)
  have Y0 := zero_le_one.trans Y1
  have X1 : 1 ≤ X := Real.one_le_rpow n1 (by positivity)
  have X0 := zero_le_one.trans X1
  have X'1 : 1 ≤ X' := Real.one_le_rpow n1 (by positivity)
  have X'0 := zero_le_one.trans X'1
  by_cases empty : D = []
  · subst D
    simpa [earlyRoundedGraph_empty] using (show 0 ≤ K * X' * Z.card by positivity)
  have pPos : 0 < p := List.length_pos_of_ne_nil empty
  have main := earlyRoundedGraph_mean_le G Z sub hPos D distinct pPos feasible
  obtain ⟨logW, round⟩ := polylogs V G
  have WUpper : ((W.log2 + 1 : ℕ) : ℝ) ≤ C * Y := by
    push_cast
    exact (show (W.log2 : ℝ) + 1 ≤ (W.log2 : ℝ) + 2 by linarith).trans logW
  have pairs := early_pairs_term npos pPos hPos cutoff slack
  have unit : (1 : ℝ) ≤ Y * X * (Z.card : ℝ) := by
    apply one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le Y1 X1) Z1
  have additive : (2 : ℝ) ≤ 2 * (Y * X * (Z.card : ℝ)) := by linarith only [unit]
  have center :
      2 + ((W.log2 + 1 : ℕ) : ℝ) *
        (12 * (h : ℝ) * (p : ℝ) ^ (1 / (h : ℝ)) * ((Nat.sqrt p : ℝ) + 1) * (Z.card : ℝ)) ≤
      F * (Y * X * (Z.card : ℝ)) := by
    calc
      _ ≤ 2 * (Y * X * (Z.card : ℝ)) + (C * Y) * (12 * (h : ℝ) * (8 * X) * (Z.card : ℝ)) := by
        refine add_le_add additive (mul_le_mul WUpper ?_ (by positivity) (by positivity))
        rw [mul_assoc (12 * (h : ℝ))]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pairs (by positivity)) (by positivity)
      _ = _ := by dsimp [F]; ring
  have product :
      (C * Y ^ (h+3)) * (F * (Y * X * (Z.card : ℝ))) ≤ C * F * A * X' * (Z.card : ℝ) := by
    calc
      _ = C * F * (Y ^ (h+4) * X) * (Z.card : ℝ) := by rw [pow_succ Y (h+3)]; ring
      _ ≤ C * F * ((A * (n : ℝ) ^ (ε / 2)) * X) * (Z.card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (absorb n1) X0) (by positivity)) (by positivity)
      _ = C * F * A * ((n : ℝ) ^ (ε / 2) * X) * (Z.card : ℝ) := by ring
      _ = _ := by
        have powEq : (n : ℝ) ^ (ε/2) * X = X' := by
          dsimp only [X, X']
          rw [← Real.rpow_add n0]
          congr 1
          ring
        rw [powEq]
  have rounded := (mul_le_mul round center (by positivity) (by positivity)).trans product
  have unit' : (1 : ℝ) ≤ X' * (Z.card : ℝ) := one_le_mul_of_one_le_of_one_le X'1 Z1
  refine main.trans ?_
  change _ ≤ K * X' * (Z.card : ℝ)
  dsimp only [K]
  nlinarith only [rounded, unit']

/-- The early rule's demand-dependent guarantee. At fixed slack, the
height and graph polylogarithm degree are independent of the demand count. -/
theorem earlyRoundedGraph_pairs_rate {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [LinearOrder V] [Fintype V] [Nonempty V] {G Z : Arcs V}
        (D : List (V × V)), D.Nodup → (∀ d ∈ D, d.1 ≠ d.2) →
        Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (𝔼 sample : EarlyRoundSample G height, ((earlyRoundedGraph G height D sample).card : ℝ)) ≤
          K * (1 + Real.log (Fintype.card V : ℝ)) ^ (height+4) *
            (D.length : ℝ) ^ (1/2+ε) * Z.card := by
  obtain ⟨h, big⟩ := exists_nat_gt (max (1 : ℝ) (1/ε))
  have hReal : (0 : ℝ) < h := lt_trans zero_lt_one ((le_max_left _ _).trans_lt big)
  have hPos : 0 < h := Nat.cast_pos.mp hReal
  have slack : (1 : ℝ) / h ≤ ε := by
    apply (div_le_iff₀ hReal).mpr
    have strict := (div_lt_iff₀ epsilon).mp ((le_max_right _ _).trans_lt big)
    linarith only [strict]
  obtain ⟨C, C0, polylogs⟩ := earlyRoundingFactor_polylog.{u} (height := h)
  let F : ℝ := 2 + 24 * (h : ℝ) * C
  let K : ℝ := C * F + 2
  refine ⟨h, hPos, K, by dsimp [K,F]; positivity, ?_⟩
  intro V _ _ _ G Z D distinct nonself sub feasible
  let n := Fintype.card V
  let p := D.length
  let Y := 1 + Real.log (n : ℝ)
  let X := (p : ℝ) ^ (1/2+ε)
  let W := forestScale G h
  by_cases empty : D = []
  · subst D
    simp only [earlyRoundedGraph_empty, card_empty, Nat.cast_zero, expect_const_zero]
    dsimp only [K, F]
    positivity
  have pPos : 0 < p := List.length_pos_of_ne_nil empty
  have Zpos : 0 < Z.card := by
    obtain ⟨d, hd⟩ : ∃ d, d ∈ D := by cases D <;> simp_all
    by_contra! zero
    have eq : Z = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero zero)
    have path : Reach (∅ : Arcs V) d.1 d.2 := eq ▸ feasible d hd
    have onlySelf {s t : V} (p : Reach (∅ : Arcs V) s t) : s = t := by
      cases p with
      | refl => rfl
      | tail _ edge => exact (notMem_empty _ edge).elim
    exact nonself d hd (onlySelf path)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (Fintype.card_pos (α := V))
  have p1 : (1 : ℝ) ≤ p := by exact_mod_cast pPos
  have Z1 : (1 : ℝ) ≤ Z.card := by exact_mod_cast Zpos
  have Y1 : 1 ≤ Y := le_add_of_nonneg_right (Real.log_nonneg n1)
  have X1 : 1 ≤ X := Real.one_le_rpow p1 (by positivity)
  have main := earlyRoundedGraph_mean_le G Z sub hPos D distinct pPos feasible
  obtain ⟨logW, rounded⟩ := polylogs V G
  have WUpper : ((W.log2 + 1 : ℕ) : ℝ) ≤ C * Y := by
    push_cast
    exact (show (W.log2 : ℝ) + 1 ≤ (W.log2 : ℝ) + 2 by linarith).trans logW
  have pairs : (p : ℝ) ^ (1/(h : ℝ)) * ((Nat.sqrt p : ℝ)+1) ≤ 2*X := by
    calc
      _ ≤ 2*(p : ℝ) ^ (1/(h : ℝ)+1/2) := early_pairs_power_le pPos h
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le p1 (by linarith only [slack])) (by norm_num)
  have unit : (1 : ℝ) ≤ Y * X * Z.card :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le Y1 X1) Z1
  have center :
      2 + ((W.log2 + 1 : ℕ) : ℝ) *
        (12 * (h : ℝ) * (p : ℝ) ^ (1 / (h : ℝ)) * ((Nat.sqrt p : ℝ) + 1) * (Z.card : ℝ)) ≤
      F * (Y * X * (Z.card : ℝ)) := by
    calc
      _ ≤ 2 * (Y * X * (Z.card : ℝ)) + (C * Y) * (12 * (h : ℝ) * (2 * X) * (Z.card : ℝ)) := by
        refine add_le_add (by linarith only [unit]) (mul_le_mul WUpper ?_ (by positivity) (by positivity))
        rw [mul_assoc (12 * (h : ℝ))]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pairs (by positivity)) (by positivity)
      _ = _ := by dsimp [F]; ring
  have kept : (earlyRoundingFactor G h : ℝ) *
      (2 + ((W.log2 + 1 : ℕ) : ℝ) *
        (12 * (h : ℝ) * (p : ℝ) ^ (1 / (h : ℝ)) * ((Nat.sqrt p : ℝ) + 1) * (Z.card : ℝ))) ≤
      C * F * (Y ^ (h+4) * X * (Z.card : ℝ)) := by
    refine (mul_le_mul rounded center (by positivity) (by positivity)).trans_eq ?_
    rw [pow_succ Y (h+3)]
    ring
  have unit' : (1 : ℝ) ≤ Y ^ (h+4) * X * (Z.card : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ Y1) X1) Z1
  refine main.trans ?_
  change _ ≤ K * Y^(h+4) * X * Z.card
  dsimp only [K]
  nlinarith only [kept,unit']

end OnlineReachabilityPreservers
