import GreedyShortcuts.DAGProgress
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact square-root parameter balancing for the proved DAG size bound. -/
namespace GreedyShortcuts.DAGBalance

open DAGProgress

noncomputable def parameter (n β : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt ((β:ℝ)^3/(n:ℝ))) + 8

theorem parameter_ge (n β : ℕ) : 8 ≤ parameter n β := by unfold parameter; omega

theorem sqrt_product {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    Real.sqrt (b^3/n)*Real.sqrt (n^3/b^3) = n := by
  rw [← Real.sqrt_mul (by positivity)]
  have he : b^3/n*(n^3/b^3) = n^2 := by field_simp
  rw [he,Real.sqrt_sq hn.le]

theorem sqrt_scaled {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    Real.sqrt (b^3/n)*n^2/b^3 = Real.sqrt (n^3/b^3) := by
  have hp := sqrt_product hn hb
  have hs : (Real.sqrt (b^3/n))^2*n = b^3 := by rw [Real.sq_sqrt (by positivity)]; field_simp
  apply (div_eq_iff (show b^3 ≠ 0 by positivity)).mpr
  calc
    Real.sqrt (b^3/n)*n^2 =
      (Real.sqrt (b^3/n)*Real.sqrt (n^3/b^3))*Real.sqrt (b^3/n)*n := by rw [hp]; ring
    _ = Real.sqrt (n^3/b^3)*((Real.sqrt (b^3/n))^2*n) := by ring
    _ = _ := by rw [hs]

/-- A uniform explicit upper bound on the integer progress denominator. -/
theorem blockLength_bound (n β : ℕ) (hn : 0 < n) (hβ : 0 < β) :
    (blockLength n β (parameter n β) : ℝ) ≤
      16384*Real.sqrt ((n:ℝ)^3/(β:ℝ)^3) + 147456*(n:ℝ)^2/(β:ℝ)^3 + 1 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb' : 0 < (β:ℝ) := by exact_mod_cast hβ
  let t := Real.sqrt ((β:ℝ)^3/(n:ℝ))
  let r := Real.sqrt ((n:ℝ)^3/(β:ℝ)^3)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hlow : t ≤ (parameter n β : ℝ) := by
    have hh := Nat.le_ceil t
    dsimp [parameter,t] at *
    push_cast
    linarith
  have hupp : (parameter n β : ℝ) ≤ t+9 := by
    have hh := Nat.ceil_lt_add_one ht
    dsimp [parameter,t] at *
    push_cast
    linarith
  have hs : 0 < (parameter n β : ℝ) := by exact_mod_cast (show 0 < parameter n β by have := parameter_ge n β; omega)
  have hprod : t*r = (n:ℝ) := sqrt_product hn' hb'
  have hscaled : t*(n:ℝ)^2/(β:ℝ)^3 = r := sqrt_scaled hn' hb'
  have hfirst : (512*n/parameter n β : ℕ) ≤ (512*r : ℝ) := by
    calc
      ((512*n/parameter n β : ℕ):ℝ) ≤ ((512*n:ℕ):ℝ)/(parameter n β:ℝ) := Nat.cast_div_le
      _ = 512*(n:ℝ)/(parameter n β:ℝ) := by norm_cast
      _ ≤ 512*r := (div_le_iff₀ hs).mpr (by nlinarith)
  have hsecond : ((16384*parameter n β*n^2/β^3 : ℕ):ℝ) ≤
      16384*r+147456*(n:ℝ)^2/(β:ℝ)^3 := by
    calc
      _ ≤ ((16384*parameter n β*n^2:ℕ):ℝ)/((β^3:ℕ):ℝ) := Nat.cast_div_le
      _ = 16384*(parameter n β:ℝ)*(n:ℝ)^2/(β:ℝ)^3 := by push_cast; rfl
      _ ≤ 16384*(t+9)*(n:ℝ)^2/(β:ℝ)^3 := by gcongr
      _ = 16384*r+147456*(n:ℝ)^2/(β:ℝ)^3 := by rw [← hscaled]; ring
  unfold blockLength
  rw [Nat.cast_max]
  push_cast
  apply max_le
  · have hnon : 0 ≤ 147456*(n:ℝ)^2/(β:ℝ)^3 := by positivity
    dsimp only [r] at hfirst hr
    nlinarith
  · dsimp only [r] at hsecond
    linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The optimized square-root bound, with an explicit finite logarithm and
absolute constants, for every positive target. -/
theorem output_card_bound {G : V → V → Prop} (hG : CanonicalSegments.Acyclic G)
    (β : ℕ) (hβ : 1 ≤ β) (hn : 0 < Fintype.card V) :
    ((GraphGreedy.output G β hβ).card : ℝ) ≤
      (Nat.log 2 ((Fintype.card V)^3)+1 : ℕ) *
        (16384*Real.sqrt ((Fintype.card V:ℝ)^3/(β:ℝ)^3) +
          147456*(Fintype.card V:ℝ)^2/(β:ℝ)^3+1) := by
  let n := Fintype.card V
  let B := 16384*Real.sqrt ((n:ℝ)^3/(β:ℝ)^3)+147456*(n:ℝ)^2/(β:ℝ)^3+1
  change ((GraphGreedy.output G β hβ).card : ℝ) ≤ (Nat.log 2 (n^3)+1 : ℕ)*B
  by_cases hb : 8 ≤ β
  · have hc := DAGProgress.output_card_bound hG β (parameter n β) hb (parameter_ge n β)
    have hc' : ((GraphGreedy.output G β hβ).card : ℝ) ≤
        (Nat.log 2 (n^3)+1 : ℕ)*(blockLength n β (parameter n β) : ℝ) := by exact_mod_cast hc
    exact hc'.trans (mul_le_mul_of_nonneg_left (blockLength_bound n β hn (by omega)) (by positivity))
  · have hb' : 0 < (β:ℝ) := by exact_mod_cast (show 0 < β by omega)
    have hpow : (β:ℝ)^3 ≤ 147456 := by
      have hh := Nat.pow_le_pow_left (show β ≤ 7 by omega) 3
      have hh' : (β:ℝ)^3 ≤ (343:ℝ) := by exact_mod_cast hh
      linarith
    have hbase : (n:ℝ)^2 ≤ 147456*(n:ℝ)^2/(β:ℝ)^3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg (n:ℝ))]
    have hB : (n:ℝ)^2 ≤ B := by
      have hs := Real.sqrt_nonneg ((n:ℝ)^3/(β:ℝ)^3)
      dsimp [B]
      linarith
    have hk : (1:ℝ) ≤ (Nat.log 2 (n^3)+1 : ℕ) := by exact_mod_cast (show 1 ≤ Nat.log 2 (n^3)+1 by omega)
    calc
      ((GraphGreedy.output G β hβ).card : ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast GraphGreedy.output_card_le G β hβ
      _ ≤ B := hB
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hk (le_trans (sq_nonneg (n:ℝ)) hB)

theorem sqrt_ratio_rpow (n b : ℝ) (hn : 0 ≤ n) (hb : 0 ≤ b) :
    Real.sqrt (n^3/b^3) = n^(3/(2:ℝ))/b^(3/(2:ℝ)) := by
  rw [Real.sqrt_div (by positivity),Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul hn 3 (1/(2:ℝ)),← Real.rpow_natCast_mul hb 3 (1/(2:ℝ))]
  norm_num

/-- The source-shaped DAG bound for the natural nontrivial parameter range
1 ≤ β ≤ n. It is a theorem about the actual greedy output, not an existence
statement about an unrelated shortcut construction. -/
theorem output_card_power_bound {G : V → V → Prop} (hG : CanonicalSegments.Acyclic G)
    (β : ℕ) (hβ : 1 ≤ β) (hβn : β ≤ Fintype.card V) :
    ((GraphGreedy.output G β hβ).card : ℝ) ≤
      (Nat.log 2 ((Fintype.card V)^3)+1 : ℕ) *
        (16385*(Fintype.card V:ℝ)^(3/(2:ℝ))/(β:ℝ)^(3/(2:ℝ)) +
          147456*(Fintype.card V:ℝ)^2/(β:ℝ)^3) := by
  have hn : 0 < Fintype.card V := by omega
  have hb : 0 < (β:ℝ) := by exact_mod_cast (show 0 < β by omega)
  have hratio : 1 ≤ Real.sqrt ((Fintype.card V:ℝ)^3/(β:ℝ)^3) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num
    exact_mod_cast Nat.pow_le_pow_left hβn 3
  have hbound := output_card_bound hG β hβ hn
  have hr := sqrt_ratio_rpow (Fintype.card V:ℝ) (β:ℝ) (by positivity) (by positivity)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_div_assoc 16385,← hr]
  nlinarith

theorem log_cube_bound (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n^3)+1 : ℕ) ≤ (4*Real.logb 2 (n:ℝ) : ℝ) := by
  have hlog := Real.natLog_le_logb (n^3) 2
  norm_num only [Nat.cast_ofNat,Nat.cast_pow,Real.logb_pow] at hlog
  have hnlog : 1 ≤ Nat.log 2 n :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by simpa using hn)
  have hl : (1:ℝ) ≤ Real.logb 2 (n:ℝ) :=
    (show (1:ℝ) ≤ (Nat.log 2 n:ℝ) by exact_mod_cast hnlog).trans (Real.natLog_le_logb n 2)
  push_cast
  linarith

/-- The original DAG theorem with its hidden logarithmic factor made explicit.
The general-directed preprocessing is a separate cited reduction. -/
theorem output_card_log_bound {G : V → V → Prop} (hG : CanonicalSegments.Acyclic G)
    (β : ℕ) (hβ : 1 ≤ β) (hβn : β ≤ Fintype.card V) (hn : 2 ≤ Fintype.card V) :
    ((GraphGreedy.output G β hβ).card : ℝ) ≤
      4*Real.logb 2 (Fintype.card V:ℝ) *
        (16385*(Fintype.card V:ℝ)^(3/(2:ℝ))/(β:ℝ)^(3/(2:ℝ)) +
          147456*(Fintype.card V:ℝ)^2/(β:ℝ)^3) := by
  exact (output_card_power_bound hG β hβ hβn).trans
    (mul_le_mul_of_nonneg_right (log_cube_bound (Fintype.card V) hn) (by positivity))

end GreedyShortcuts.DAGBalance
