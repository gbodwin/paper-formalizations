import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import OnlineReachabilityPreservers.Majorization

/-! Lemma 30 with explicit interval integrability. -/

namespace OnlineReachabilityPreservers

open Finset MeasureTheory intervalIntegral

/-- The integral prefix bounds in Lemma 30 imply the square-sum bound.
Both the function and its square are interval integrable. -/
theorem lemma30_integral_square_sum (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (nonneg : ∀ i < n, 0 ≤ a i)
    (decreasing : ∀ i j, i ≤ j → j < n → a j ≤ a i)
    (integrable : IntervalIntegrable f volume 0 (n : ℝ))
    (square_integrable : IntervalIntegrable (fun x => (f x)^2) volume 0 (n : ℝ))
    (prefixBounds : ∀ k ≤ n, (∑ i ∈ range k, a i) ≤ ∫ x in 0..(k : ℝ), f x) :
    (∑ i ∈ range n, (a i)^2) ≤ ∫ x in 0..(n : ℝ), (f x)^2 := by
  let b (i : ℕ) := ∫ x in (i : ℝ)..((i+1 : ℕ) : ℝ), f x
  have contained (i : ℕ) (hi : i < n) :
      Set.uIcc (i : ℝ) ((i+1 : ℕ) : ℝ) ⊆ Set.uIcc 0 (n : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ i), Set.uIcc_of_le (by positivity)]
    exact Set.Icc_subset_Icc (by positivity) (by exact_mod_cast Nat.succ_le_of_lt hi)
  have hsum (k : ℕ) (hk : k ≤ n) : (∑ i ∈ range k, b i) = ∫ x in 0..(k : ℝ), f x := by
    have hcell : ∀ i < k, IntervalIntegrable f volume (i : ℝ) ((i+1 : ℕ) : ℝ) :=
      fun i hi => integrable.mono_set (contained i (hi.trans_le hk))
    simpa only [b, Nat.cast_zero] using sum_integral_adjacent_intervals hcell
  apply (lemma29_square_sum n a b nonneg decreasing (fun k hk => (prefixBounds k hk).trans_eq (hsum k hk).symm)).trans
  have hcell : ∀ i < n, IntervalIntegrable (fun x => (f x)^2) volume (i : ℝ) ((i+1 : ℕ) : ℝ) :=
    fun i hi => square_integrable.mono_set (contained i hi)
  have hsq : ∀ i < n, (b i)^2 ≤ ∫ x in (i : ℝ)..((i+1 : ℕ) : ℝ), (f x)^2 := by
    intro i hi
    have hfi := integrable.mono_set (contained i hi)
    have hqi := hcell i hi
    have hconst : IntervalIntegrable (fun _ : ℝ => (b i)^2) volume (i:ℝ) ((i+1 : ℕ):ℝ) :=
      intervalIntegrable_const
    have hpoly : (fun x => (f x - b i)^2) = fun x => (f x)^2 - (2*b i)*f x + (b i)^2 := by
      funext x
      ring
    have nonnegative : 0 ≤ ∫ x in (i:ℝ)..((i+1 : ℕ):ℝ), (f x - b i)^2 :=
      integral_nonneg_of_forall (by exact_mod_cast Nat.le_succ i) (fun _ => sq_nonneg _)
    rw [hpoly, integral_add (hqi.sub (hfi.const_mul _)) hconst,
      integral_sub hqi (hfi.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      smul_eq_mul] at nonnegative
    change 0 ≤ (∫ x in (i:ℝ)..((i+1:ℕ):ℝ), (f x)^2) - 2*b i*b i +
      (((i+1:ℕ):ℝ)-(i:ℝ))*(b i)^2 at nonnegative
    push_cast at nonnegative ⊢
    nlinarith only [nonnegative]
  refine (sum_le_sum (fun i hi => hsq i (mem_range.mp hi))).trans_eq ?_
  simpa only [Nat.cast_zero] using sum_integral_adjacent_intervals hcell

end OnlineReachabilityPreservers
