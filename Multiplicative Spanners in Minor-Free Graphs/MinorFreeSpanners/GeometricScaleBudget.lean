import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite geometric scale sums are paid by their largest processed scale.
These estimates permit an explicit per-scale auxiliary bill without multiplying
it by the number of levels. Graph-edge bounds and an actual bill certificate
must be supplied by the phase construction. -/
namespace MinorFreeSpanners
open Finset

 theorem geometric_prefix_mass_bound (t u : ℝ) (ht : 2≤t) (hu : 0≤u) (n : ℕ) :
    (∑ i∈range (n+1),u*t^i)≤2*(u*t^n) := by
  induction n with
  | zero => simpa using (show u≤2*u by linarith)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0≤u*t^n := mul_nonneg hu (pow_nonneg (by linarith) _)
    have hg := mul_le_mul_of_nonneg_left ht hp
    have hnext : 2*(u*t^n)≤u*t^(n+1) := by
      rw [pow_succ]
      nlinarith only [hg]
    linarith only [ih,hnext]

 theorem geometric_processed_mass_bound (t u budget : ℝ)
    (ht : 2≤t) (hu : 0≤u) (S : Finset ℕ) (n : ℕ)
    (hS : S⊆range (n+1)) (hmax : u*t^n≤2*budget) :
    (∑ i∈S,u*t^i)≤4*budget := by
  have hsub : (∑ i∈S,u*t^i)≤∑ i∈range (n+1),u*t^i :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ =>
      mul_nonneg hu (pow_nonneg (by linarith) i))
  have hp := geometric_prefix_mass_bound t u ht hu n
  linarith only [hsub,hp,hmax]

end MinorFreeSpanners
