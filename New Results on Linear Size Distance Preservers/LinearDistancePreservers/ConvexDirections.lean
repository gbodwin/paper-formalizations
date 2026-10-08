import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A concrete strict-convexity ingredient for the unweighted construction
in Section 4.3. Integer vectors on one sphere cannot average to a different
vector on that sphere. The modular version explicitly proves that the
coordinate sums do not wrap; no Euclidean intuition is substituted for it.
This module does not assert the sharp lattice-set cardinality of Theorem 6. -/
namespace LinearDistancePreservers.ConvexDirections
open Finset

/-- Equality in the squared-distance identity forces every summand to be
the target vector. This also works for a zero-dimensional coordinate set. -/
theorem sphere_average_unique {D : Type*} [Fintype D] {m : ℕ}
    (v : Fin m → D → ℤ) (a : D → ℤ)
    (hsphere : ∀ i, ∑ j, (v i j)^2 = ∑ j, (a j)^2)
    (hsum : ∀ j, ∑ i, v i j = (m : ℤ) * a j) : ∀ i, v i = a := by
  have hvariance (j : D) :
      ∑ i, (v i j - a j)^2 = (∑ i, (v i j)^2) - (m : ℤ)*(a j)^2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
    ring
  have hz : ∑ i, ∑ j, (v i j - a j)^2 = 0 := by
    rw [sum_comm]
    simp_rw [hvariance]
    rw [sum_sub_distrib, sum_comm, ← mul_sum]
    simp [hsphere]
  have heach := (sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (univ : Finset (Fin m))) =>
      sum_nonneg (fun j _ => sq_nonneg (v i j - a j)))).mp hz
  intro i
  have hi := (sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (univ : Finset D)) => sq_nonneg (v i j - a j))).mp
    (heach i (mem_univ _))
  funext j
  have hj := hi j (mem_univ _)
  nlinarith [sq_nonneg (v i j - a j)]

/-- Coordinatewise modular endpoint equality is ordinary sum equality
when each total displacement is strictly below the modulus. -/
theorem no_wrap_sum {D : Type*} {m r n : ℕ}
    (v : Fin m → D → ℕ) (a : D → ℕ)
    (hv : ∀ i j, v i j < r) (ha : ∀ j, a j < r)
    (hn : (m+1)*r ≤ n)
    (he : ∀ j, (∑ i, (v i j : ZMod n)) = (m : ZMod n) * (a j : ZMod n)) :
    ∀ j, ∑ i, (v i j : ℤ) = (m : ℤ) * (a j : ℤ) := by
  intro j
  have hmod := (ZMod.intCast_eq_intCast_iff'
    (∑ i, (v i j : ℤ)) ((m : ℤ) * (a j : ℤ)) n).mp (by simpa using he j)
  have hr : (0 : ℤ) < r := by exact_mod_cast (Nat.zero_lt_of_lt (ha j))
  have hn' : ((m : ℤ)+1)*r ≤ n := by exact_mod_cast hn
  have hs0 : 0 ≤ ∑ i, (v i j : ℤ) := sum_nonneg fun i _ => by positivity
  have hsle : ∑ i, (v i j : ℤ) ≤ (m : ℤ)*r := by
    calc
      _ ≤ ∑ _i : Fin m, (r : ℤ) := sum_le_sum fun i _ => by exact_mod_cast (hv i j).le
      _ = _ := by simp
  have hslt : ∑ i, (v i j : ℤ) < n := by nlinarith
  have ha' : (a j : ℤ) < r := by exact_mod_cast ha j
  have halt : (m : ℤ)*(a j : ℤ) < n := by
    have := mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg m)
    nlinarith
  simpa only [Int.emod_eq_of_lt hs0 hslt, Int.emod_eq_of_lt (by positivity) halt] using hmod

/-- Thus a forward modular route with common-sphere directions and the
constant-direction endpoints must use that direction at every step. -/
theorem modular_sphere_unique {D : Type*} [Fintype D] {m r n : ℕ}
    (v : Fin m → D → ℕ) (a : D → ℕ)
    (hv : ∀ i j, v i j < r) (ha : ∀ j, a j < r)
    (hn : (m+1)*r ≤ n)
    (hsphere : ∀ i, ∑ j, (v i j : ℤ)^2 = ∑ j, (a j : ℤ)^2)
    (he : ∀ j, (∑ i, (v i j : ZMod n)) = (m : ZMod n) * (a j : ZMod n)) :
    ∀ i, v i = a := by
  have hu := sphere_average_unique (fun i j => (v i j : ℤ)) (fun j => (a j : ℤ))
    hsphere (no_wrap_sum v a hv ha hn he)
  intro i
  funext j
  exact_mod_cast congrFun (hu i) j

end LinearDistancePreservers.ConvexDirections
