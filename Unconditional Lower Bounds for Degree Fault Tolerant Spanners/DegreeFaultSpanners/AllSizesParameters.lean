import DegreeFaultSpanners.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.NumberTheory.Bertrand

/-!
# Integer parameters for the all-size lower bound

Bertrand's postulate and the integer `k`th root choose a prime-parameter
incidence construction occupying a constant fraction of any sufficiently
large target size.  The remaining lemmas transfer the exact construction's
power identity, or the dense construction's edge bound, to a common explicit
constant.  All rounding and all inequalities in this file are over `ℕ`.
-/

namespace DegreeFaultSpanners

/-- Reciprocal of the explicit coefficient in the all-size real lower bound. -/
def allSizesFactor (k : ℕ) : ℕ := 2 ^ (k + 3)

/-- A prime-parameter family fits into every size in the large regime and
occupies at least a `2 ^ k` fraction of that size. -/
theorem exists_prime_family_fit (k f N : ℕ) (hk : 2 ≤ k) (hf : 1 ≤ f)
    (hlarge : 2 ^ (k + 1) * f ≤ N) :
    ∃ p : ℕ, p.Prime ∧ familyVertices k p f ≤ N ∧
      N ≤ 2 ^ k * familyVertices k p f := by
  have hk0 : k ≠ 0 := by omega
  have hden : 0 < 2 * f := by omega
  let q := N / (2 * f)
  let r := Nat.nthRoot k q
  have hq : 2 ^ k ≤ q := by
    apply (Nat.le_div_iff_mul_le hden).2
    calc
      2 ^ k * (2 * f) = 2 ^ (k + 1) * f := by rw [pow_succ]; ring
      _ ≤ N := hlarge
  have hr : 2 ≤ r := (Nat.le_nthRoot_iff hk0).2 hq
  have hrpow : r ^ k ≤ q := Nat.pow_nthRoot_le (.inl hk0)
  have hrnext : q < (r + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk0 q
  obtain ⟨p, hp, hplo, hphi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (r / 2) (by omega)
  have hpr : p ≤ r := by omega
  have hrp : r + 1 ≤ 2 * p := by omega
  refine ⟨p, hp, ?_, ?_⟩
  · have hpq : p ^ k ≤ q := (Nat.pow_le_pow_left hpr k).trans hrpow
    have hfit : p ^ k * (2 * f) ≤ N := (Nat.le_div_iff_mul_le hden).1 hpq
    simpa only [familyVertices, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfit
  · have hnext : N < (r + 1) ^ k * (2 * f) :=
      (Nat.div_lt_iff_lt_mul hden).1 hrnext
    calc
      N ≤ (r + 1) ^ k * (2 * f) := hnext.le
      _ ≤ (2 * p) ^ k * (2 * f) :=
        Nat.mul_le_mul_right (2 * f) (Nat.pow_le_pow_left hrp k)
      _ = 2 ^ k * familyVertices k p f := by
        simp only [familyVertices, mul_pow]
        ring

/-- Padding a prime-parameter family by at most a factor `2 ^ k` preserves
an explicit lower bound with the common all-size constant. -/
theorem family_padding_power_lower_bound (k p f N : ℕ) (hk : 2 ≤ k)
    (hsize : N ≤ 2 ^ k * familyVertices k p f) :
    f ^ (k - 1) * N ^ (k + 1) ≤
      allSizesFactor k ^ k * familyEdges k p f ^ k := by
  dsimp only [allSizesFactor]
  have hscale := family_scaling k p f (by omega)
  have hexp : k * (k + 1) + (k + 1) ≤ (k + 3) * k := by nlinarith
  calc
    f ^ (k - 1) * N ^ (k + 1) ≤
        f ^ (k - 1) * (2 ^ k * familyVertices k p f) ^ (k + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize (k + 1))
    _ = (2 ^ k) ^ (k + 1) *
        (f ^ (k - 1) * familyVertices k p f ^ (k + 1)) := by
      rw [mul_pow]
      ring
    _ = (2 ^ k) ^ (k + 1) *
        (2 ^ (k + 1) * familyEdges k p f ^ k) := by rw [hscale]
    _ = 2 ^ (k * (k + 1) + (k + 1)) * familyEdges k p f ^ k := by
      rw [← pow_mul, ← mul_assoc, ← pow_add]
    _ ≤ 2 ^ ((k + 3) * k) * familyEdges k p f ^ k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hexp)
    _ = (2 ^ (k + 3)) ^ k * familyEdges k p f ^ k := by rw [pow_mul]

/-- In the dense regime an edge count `N * f ≤ 4 * M` gives the same
explicit power bound.  Positivity of `f` is not needed for this implication. -/
theorem dense_parameter_power_lower_bound (k f N M : ℕ) (hk : 2 ≤ k)
    (hsize : N ≤ 2 ^ (k + 1) * f) (hedges : N * f ≤ 4 * M) :
    f ^ (k - 1) * N ^ (k + 1) ≤ allSizesFactor k ^ k * M ^ k := by
  dsimp only [allSizesFactor]
  have hfk : f * f ^ (k - 1) = f ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hfour : 4 ^ k = (2 : ℕ) ^ (2 * k) := by rw [pow_mul]; norm_num
  have hexp : k + 1 + 2 * k ≤ (k + 3) * k := by nlinarith
  calc
    f ^ (k - 1) * N ^ (k + 1) = N * (f ^ (k - 1) * N ^ k) := by
      rw [pow_succ]
      ring
    _ ≤ (2 ^ (k + 1) * f) * (f ^ (k - 1) * N ^ k) :=
      Nat.mul_le_mul_right _ hsize
    _ = 2 ^ (k + 1) * (N * f) ^ k := by
      rw [mul_pow]
      calc
        (2 ^ (k + 1) * f) * (f ^ (k - 1) * N ^ k) =
            2 ^ (k + 1) * (f * f ^ (k - 1)) * N ^ k := by ring
        _ = 2 ^ (k + 1) * (N ^ k * f ^ k) := by rw [hfk]; ring
    _ ≤ 2 ^ (k + 1) * (4 * M) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hedges k)
    _ = 2 ^ (k + 1 + 2 * k) * M ^ k := by
      rw [mul_pow, hfour, ← mul_assoc, ← pow_add]
    _ ≤ 2 ^ ((k + 3) * k) * M ^ k :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hexp)
    _ = (2 ^ (k + 3)) ^ k * M ^ k := by rw [pow_mul]

end DegreeFaultSpanners
