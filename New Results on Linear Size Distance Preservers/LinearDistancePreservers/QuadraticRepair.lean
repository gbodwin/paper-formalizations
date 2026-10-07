import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# A replacement weighting for the modular construction

A walk is encoded by its step directions and slopes. A forward step raises
the layer by one and adds its slope modulo n; a backward step reverses both.
The endpoint equations below are exactly the telescoping layer and column
equations. We allow intermediate layers outside the finite graph, so the
result also holds for every walk that stays within its layers.

For k+1 layers and x slopes, the integer weight C+a^2, with C=k*x^2+1,
makes every constant-slope forward walk uniquely shortest. This is a
replacement for, not a validation of, the paper's Euclidean weighting.
-/
namespace LinearDistancePreservers.QuadraticRepair
open Finset

def height {m : ℕ} (forward : Fin m → Bool) : ℤ :=
  ∑ i, if forward i then 1 else -1

def displacement {m : ℕ} (forward : Fin m → Bool) (slope : Fin m → ℕ) : ℤ :=
  ∑ i, if forward i then (slope i : ℤ) else -(slope i : ℤ)

def baseline (k x : ℕ) : ℤ := (k : ℤ) * (x : ℤ)^2 + 1

def cost {m : ℕ} (k x : ℕ) (slope : Fin m → ℕ) : ℤ :=
  ∑ i, (baseline k x + (slope i : ℤ)^2)

theorem height_le_length {m : ℕ} (forward : Fin m → Bool) :
    height forward ≤ (m : ℤ) := by
  calc
    height forward ≤ ∑ _i : Fin m, (1 : ℤ) :=
      sum_le_sum fun i _ => by split <;> norm_num
    _ = m := by simp

theorem forward_of_height_eq_length {m : ℕ} (forward : Fin m → Bool)
    (h : height forward = (m : ℤ)) : ∀ i, forward i = true := by
  intro i
  by_contra hfalse
  have hfalse' : forward i = false := by cases hfi : forward i <;> simp_all
  have hlt : height forward < ∑ _i : Fin m, (1:ℤ) := by
    apply sum_lt_sum
    · intro j _
      split <;> norm_num
    · exact ⟨i, mem_univ _, by simp [hfalse']⟩
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
  omega

theorem cost_formula {m : ℕ} (k x : ℕ) (slope : Fin m → ℕ) :
    cost k x slope = (m : ℤ) * baseline k x + ∑ i, (slope i : ℤ)^2 := by
  simp [cost,sum_add_distrib]

/-- The squared-deviation identity gives both optimality and uniqueness. -/
theorem variance_identity {k a : ℕ} (slope : Fin k → ℕ)
    (h : ∑ i, (slope i : ℤ) = (k : ℤ) * a) :
    (∑ i, (slope i : ℤ)^2) - (k : ℤ) * (a : ℤ)^2 =
      ∑ i, ((slope i : ℤ) - a)^2 := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h]
  ring

/-- Universal lower bound and equality case for walks with the designated
endpoints. No shortest-path or convexity hypothesis is assumed. -/
theorem constant_slope_unique_shortest {n k x a m : ℕ}
    (ha : a < x) (hn : (k+1)*x ≤ n)
    (forward : Fin m → Bool) (slope : Fin m → ℕ)
    (hslope : ∀ i, slope i < x)
    (hheight : height forward = (k : ℤ))
    (hcolumn : displacement forward slope % (n : ℤ) = ((k : ℤ)*a) % (n : ℤ)) :
    (k : ℤ) * (baseline k x + (a : ℤ)^2) ≤ cost k x slope ∧
    (cost k x slope = (k : ℤ) * (baseline k x + (a : ℤ)^2) →
      m = k ∧ (∀ i, forward i = true) ∧ (∀ i, slope i = a)) := by
  have hm : k ≤ m := by
    have := height_le_length forward
    rw [hheight] at this
    exact_mod_cast this
  have hx : (0:ℤ) < x := by exact_mod_cast (by omega : 0 < x)
  have hn' : ((k:ℤ)+1)*x ≤ n := by exact_mod_cast hn
  have ha' : (a:ℤ) < x := by exact_mod_cast ha
  have hc : 0 < baseline k x := by unfold baseline; positivity
  have hsquares : 0 ≤ ∑ i, (slope i : ℤ)^2 := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hmk : m = k
  · subst m
    have hf := forward_of_height_eq_length forward hheight
    have hd : displacement forward slope = ∑ i, (slope i : ℤ) := by
      simp [displacement,hf]
    have hsum0 : 0 ≤ ∑ i, (slope i : ℤ) := sum_nonneg fun _ _ => by positivity
    have hsumle : ∑ i, (slope i : ℤ) ≤ (k:ℤ)*x := by
      calc
        _ ≤ ∑ _i : Fin k, (x:ℤ) := sum_le_sum fun i _ => by exact_mod_cast (hslope i).le
        _ = _ := by simp
    have hsumlt : ∑ i, (slope i : ℤ) < n := by nlinarith
    have halt : (k:ℤ)*a < n := by
      have := mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg k)
      nlinarith
    rw [hd,Int.emod_eq_of_lt hsum0 hsumlt,
      Int.emod_eq_of_lt (by positivity) halt] at hcolumn
    have hv := variance_identity slope hcolumn
    have hvar : 0 ≤ ∑ i, ((slope i : ℤ) - a)^2 := sum_nonneg fun _ _ => sq_nonneg _
    constructor
    · rw [cost_formula]
      nlinarith
    · intro heq
      refine ⟨rfl,hf,?_⟩
      rw [cost_formula] at heq
      have hz : ∑ i, ((slope i : ℤ)-a)^2 = 0 := by nlinarith
      have heach := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin k))) =>
        sq_nonneg ((slope i : ℤ)-a))).mp hz
      intro i
      have hi := heach i (mem_univ _)
      have : (slope i : ℤ) = a := by nlinarith [sq_nonneg ((slope i:ℤ)-a)]
      exact_mod_cast this
  · have hmk' : (k:ℤ)+1 ≤ m := by exact_mod_cast (by omega : k+1 ≤ m)
    have hsq : (a:ℤ)^2 ≤ (x:ℤ)^2 := by nlinarith [Int.natCast_nonneg a]
    have hmul := mul_le_mul_of_nonneg_left hsq (Int.natCast_nonneg k)
    have hbase : (k:ℤ)*(a:ℤ)^2 < baseline k x := by unfold baseline; omega
    have hcost : (k:ℤ)*(baseline k x+(a:ℤ)^2) < cost k x slope := by
      rw [cost_formula]
      have := mul_le_mul_of_nonneg_right hmk' hc.le
      nlinarith
    exact ⟨hcost.le,fun heq => False.elim ((ne_of_gt hcost) heq)⟩

end LinearDistancePreservers.QuadraticRepair
