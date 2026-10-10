import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace DirectedFlowCutGap.QueryBudgetArithmetic

def width (n : ℕ) : ℕ := Nat.log2 n+1

def epochs (n : ℕ) : ℕ := Nat.log (Nat.log2 (n+2)+2) (n^3)+2

def polynomial (n : ℕ) : ℕ :=
  (n^3+2)*n^2*((n^3+2)*(2*n*n)+3)*(n^2+n+2)

theorem width_le (n : ℕ) : width n≤n+1 := by
  have h := Nat.log_le_self 2 n
  simpa only [width,Nat.log2_eq_log_two] using Nat.add_le_add_right h 1

theorem epochs_le (n : ℕ) : epochs n≤n^3+2 :=
  Nat.add_le_add_right (Nat.log_le_self _ _) 2

theorem budget_le {n L : ℕ} (hL : L≤n) :
    epochs n*(n*n)*(width (epochs n*(2*n*n))+2)*(width (n*n)+width L)≤polynomial n := by
  have hw := width_le (epochs n*(2*n*n))
  have hm := width_le (n*n)
  have hcut := width_le L
  have he := epochs_le n
  have ht : width (epochs n*(2*n*n))+2≤(n^3+2)*(2*n*n)+3 := by
    have hx := Nat.mul_le_mul_right (2*n*n) he
    omega
  have hs : width (n*n)+width L≤n^2+n+2 := by nlinarith
  unfold polynomial
  calc
    _ ≤ (n^3+2)*(n*n)*((n^3+2)*(2*n*n)+3)*(n^2+n+2) := by gcongr
    _ = _ := by ring

theorem polynomial_mono {n m : ℕ} (h : n≤m) : polynomial n≤polynomial m := by
  unfold polynomial
  gcongr

theorem width_of_lt {v k : ℕ} (hv : v<2^k) : width v≤k+1 := by
  have h := Nat.log_lt_of_lt_pow' (show k+1≠0 by omega)
    (hv.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ _)))
  simpa only [width,Nat.log2_eq_log_two] using (Nat.succ_le_of_lt h)

theorem oracle_bound (n B : ℕ) : width (3*n^2+1)+(2*B+Nat.size n+1)≤3*n^2+2*B+n+3 := by
  have hs : Nat.size n≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  have hw := width_le (3*n^2+1)
  omega

end DirectedFlowCutGap.QueryBudgetArithmetic
