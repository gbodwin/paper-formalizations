import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Explicit logarithmic budget for the deterministic clique-minor construction. -/
namespace MinorFreeSpanners

def cliqueDensityScale (h : ℕ) : ℕ := 4096*h*(Nat.log 2 h+2)

theorem cliqueDensityScale_pos {h : ℕ} (hh : 0 < h) : 0 < cliqueDensityScale h := by
  unfold cliqueDensityScale
  positivity

theorem cliqueDensityScale_cover_budget (h n : ℕ)
    (hn : n ≤ 12*cliqueDensityScale h) :
    h*(48*(Nat.log 2 n+1)) ≤ cliqueDensityScale h := by
  let q := Nat.log 2 h+1
  have hh : h < 2^q := Nat.lt_pow_succ_log_self (by omega) h
  have hq : q+1 ≤ 2^q := Nat.lt_two_pow_self
  have hpow : n < 2^(2*q+16) := by
    calc
      n ≤ 12*cliqueDensityScale h := hn
      _ = 49152*h*(q+1) := by dsimp [cliqueDensityScale,q]; ring
      _ ≤ 49152*(2^q*2^q) := by nlinarith [Nat.mul_le_mul hh.le hq]
      _ < 65536*(2^q*2^q) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2^(2*q+16) := by rw [show 2*q+16 = q+q+16 by omega,pow_add,pow_add]; norm_num; ring
  have hl : Nat.log 2 n < 2*q+16 :=
    Nat.log_lt_of_lt_pow' (by omega) hpow
  have hc : 48*(Nat.log 2 n+1) ≤ 4096*(q+1) := by omega
  have hm := Nat.mul_le_mul_left h hc
  simpa [cliqueDensityScale,q,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm

end MinorFreeSpanners
