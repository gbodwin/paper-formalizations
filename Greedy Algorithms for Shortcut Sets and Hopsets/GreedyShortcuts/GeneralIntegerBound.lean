import GreedyShortcuts.GeneralDirected

/-! A uniform, source-shaped integer square-root bound with only a fixed
fourth power of a graph-size logarithm. -/
namespace GreedyShortcuts.GeneralIntegerBound
open KernelSamplingBalance

def root (n B : ℕ) : ℕ := Nat.sqrt (n/B)+1

theorem root_pos (n B : ℕ) : 1≤root n B := by unfold root;omega

theorem parameter_le (n B : ℕ) (hB : 0<B) :
    parameter n B ≤ 10*logarithm n*root n B := by
  let k := logarithm n
  let q := root n B
  let X := 42*k*n/B
  have hk : 1≤k := by dsimp [k,logarithm];omega
  have hq : 1≤q := root_pos n B
  have hs : n/B+1 ≤ q^2 := Nat.succ_le_succ_sqrt' _
  have hx : X ≤ 42*k*q^2 :=
    (SCCBudget.scaled_div (C:=42*k) (a:=n) hB).trans (Nat.mul_le_mul_left _ hs)
  have hk2 : k≤k^2 := by nlinarith
  have hmul := Nat.mul_le_mul_right (q^2) hk2
  have hX : X ≤ (7*k*q)^2 := by nlinarith
  have hroot : Nat.sqrt X ≤ 7*k*q := by
    have hh := Nat.sqrt_le_sqrt hX
    simpa only [Nat.sqrt_eq'] using hh
  have hroot' : Nat.sqrt X+1 ≤ 8*k*q := by nlinarith
  change max (8+2*k) (Nat.sqrt X+1) ≤ 10*k*q
  exact max_le (by nlinarith) (hroot'.trans (by nlinarith))

theorem parameter_log (n B : ℕ) (hn : 1≤n) (hB : 0<B) :
    Nat.log 2 ((parameter n B)^9)+1 ≤ 81*logarithm n := by
  let k := logarithm n
  let b := parameter n B
  have hk : 1≤k := by dsimp [k,logarithm];omega
  have hkle : k≤2*n^2 := by
    have hh := Nat.log_le_self 2 (n^2)
    dsimp [k,logarithm]
    nlinarith
  have hq : root n B≤2*n := by
    have hh := (Nat.sqrt_le_self (n/B)).trans (Nat.div_le_self n B)
    unfold root
    omega
  have hb : b≤40*n^3 := by
    have hh := parameter_le n B hB
    have hm := Nat.mul_le_mul hkle hq
    change k*root n B ≤ (2*n^2)*(2*n) at hm
    change b ≤ 10*k*root n B at hh
    nlinarith
  have hn2 : n≤n^2 := by nlinarith
  have hnpow : n < 2^k := hn2.trans_lt (Nat.lt_pow_succ_log_self (by decide) (n^2))
  have hbcube : b < 2^(6+3*k) := by
    have hp := Nat.pow_lt_pow_left hnpow (by decide : 3≠0)
    have hpos : 0<(2^k)^3 := by positivity
    have hh : 40*n^3 < 64*(2^k)^3 := by nlinarith
    have he : (2:ℕ)^(6+3*k) = 64*(2^k)^3 := by
      simp [pow_add,← pow_mul,Nat.mul_comm]
    rw [he]
    exact hb.trans_lt hh
  have hbpow : b < 2^(9*k) := hbcube.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb9 : b^9 < 2^(81*k) := by
    have hh := Nat.pow_lt_pow_left hbpow (by decide : 9≠0)
    simpa only [← pow_mul,show 9*k*9=81*k by omega] using hh
  have hl := Nat.log_lt_of_lt_pow' (by positivity : 81*k≠0) hb9
  change Nat.log 2 (b^9)+1 ≤ 81*k
  omega

theorem cube_log (n : ℕ) (hn : 1≤n) :
    Nat.log 2 (n^3)+1 ≤ 2*logarithm n := by
  let k := logarithm n
  have hp : n^2 < 2^k := Nat.lt_pow_succ_log_self (by decide) _
  have h3 : n^3 ≤ n^4 := Nat.pow_le_pow_right hn (by decide)
  have h4 : n^4 < 2^(2*k) := by
    have hh := Nat.pow_lt_pow_left hp (by decide : 2≠0)
    simpa [← pow_mul,Nat.mul_comm] using hh
  have hh := Nat.log_lt_of_lt_pow' (by dsimp [k,logarithm];omega : 2*k≠0) (h3.trans_lt h4)
  change Nat.log 2 (n^3)+1 ≤ 2*k
  omega

theorem kernel_term (n B : ℕ) (hn : 1≤n) (hB : 0<B) :
    GeneralDirected.kernelTerm n B ≤ 22000000000*(logarithm n)^4*(root n B)^3 := by
  let k := logarithm n
  let q := root n B
  have hk : 1≤k := by dsimp [k,logarithm];omega
  have hq : 1≤q := root_pos n B
  have hb := parameter_le n B hB
  have hc : 8+2*k ≤ 10*k*q := by nlinarith
  have hr : Nat.sqrt (42*k*n/B)+1 ≤ 10*k*q :=
    (Nat.le_max_right _ _).trans hb
  have hc3 : (8+2*k)^3 ≤ 1000*k^3*q^3 := by simpa [mul_pow] using Nat.pow_le_pow_left hc 3
  have hr3 : (Nat.sqrt (42*k*n/B)+1)^3 ≤ 1000*k^3*q^3 := by simpa [mul_pow] using Nat.pow_le_pow_left hr 3
  have hprod : 1≤k^3*q^3 := by
    have hp : 0<k^3*q^3 := by positivity
    omega
  have hsize : 131074*((8+2*k)^3+(Nat.sqrt (42*k*n/B)+1)^3)+1 ≤ 263000000*k^3*q^3 := by
    nlinarith
  have hl := parameter_log n B hn hB
  have hh := Nat.mul_le_mul hl hsize
  change GeneralDirected.kernelTerm n B ≤ _
  unfold GeneralDirected.kernelTerm
  change _ ≤ 22000000000*k^4*q^3
  calc
    _ ≤ (81*k)*(263000000*k^3*q^3) := hh
    _ = 21303000000*k^4*q^3 := by ring
    _ ≤ _ := by nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unconditional integer square-root version of the source tradeoff,
with explicit fourth-power logarithmic loss. -/
theorem output_card (G : V → V → Prop) (B : ℕ) (hB : 1≤B)
    (hn : 1≤Fintype.card V) :
    (GeneralDirected.output G B hB).card ≤ 500000000000000*(logarithm (Fintype.card V))^4*
      ((root (Fintype.card V) B)^3+(Fintype.card V)^2/B^3+1) := by
  let n := Fintype.card V
  let k := logarithm n
  let q := root n B
  let d := n^2/B^3
  have hk : 1≤k := by dsimp [k,logarithm];omega
  have hkernel := kernel_term n B hn (by omega)
  have hlog := cube_log n hn
  have hcubic : 216000000000000*k*(Nat.log 2 (n^3)+1)*(d+1) ≤
      432000000000000*k^4*(d+1) := by
    have hm := Nat.mul_le_mul_left (216000000000000*k) hlog
    have hpow : k^2≤k^4 := Nat.pow_le_pow_right hk (by decide)
    have hh : 216000000000000*k*(Nat.log 2 (n^3)+1) ≤ 432000000000000*k^4 := by nlinarith
    exact Nat.mul_le_mul_right _ hh
  have hcard := GeneralDirected.output_card G B hB
  change (GeneralDirected.output G B hB).card ≤
    GeneralDirected.kernelTerm n B+1000000*k^4+
      216000000000000*k*(Nat.log 2 (n^3)+1)*(d+1) at hcard
  change (GeneralDirected.output G B hB).card ≤ 500000000000000*k^4*(q^3+d+1)
  change GeneralDirected.kernelTerm n B ≤ 22000000000*k^4*q^3 at hkernel
  nlinarith

end GreedyShortcuts.GeneralIntegerBound
