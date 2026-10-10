import GreedyShortcuts.KernelBalance

/-! Unconditional large-budget general-directed application. When the inner
hop target b obeys b^3 <= n, the SCC preprocessing cost is absorbed by the
n^2/b^3 term, with every finite division explicit. -/
namespace GreedyShortcuts.SCCBudget

open DirectedPaths DAGProgress

 theorem scaled_div {a d C : ℕ} (hd : 0 < d) : C*a/d ≤ C*(a/d+1) := by
  have hrem := Nat.mod_lt a hd
  have he := Nat.mod_add_div a d
  have ha : a ≤ (a/d+1)*d := by nlinarith
  have hm := Nat.mul_le_mul_left C ha
  have hnum : C*a ≤ (C*(a/d+1))*d := by nlinarith
  have hh := Nat.div_le_div_right (c:=d) hnum
  simpa [Nat.mul_div_cancel _ hd] using hh

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem output_card (G : V → V → Prop) (b : ℕ) (hb : 1 ≤ b)
    (hregime : b^3 ≤ Fintype.card V) :
    (SCCGreedy.output G b hb).card ≤
      (Nat.log 2 ((Fintype.card V)^3)+1)*132000*((Fintype.card V)^2/b^3+1) := by
  let n := Fintype.card V
  let q := Fintype.card (SCCQuotient.Component G)
  let d := n^2/b^3
  let k := Nat.log 2 (n^3)+1
  have hn : 0 < n := lt_of_lt_of_le (by positivity : 0 < b^3) hregime
  have hq : q ≤ n := SCCQuotient.component_card G
  have hnD : n ≤ d := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    nlinarith [Nat.mul_le_mul_left n hregime]
  have hk : 1 ≤ k := by dsimp [k];omega
  change (SCCGreedy.output G b hb).card ≤ k*132000*(d+1)
  by_cases hb8 : 8 ≤ b
  · have hd := DAGProgress.output_card_bound (SCCQuotient.acyclic G) b 8 hb8 (by omega)
    have hlog : Nat.log 2 (q^3)+1 ≤ k := Nat.add_le_add_right
      (Nat.log_mono_right (Nat.pow_le_pow_left hq 3)) 1
    have hblock : blockLength q b 8 ≤ 131072*(d+1)+1 := by
      unfold blockLength
      apply max_le
      · have hh := Nat.div_le_self (512*q) 8
        omega
      · have hnum : 16384*8*q^2 ≤ 131072*n^2 := by nlinarith [Nat.pow_le_pow_left hq 2]
        have hd' := (Nat.div_le_div_right (c:=b^3) hnum).trans
          (scaled_div (C:=131072) (a:=n^2) (by positivity : 0 < b^3))
        change 16384*8*q^2/b^3 ≤ 131072*(d+1) at hd'
        omega
    have hgreedy := hd.trans (Nat.mul_le_mul hlog hblock)
    have hcard := SCCGreedy.output_card_le G b hb
    change (SCCGreedy.output G b hb).card ≤ 2*n+_ at hcard
    have hkn := Nat.mul_le_mul_right (2*n) hk
    nlinarith
  · have hb7 : b ≤ 7 := by omega
    have hb3 : b^3 ≤ 343 := by nlinarith [Nat.pow_le_pow_left hb7 3]
    have hrem := Nat.mod_lt (n^2) (by positivity : 0 < b^3)
    have he := Nat.mod_add_div (n^2) (b^3)
    have hstep : n^2 ≤ b^3*(d+1) := by dsimp [d];nlinarith
    have hbase : n^2 ≤ 343*(d+1) := hstep.trans (Nat.mul_le_mul_right _ hb3)
    have hcard : (SCCGreedy.output G b hb).card ≤ n^2 := by
      calc
        _ ≤ (candidates G).card := Finset.card_le_card (SCCGreedy.output_legal G b hb)
        _ ≤ Fintype.card (V × V) := Finset.card_le_univ _
        _ = n^2 := by simp [n,pow_two]
    have hmul := Nat.mul_le_mul_right (132000*(d+1)) hk
    nlinarith

/-- Exact requested-target version; its hop correctness is SCCGreedy's actual
integer retargeting, not an assumed quality predicate. -/
theorem target_card (G : V → V → Prop) (B : ℕ) (hB : 5 ≤ B)
    (hregime : ((B-2)/3)^3 ≤ Fintype.card V) :
    (SCCGreedy.output G ((B-2)/3) (by omega)).card ≤
      (Nat.log 2 ((Fintype.card V)^3)+1)*132000*
        ((Fintype.card V)^2/((B-2)/3)^3+1) := output_card G _ (by omega) hregime

/-- Division-free cubic form of the actual inner-target bound. -/
theorem output_card_scaled (G : V → V → Prop) (b : ℕ) (hb : 1 ≤ b)
    (hregime : b^3 ≤ Fintype.card V) :
    (SCCGreedy.output G b hb).card*b^3 ≤
      264000*(Nat.log 2 ((Fintype.card V)^3)+1)*(Fintype.card V)^2 := by
  let n := Fintype.card V
  let d := n^2/b^3
  let k := Nat.log 2 (n^3)+1
  have hn : 0 < n := lt_of_lt_of_le (by positivity : 0 < b^3) hregime
  have hnd : n ≤ d := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    nlinarith [Nat.mul_le_mul_left n hregime]
  have hd : 1 ≤ d := by omega
  have hh := output_card G b hb hregime
  change (SCCGreedy.output G b hb).card ≤ k*132000*(d+1) at hh
  have hsmall : (SCCGreedy.output G b hb).card ≤ k*264000*d := by
    calc
      _ ≤ k*132000*(d+1) := hh
      _ ≤ k*132000*(2*d) := Nat.mul_le_mul_left _ (by omega)
      _ = k*264000*d := by ring
  have hdiv : d*b^3 ≤ n^2 := Nat.div_mul_le_self _ _
  change (SCCGreedy.output G b hb).card*b^3 ≤ 264000*k*n^2
  calc
    _ ≤ (k*264000*d)*b^3 := Nat.mul_le_mul_right _ hsmall
    _ = (264000*k)*(d*b^3) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hdiv

/-- Source-shaped n²/B³ size bound, with actual requested-target output and
an explicit absolute constant. Together with target_hop_bound this is the
unconditional general-directed low-target regime. -/
theorem target_card_scaled (G : V → V → Prop) (B : ℕ) (hB : 5 ≤ B)
    (hregime : ((B-2)/3)^3 ≤ Fintype.card V) :
    (SCCGreedy.output G ((B-2)/3) (by omega)).card*B^3 ≤
      90552000*(Nat.log 2 ((Fintype.card V)^3)+1)*(Fintype.card V)^2 := by
  let b := (B-2)/3
  have hb : 1 ≤ b := by dsimp [b];omega
  have hBb : B ≤ 7*b := by dsimp [b];omega
  have hpow : B^3 ≤ 343*b^3 := by nlinarith [Nat.pow_le_pow_left hBb 3]
  have hh := output_card_scaled G b hb hregime
  calc
    _ ≤ (SCCGreedy.output G b hb).card*(343*b^3) := Nat.mul_le_mul_left _ hpow
    _ = 343*((SCCGreedy.output G b hb).card*b^3) := by ring
    _ ≤ 343*(264000*(Nat.log 2 ((Fintype.card V)^3)+1)*(Fintype.card V)^2) := Nat.mul_le_mul_left _ hh
    _ = _ := by ring

/-- Targets below five need no SCC reduction: the actual original greedy
output's elementary bound already has the required cubic size scale. -/
theorem small_target_card_scaled (G : V → V → Prop) (B : ℕ)
    (hB : 1 ≤ B) (hsmall : B < 5) :
    (GraphGreedy.output G B hB).card*B^3 ≤ 64*(Fintype.card V)^2 := by
  have hpow : B^3 ≤ 64 := by nlinarith [Nat.pow_le_pow_left (by omega : B ≤ 4) 3]
  have hh := Nat.mul_le_mul (GraphGreedy.output_card_le G B hB) hpow
  simpa [Nat.mul_comm] using hh

end GreedyShortcuts.SCCBudget
