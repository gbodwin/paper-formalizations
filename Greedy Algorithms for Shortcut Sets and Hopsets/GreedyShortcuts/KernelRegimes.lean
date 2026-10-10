import GreedyShortcuts.KernelSamplingBalance

/-! Exhaustive numerical regimes for the constructed sample-kernel target. -/
namespace GreedyShortcuts.KernelRegimes
open KernelSamplingBalance

theorem parameter_large_split (n B : ℕ)
    (hlarge : logarithm n*n < (parameter n B)^3) :
    n ≤ 1000*(logarithm n)^2 ∨ B^3 ≤ 4741632*logarithm n*n := by
  let k := logarithm n
  let N := k*n
  let X := 42*N/B
  let c := 8+2*k
  let b := parameter n B
  have hbdef : b = max c (Nat.sqrt X+1) := by simp [b,parameter,c,X,N,k,Nat.mul_assoc]
  have hk : 1≤k := by dsimp [k,logarithm];omega
  by_cases hn : n=0
  · left; simp [hn]
  have hN : 0<N := by dsimp [N];positivity
  by_cases hc : Nat.sqrt X+1 ≤ c
  · left
    have hb : b=c := hbdef.trans (max_eq_left hc)
    have hc10 : c≤10*k := by dsimp [c];omega
    have hpow : c^3≤1000*k^3 := by
      have hh := Nat.pow_le_pow_left hc10 3
      nlinarith
    change k*n < b^3 at hlarge
    rw [hb] at hlarge
    have hm : k*n ≤ k*(1000*k^2) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hm (by omega)
  · right
    have hcb : c < Nat.sqrt X+1 := by omega
    have hb : b=Nat.sqrt X+1 := hbdef.trans (max_eq_right (by omega))
    have hs : 1≤Nat.sqrt X := by dsimp [c] at hcb;omega
    have hsquare := Nat.sqrt_le' X
    have hb2 : b^2≤4*X := by rw [hb];nlinarith
    have hNle : N ≤ b^3 := by exact Nat.le_of_lt hlarge
    have hN2 : N^2≤b^6 := by simpa only [← pow_mul] using Nat.pow_le_pow_left hNle 2
    have hb6 : b^6≤64*X^3 := by
      have hh := Nat.pow_le_pow_left hb2 3
      simpa [← pow_mul,mul_pow] using hh
    have hdiv : X*B≤42*N := Nat.div_mul_le_self _ _
    have hpow := Nat.pow_le_pow_left hdiv 3
    have hm : N^2*B^3 ≤ N^2*(4741632*N) := by
      calc
        _ ≤ b^6*B^3 := Nat.mul_le_mul_right _ hN2
        _ ≤ (64*X^3)*B^3 := Nat.mul_le_mul_right _ hb6
        _ = 64*(X*B)^3 := by ring
        _ ≤ 64*(42*N)^3 := Nat.mul_le_mul_left _ hpow
        _ = _ := by ring
    have hB := Nat.le_of_mul_le_mul_left hm (by positivity : 0<N^2)
    simpa only [N,k,Nat.mul_assoc] using hB

end GreedyShortcuts.KernelRegimes
