import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic

/-! Integer parameter selection for the weighted subset-preserver lower
bound. All estimates are uniform, including the floor and padding losses. -/
namespace LinearDistancePreservers.LowerBoundParameters

/-- A cube-root scale within a factor two of the real cube root. -/
theorem cube_scale_mul {N T C : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ C^3*N^2) :
    ∃ q : ℕ, 0 < q ∧ q^3 ≤ N ∧ N ≤ 8*q^3 ∧ T ≤ 4*C*q^2 := by
  let q := Nat.nthRoot 3 N
  have hlo : q^3 ≤ N := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : N < (q+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hq : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    rw [hz] at hhi
    norm_num at hhi
    omega
  have hN : N ≤ 8*q^3 := by
    have hh := Nat.pow_le_pow_left (show q+1 ≤ 2*q by omega) 3
    nlinarith only [hhi,hh]
  have hTc : T^3 ≤ (4*C*q^2)^3 := by
    calc
      _ ≤ C^3*N^2 := hrange
      _ ≤ C^3*(8*q^3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
      _ = _ := by ring
  have ht : T ≤ 4*C*q^2 := by
    by_contra h
    have hh := Nat.pow_lt_pow_left (show 4*C*q^2 < T by omega) (by decide : 3 ≠ 0)
    omega
  exact ⟨q,hq,hlo,hN,ht⟩

theorem cube_scale {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ N^2) :
    ∃ q : ℕ, 0 < q ∧ q^3 ≤ N ∧ N ≤ 8*q^3 ∧ T ≤ 4*q^2 := by
  simpa using cube_scale_mul (C := 1) hT hTN (by simpa using hrange)

/-- Above the linear regime, floored parameters fit inside q³ vertices
and retain a constant fraction of T q² edges. -/
theorem product_parameters {q T : ℕ} (hq : 0 < q)
    (hlarge : 192*q ≤ T) (hsmall : T ≤ 4*q^2) :
    ∃ σ k x : ℕ, 0 < σ ∧ 0 < x ∧ x ≤ q ∧ (k+1)*x ≤ q ∧
      3*(q*x) ≤ σ ∧ 2*σ ≤ T ∧ 2*σ+σ*(k+1)*q ≤ q^3 ∧
      T*q^2 ≤ 2048*(σ*q*x*(k+2)) := by
  let σ := T/32
  let x := σ/(3*q)
  let k := q^2/(4*σ)
  have hσlow : 6*q ≤ σ := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have hσ : 0 < σ := by omega
  have hσT : 32*σ ≤ T := by simpa [σ,Nat.mul_comm] using Nat.div_mul_le_self T 32
  have hTσ : T ≤ 64*σ := by
    have hh := Nat.lt_mul_div_succ T (by decide : 0 < 32)
    change T < 32*(σ+1) at hh
    omega
  have hσq : 8*σ ≤ q^2 := by omega
  have hx : 0 < x := by
    have : 1 ≤ x := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega
  have hxs : 3*q*x ≤ σ := by simpa [x,Nat.mul_comm] using Nat.div_mul_le_self σ (3*q)
  have hsx : σ ≤ 6*q*x := by
    have hh := Nat.lt_mul_div_succ σ (by omega : 0 < 3*q)
    change σ < 3*q*(x+1) at hh
    nlinarith only [hh,Nat.mul_le_mul_left (3*q) hx]
  have hkq : 4*σ*k ≤ q^2 := by simpa [k,Nat.mul_comm] using Nat.div_mul_le_self (q^2) (4*σ)
  have hqk : q^2 ≤ 4*σ*(k+2) := by
    have hh := Nat.lt_mul_div_succ (q^2) (by omega : 0 < 4*σ)
    change q^2 < 4*σ*(k+1) at hh
    nlinarith only [hh]
  have hinner : (k+1)*x ≤ q := by
    have hh := Nat.mul_le_mul_left (k+1) hxs
    by_contra hn
    have hnx : q+1 ≤ (k+1)*x := by omega
    have hh' := Nat.mul_le_mul_left (12*q) hnx
    nlinarith only [hh,hh',hkq,hσq,hq]
  have hxn : x ≤ q := by nlinarith only [hinner,Nat.zero_le (k*x)]
  have hV : 2*σ+σ*(k+1)*q ≤ q^3 := by
    have h1 := Nat.mul_le_mul_right q hkq
    have h2 := Nat.mul_le_mul_right q hσq
    have h3 : 2*σ ≤ 2*σ*q := Nat.le_mul_of_pos_right _ hq
    nlinarith only [h1,h2,h3]
  have hE : σ*q^2 ≤ 24*(σ*q*x*(k+2)) := by
    have h1 := Nat.mul_le_mul_left σ hqk
    have h2 := Nat.mul_le_mul_right (4*σ*(k+2)) hsx
    nlinarith only [h1,h2]
  have hTE : T*q^2 ≤ 2048*(σ*q*x*(k+2)) := by
    have hh := Nat.mul_le_mul_right (q^2) hTσ
    nlinarith only [hh,hE]
  exact ⟨σ,k,x,hσ,hx,hxn,hinner,by nlinarith only [hxs],by omega,hV,hTE⟩

/-- Cubed form of the lower bound after rounding the vertex scale. -/
theorem product_rate {N T q E : ℕ} (hN : N ≤ 8*q^3) (hE : T*q^2 ≤ 2048*E) :
    T^3*N^2 ≤ 8192^3*E^3 := by
  calc
    _ ≤ T^3*(8*q^3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
    _ = 64*(T*q^2)^3 := by ring
    _ ≤ 64*(2048*E)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 3)
    _ = _ := by ring

/-- A path suffices when T is at most a constant times the cube root of N. -/
theorem path_rate {N T q : ℕ} (hN : 2 ≤ N) (hq : q^3 ≤ N) (hT : T ≤ 192*q) :
    T^3*N^2 ≤ 8192^3*(N-1)^3 := by
  have h1 : T^3 ≤ 192^3*N := by
    calc
      _ ≤ (192*q)^3 := Nat.pow_le_pow_left hT 3
      _ = 192^3*q^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hq
  calc
    _ ≤ (192^3*N)*N^2 := Nat.mul_le_mul_right _ h1
    _ = 192^3*N^3 := by ring
    _ ≤ 192^3*(2*(N-1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    _ = 384^3*(N-1)^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

end LinearDistancePreservers.LowerBoundParameters
