import GreedyShortcuts.GeneralIntegerBound
import GreedyShortcuts.DAGBalance

/-! The general-directed theorem with explicit real powers and a fixed
fourth-power logarithmic factor, including the exact target range. -/
namespace GreedyShortcuts.GeneralPowerBound
open DirectedPaths KernelSamplingBalance GeneralIntegerBound

 theorem root_cube (n B : ℕ) (hB : 1≤B) (hBn : B≤n) :
    ((root n B : ℕ) : ℝ)^3 ≤ 8*Real.sqrt ((n:ℝ)^3/(B:ℝ)^3) := by
  let x : ℝ := (n:ℝ)/(B:ℝ)
  let s := Real.sqrt x
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hx : 1≤x := (le_div_iff₀ hb).mpr (by
    simpa only [one_mul] using (show (B:ℝ)≤n by exact_mod_cast hBn))
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs1 : 1≤s := Real.le_sqrt_of_sq_le (by simpa using hx)
  have hs2 : s^2=x := Real.sq_sqrt (by linarith)
  have hnat : ((Nat.sqrt (n/B):ℕ):ℝ)^2≤x := by
    have hsq : ((Nat.sqrt (n/B):ℕ):ℝ)^2≤((n/B:ℕ):ℝ) := by exact_mod_cast Nat.sqrt_le' (n/B)
    exact hsq.trans Nat.cast_div_le
  have hrt : (root n B:ℝ)≤2*s := by
    have hnon : (0:ℝ)≤Nat.sqrt (n/B) := by positivity
    have hh : (Nat.sqrt (n/B):ℝ)≤s := by nlinarith
    unfold root
    push_cast
    linarith
  have hcube : (root n B:ℝ)^3≤8*s^3 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤root n B) hrt 3
    nlinarith
  have he : s^3=Real.sqrt ((n:ℝ)^3/(B:ℝ)^3) := by
    calc
      s^3 = Real.sqrt ((s^3)^2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (x^3) := by congr 1;rw [← hs2];ring
      _ = _ := by dsimp [x];rw [div_pow]
  simpa only [he] using hcube

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem output_card_power (G : V → V → Prop) (B : ℕ) (hB : 1≤B)
    (hBn : B≤Fintype.card V) :
    ((GeneralDirected.output G B hB).card:ℝ) ≤
      4500000000000000*(logarithm (Fintype.card V):ℝ)^4*
        ((Fintype.card V:ℝ)^(3/(2:ℝ))/(B:ℝ)^(3/(2:ℝ))+
          (Fintype.card V:ℝ)^2/(B:ℝ)^3) := by
  let n := Fintype.card V
  let K : ℝ := logarithm n
  let R := Real.sqrt ((n:ℝ)^3/(B:ℝ)^3)
  let Q : ℝ := (n:ℝ)^2/(B:ℝ)^3
  have hn : 1≤n := hB.trans hBn
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hR : 1≤R := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num
    exact_mod_cast Nat.pow_le_pow_left hBn 3
  have hQ : 0≤Q := by positivity
  have hroot := root_cube n B hB hBn
  have hdiv : ((n^2/B^3:ℕ):ℝ)≤Q := by
    have hh : ((n^2/B^3:ℕ):ℝ)≤((n^2:ℕ):ℝ)/((B^3:ℕ):ℝ) := Nat.cast_div_le
    simpa only [Nat.cast_pow] using hh
  have hc : ((GeneralDirected.output G B hB).card:ℝ) ≤
      500000000000000*K^4*((root n B:ℝ)^3+((n^2/B^3:ℕ):ℝ)+1) := by
    dsimp only [K,n]
    exact_mod_cast GeneralIntegerBound.output_card G B hB hn
  have hsum : (root n B:ℝ)^3+((n^2/B^3:ℕ):ℝ)+1 ≤ 9*(R+Q) := by
    change (root n B:ℝ)^3≤8*R at hroot
    linarith
  have hh := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have he := DAGBalance.sqrt_ratio_rpow (n:ℝ) (B:ℝ) (by positivity) (by positivity)
  change ((GeneralDirected.output G B hB).card:ℝ) ≤ 4500000000000000*K^4*
    ((n:ℝ)^(3/(2:ℝ))/(B:ℝ)^(3/(2:ℝ))+Q)
  rw [← he]
  change _ ≤ 4500000000000000*K^4*(R+Q)
  nlinarith

/-- All positive targets are covered; the empty-output branch handles B>=n. -/
theorem output_card_log (G : V → V → Prop) (B : ℕ) (hB : 1≤B)
    (hn : 2≤Fintype.card V) :
    ((GeneralDirected.output G B hB).card:ℝ) ≤
      1152000000000000000*(Real.logb 2 (Fintype.card V:ℝ))^4*
        ((Fintype.card V:ℝ)^(3/(2:ℝ))/(B:ℝ)^(3/(2:ℝ))+
          (Fintype.card V:ℝ)^2/(B:ℝ)^3) := by
  by_cases hBn : B≤Fintype.card V
  · have hh := output_card_power G B hB hBn
    have hpow : (Fintype.card V)^2 ≤ (Fintype.card V)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    have hnat : logarithm (Fintype.card V) ≤ Nat.log 2 ((Fintype.card V)^3)+1 :=
      Nat.add_le_add_right (Nat.log_mono_right hpow) 1
    have hlog : (logarithm (Fintype.card V):ℝ)≤4*Real.logb 2 (Fintype.card V:ℝ) :=
      (by exact_mod_cast hnat : (logarithm (Fintype.card V):ℝ)≤(Nat.log 2 ((Fintype.card V)^3)+1:ℕ)).trans
        (DAGBalance.log_cube_bound (Fintype.card V) hn)
    have hk4 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤logarithm (Fintype.card V)) hlog 4
    calc
      _ ≤ 4500000000000000*(logarithm (Fintype.card V):ℝ)^4*
          ((Fintype.card V:ℝ)^(3/(2:ℝ))/(B:ℝ)^(3/(2:ℝ))+(Fintype.card V:ℝ)^2/(B:ℝ)^3) := hh
      _ ≤ 4500000000000000*(4*Real.logb 2 (Fintype.card V:ℝ))^4*
          ((Fintype.card V:ℝ)^(3/(2:ℝ))/(B:ℝ)^(3/(2:ℝ))+(Fintype.card V:ℝ)^2/(B:ℝ)^3) := by gcongr
      _ = _ := by ring
  · have hnB : Fintype.card V≤B := by omega
    simp only [GeneralDirected.output,ite_eq_left hnB,Finset.card_empty,Nat.cast_zero]
    positivity

end GreedyShortcuts.GeneralPowerBound
