import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One compatible numerical profile for the actual phase. The scale multiplier
is an integer, so every size budget is a literal natural number. The old baseline
and cap scale together; the conclusion includes a next-level cap. This lemma
still requires the stated weighted-girth gap and density credit. -/
namespace MinorFreeSpanners

 theorem canonical_phase_numerics (t : ℕ) (u c sigma g : ℝ)
    (ht : 4096≤t) (hu : 1≤u) (hc : 30000*(t:ℝ)^3≤c)
    (hcreditDensity : 8*sigma*(t:ℝ)≤c)
    (hgap : 4000*u≤(g-2)*((t:ℝ)*u)) :
    let D := 200*u
    let M := 2*(t:ℝ)*u
    let L := M
    let b := u
    let R := 10*c*M
    let q := 100*t
    let s := 4*t
    let N := 20*t
    let Nsmall := 4*t
    let Nheavy := 12*t
    let a := (q:ℝ)*M
    0≤c ∧ 0≤D ∧ 0≤M ∧ 0≤b ∧ 1<M/2 ∧
    2*R≤(q+1:ℕ)*(c*b) ∧ 4*sigma*M≤c*b ∧
    3*(D+1)<L ∧ L+D≤s*b ∧ (s+1:ℕ)*a≤c*b/2 ∧
    8*a≤c*b ∧ 15*D+4*M+15+2*b≤6*L ∧
    a*N+c*b/2≤c*((g-2)*(M/2)-6*D-4) ∧
    2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b) ∧ 2*a≤c*b ∧
    2*L≤Nsmall*b ∧ Nsmall*a+5*(Nheavy:ℝ)*a≤c*b/2 ∧
    c*(4*(D+M)+D)+Nsmall*a+(2*c*M+7*(Nheavy:ℝ)*a)≤R ∧
    0≤M/2 ∧ M/2≤L-1 ∧ M/2≤4*(D+M)+D ∧
    2*(2*L+(D+1))≤Nheavy*b ∧ 2*(Nheavy:ℝ)*a≤c*L/4 ∧
    (Nheavy+1:ℕ)*a≤c*b/2 ∧
    max ((max (4*(D+M)+D) (2*(L+2*D+1)+M)+2*L)+4*(2*L+(D+1))+2*M)
      (2*L+(D+1)-1)≤100*M := by
  have htR : (4096:ℝ)≤t := by exact_mod_cast ht
  have ht0 : (0:ℝ)≤t := Nat.cast_nonneg _
  have hu0 : 0≤u := by linarith
  have hc0 : 0≤c := le_trans (by positivity) hc
  have hcu : 30000*(t:ℝ)^3*u≤c*u := mul_le_mul_of_nonneg_right hc hu0
  have htu : 4096*u≤(t:ℝ)*u := mul_le_mul_of_nonneg_right htR hu0
  have hcu0 : 0≤c*u := mul_nonneg hc0 hu0
  have hctu : 4096*(c*u)≤(t:ℝ)*(c*u) := mul_le_mul_of_nonneg_right htR hcu0
  have ht2u : 0≤(t:ℝ)^2*u := by positivity
  have ht3u : 0≤(t:ℝ)^3*u := by positivity
  have ht2le : (t:ℝ)^2*u≤(t:ℝ)^3*u := by
    have h := mul_le_mul_of_nonneg_right (show (1:ℝ)≤t by linarith) ht2u
    nlinarith only [h]
  have hdensity := mul_le_mul_of_nonneg_right hcreditDensity hu0
  have hgapc := mul_le_mul_of_nonneg_left hgap hc0
  have hcuFloor := mul_le_mul_of_nonneg_left hu hc0
  dsimp
  push_cast
  refine ⟨hc0,by positivity,by positivity,hu0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [htu,hu]
  · nlinarith only [hctu,hcu0]
  · nlinarith only [hdensity]
  · nlinarith only [htu,hu]
  · nlinarith only [htu,hu0]
  · nlinarith only [hcu,ht2le,ht3u]
  · nlinarith only [hcu,ht2le,ht3u]
  · nlinarith only [htu,hu]
  · nlinarith only [hgapc,hcu,hcuFloor,hcu0,ht3u]
  · nlinarith only [hctu,hcuFloor,hcu0]
  · nlinarith only [hcu,ht2le,ht3u]
  · ring_nf
    exact le_rfl
  · nlinarith only [hcu,ht3u]
  · nlinarith only [hcu,hctu,hcu0,ht3u]
  · positivity
  · nlinarith only [htu,hu]
  · nlinarith only [htu,hu0]
  · nlinarith only [htu,hu]
  · nlinarith only [hcu,hctu,hcu0,ht3u]
  · nlinarith only [hcu,ht2le,ht3u]
  · rw [max_le_iff]
    constructor
    · simp only [max_def]
      split_ifs <;> nlinarith only [htu,hu]
    · nlinarith only [htu,hu]

end MinorFreeSpanners
