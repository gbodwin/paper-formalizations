import MinorFreeSpanners.CanonicalPhaseNumerics
import Mathlib.Tactic.FieldSimp

/-! Explicit weighted-girth and credit choices for the numerical phase profile.
The credit coefficient is cubic in the scale multiplier and linear in the
cluster-density bound (with a unit floor for degenerate instances). -/
namespace MinorFreeSpanners

 theorem canonical_phase_girth (t r : ℕ) (u : ℝ)
    (ht : 4096≤t) (hr : 1≤r) (hu : 1≤u) :
    let g := 2*(r:ℝ)*(1+2000/(t:ℝ))
    2≤g ∧ 4000*u≤(g-2)*((t:ℝ)*u) ∧
    2*(200*u)≤(g-2)*((t:ℝ)*u) ∧
    ((2*r:ℕ):ℝ)*(1+(200*u)/((t:ℝ)*u))≤g := by
  intro g
  have htR : (4096:ℝ)≤t := by exact_mod_cast ht
  have hrR : (1:ℝ)≤r := by exact_mod_cast hr
  have htpos : (0:ℝ)<t := by linarith
  have hup : 0<u := by linarith
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg _
  have hid : (g-2)*((t:ℝ)*u)=
      (2*(r:ℝ)-2)*((t:ℝ)*u)+4000*(r:ℝ)*u := by
    dsimp [g]
    field_simp
    ring
  have hterm : 0≤(2*(r:ℝ)-2)*((t:ℝ)*u) :=
    mul_nonneg (by linarith) (mul_nonneg htpos.le hup.le)
  have hru : u≤(r:ℝ)*u := by nlinarith only [mul_le_mul_of_nonneg_right hrR hup.le]
  have hgap : 4000*u≤(g-2)*((t:ℝ)*u) := by nlinarith only [hid,hterm,hru]
  refine ⟨?_,hgap,?_,?_⟩
  · dsimp [g]
    have hf : 0≤(r:ℝ)*(2000/(t:ℝ)) := by positivity
    nlinarith only [hrR,hf]
  · nlinarith only [hgap,hu]
  · have he : (200*u)/((t:ℝ)*u)=200/(t:ℝ) := by
      field_simp
    rw [he]
    push_cast
    dsimp [g]
    have hd : (200:ℝ)/(t:ℝ)≤2000/(t:ℝ) := by
      apply (div_le_div_iff_of_pos_right htpos).mpr
      norm_num
    have hh : 1+200/(t:ℝ)≤1+2000/(t:ℝ) := by linarith only [hd]
    exact mul_le_mul_of_nonneg_left hh (by positivity)

 theorem canonical_phase_credit (t : ℕ) (sigma : ℝ) (ht : 1≤t) :
    let c := 30008*max 1 sigma*(t:ℝ)^3
    30000*(t:ℝ)^3≤c ∧ 8*sigma*(t:ℝ)≤c := by
  intro c
  have htR : (1:ℝ)≤t := by exact_mod_cast ht
  have ht0 : (0:ℝ)≤t := Nat.cast_nonneg _
  have hm : (1:ℝ)≤max 1 sigma := le_max_left _ _
  have hms : sigma≤max 1 sigma := le_max_right _ _
  have hp : (0:ℝ)≤(t:ℝ)^3 := by positivity
  have ht2 : (t:ℝ)≤(t:ℝ)^2 := by nlinarith only [sq_nonneg ((t:ℝ)-1),htR]
  have ht3 : (t:ℝ)≤(t:ℝ)^3 := by nlinarith only [mul_le_mul_of_nonneg_right ht2 ht0,ht2]
  have hscale := mul_le_mul_of_nonneg_left ht3 (show 0≤max 1 sigma by linarith)
  have hs := mul_le_mul_of_nonneg_right hms ht0
  have hbig := mul_le_mul_of_nonneg_right hm hp
  constructor <;> dsimp [c] <;> nlinarith only [hscale,hs,hbig,hp]

end MinorFreeSpanners
