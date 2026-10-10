import LinearDistancePreservers.UnlayeredEnvelope
import Mathlib.Analysis.SpecialFunctions.Exp

namespace LinearDistancePreservers.NaturalBoundary
open Filter Asymptotics
open scoped Topology

def vertices (q : ℕ) : ℕ := 2^(3*q^2)
def terminals (k q : ℕ) : ℕ := 2^(2*q^2-k*q)

theorem log_vertices (q : ℕ) :
    Real.log (vertices q : ℝ)=3*(q : ℝ)^2*Real.log 2 := by
  simp only [vertices,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  push_cast
  ring

theorem log_terminals {k q : ℕ} (hkq : k ≤ q) :
    Real.log (terminals k q : ℝ)=(2/3)*Real.log (vertices q : ℝ)-k*q*Real.log 2 := by
  have he : k*q ≤ 2*q^2 := by nlinarith [Nat.mul_le_mul_right q hkq]
  simp only [terminals,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  rw [Nat.cast_sub he,log_vertices]
  push_cast
  ring

theorem sqrt_log_vertices (q : ℕ) :
    Real.sqrt (Real.log (vertices q : ℝ))=(q : ℝ)*Real.sqrt (3*Real.log 2) := by
  rw [log_vertices,show 3*(q : ℝ)^2*Real.log 2=(q : ℝ)^2*(3*Real.log 2) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg q)]

theorem natural_subsequence_little_o {k : ℕ} {c : ℝ}
    (hk : c*Real.sqrt (3*Real.log 2)<(k : ℝ)*Real.log 2) :
    (fun q : ℕ => (terminals k q : ℝ)) =o[atTop]
      (fun q : ℕ => (vertices q : ℝ)^((2 : ℝ)/3)*
        Real.exp (-c*Real.sqrt (Real.log (vertices q : ℝ)))) := by
  let f := fun q : ℕ => (2/3)*Real.log (vertices q : ℝ)-k*q*Real.log 2
  let g := fun q : ℕ => (2/3)*Real.log (vertices q : ℝ)-c*Real.sqrt (Real.log (vertices q : ℝ))
  have hd : Tendsto (fun q : ℕ => g q-f q) atTop atTop := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop).const_mul_atTop (sub_pos.mpr hk)
    convert hh using 1
    funext q
    dsimp [f,g]
    rw [sqrt_log_vertices]
    ring
  have ho := Real.isLittleO_exp_comp_exp_comp.mpr hd
  apply ho.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop k] with q hq
    rw [← Real.exp_log (show (0 : ℝ)<terminals k q by exact_mod_cast Nat.two_pow_pos _),log_terminals hq]
  · filter_upwards [] with q
    rw [Real.rpow_def_of_pos (show (0 : ℝ)<vertices q by exact_mod_cast Nat.two_pow_pos _),← Real.exp_add]
    congr 1
    dsimp [g]
    ring

theorem exists_natural_subsequence (c : ℝ) : ∃ k : ℕ,
    (fun q : ℕ => (terminals k q : ℝ)) =o[atTop]
      (fun q : ℕ => (vertices q : ℝ)^((2 : ℝ)/3)*
        Real.exp (-c*Real.sqrt (Real.log (vertices q : ℝ)))) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (c*Real.sqrt (3*Real.log 2)/Real.log 2)
  refine ⟨k,natural_subsequence_little_o ?_⟩
  exact (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp hk

theorem vertices_tendsto : Tendsto vertices atTop atTop := by
  have he : Tendsto (fun q : ℕ => 3*q^2) atTop atTop :=
    tendsto_atTop_mono (fun q => by
      change q ≤ 3*q^2
      by_cases hq : q=0
      · simp [hq]
      · have hp : 1 ≤ q := by omega
        nlinarith) tendsto_id
  exact (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ)<2)).comp he

theorem terminals_admissible {k q : ℕ} (hkq : k ≤ q) (hq : 1 ≤ q) :
    2 ≤ terminals k q ∧ terminals k q ≤ vertices q := by
  have he : 1 ≤ 2*q^2-k*q := by
    have hh : k*q ≤ q^2 := by simpa [pow_two] using Nat.mul_le_mul_right q hkq
    have hsq : 1 ≤ q^2 := by nlinarith
    omega
  constructor
  · exact Nat.one_lt_two_pow (by omega)
  · apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    omega

theorem subsequence_product_bound {M n b ell d E P k q : ℕ}
    (hkq : k ≤ q) (hq : 1 ≤ q) (hd : 1 ≤ d) (hell : 1 ≤ ell)
    (hinner : ell*b^(d+1) ≤ n)
    (hpaths : P*ell=n^d*b^(d*(d-1))) (hports : P ≤ M)
    (hvertices : M*n^d ≤ vertices q) (hterminals : M ≤ terminals k q)
    (hE : E ≤ M*n^d*b^(d*(d-1))+2*M*P) :
    (E : ℝ) ≤ 3*Real.exp (6*(k : ℝ)^2)*(terminals k q : ℝ)^2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hsqrt : Real.log 2 ≤ Real.sqrt (3*Real.log 2) := by
    have hp := Real.sqrt_nonneg (3*Real.log 2)
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 3*Real.log 2)
    have hm := mul_nonneg hl.le (show 0 ≤ 3-Real.log 2 by linarith)
    nlinarith
  have hdeficit : (k : ℝ)*q*Real.log 2 ≤ (k : ℝ)*Real.sqrt (Real.log (vertices q : ℝ)) := by
    rw [sqrt_log_vertices]
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (k : ℝ)*q by positivity)]
  have hN : 1 < vertices q := Nat.one_lt_two_pow (by
    have hqp : q ≠ 0 := by omega
    exact Nat.mul_ne_zero (by decide) (pow_ne_zero _ hqp))
  have hT : 0 < terminals k q := by unfold terminals; positivity
  have hb := UnlayeredEnvelope.full_product_sqrt_deficit hd hell hN hT hinner hpaths hports
    hvertices hterminals hE (by positivity : 0 ≤ (k : ℝ)*q*Real.log 2)
    (Nat.cast_nonneg k) (log_terminals hkq) hdeficit
  nlinarith only [hb]

/-- Every fixed square-root-deficit range contains an explicit admissible
natural subsequence on which the reviewed count template has bounded gain.
The conclusion constrains that template only, not arbitrary graph witnesses. -/
theorem every_deficit_has_bounded_count_subsequence (c : ℝ) :
    ∃ (k : ℕ) (B : ℝ), 0 < B ∧ Tendsto vertices atTop atTop ∧
      ((fun q : ℕ => (terminals k q : ℝ)) =o[atTop]
        (fun q : ℕ => (vertices q : ℝ)^((2 : ℝ)/3)*
          Real.exp (-c*Real.sqrt (Real.log (vertices q : ℝ))))) ∧
      ∀ q : ℕ, k ≤ q → 1 ≤ q →
        2 ≤ terminals k q ∧ terminals k q ≤ vertices q ∧
        ∀ (M n b ell d E P : ℕ), 1 ≤ d → 1 ≤ ell →
          ell*b^(d+1) ≤ n → P*ell=n^d*b^(d*(d-1)) → P ≤ M →
          M*n^d ≤ vertices q → M ≤ terminals k q →
          E ≤ M*n^d*b^(d*(d-1))+2*M*P →
          (E : ℝ) ≤ B*(terminals k q : ℝ)^2 := by
  obtain ⟨k,hk⟩ := exists_natural_subsequence c
  refine ⟨k,3*Real.exp (6*(k : ℝ)^2),by positivity,vertices_tendsto,hk,?_⟩
  intro q hkq hq
  refine ⟨(terminals_admissible hkq hq).1,(terminals_admissible hkq hq).2,?_⟩
  intro M n b ell d E P hd hell hi hp hports hv ht he
  exact subsequence_product_bound hkq hq hd hell hi hp hports hv ht he

end LinearDistancePreservers.NaturalBoundary
