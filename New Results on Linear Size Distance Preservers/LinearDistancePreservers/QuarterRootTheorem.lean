import LinearDistancePreservers.QuarterRootParameters
import LinearDistancePreservers.UniformDimension

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- A stronger corrected near-threshold corollary. The deficit exponent3/4
still exceeds the source's unproved square-root logarithmic deficit. -/
theorem superquadratic_quarter_root {N T : ℕ} (hT : 2≤T) (hTN : T≤N)
    (hN : (8 : ℝ)^4≤Real.log N)
    (hcap : (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3)*Real.exp (-32*(Real.log N)^((3 : ℝ)/4))) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (T : ℝ)^2*Real.exp (Real.sqrt (Real.log N))≤(H.edgeFinset.card : ℝ) := by
  let L := Real.log (N : ℝ)
  let R := L^((4 : ℝ)⁻¹)
  have hL : 0≤L := by dsimp [L]; linarith
  have hR0 : 0≤R := Real.rpow_nonneg hL _
  have hR4 : R^4=L := Real.rpow_inv_natCast_pow hL (by decide : (4 : ℕ)≠0)
  have hR : 8≤R := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hR0 (by decide : (4 : ℕ)≠0)).mp
    simpa only [hR4,L] using hN
  have hR3 : R^3=L^((3 : ℝ)/4) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hL]
    norm_num
  have hR2 : R^2=Real.sqrt L := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg L)).mp
    rw [Real.sq_sqrt hL,← hR4]
    ring
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hT0 : (0 : ℝ)<T := by positivity
  have hN8 : 8≤N := by
    by_contra hn
    have hn7 : (N : ℝ)≤7 := by exact_mod_cast (show N≤7 by omega)
    have hh := Real.log_le_sub_one_of_pos hN0
    linarith
  have hbasic : (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3) := by
    apply hcap.trans
    have he : Real.exp (-32*(Real.log (N : ℝ))^((3 : ℝ)/4))≤1 :=
      Real.exp_le_one_iff.mpr (by have hp := Real.rpow_nonneg hL ((3 : ℝ)/4); dsimp [L] at hp; nlinarith)
    simpa using mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ)≤(N : ℝ)^((2 : ℝ)/3))
  have hhalf := terminal_half_of_cap hN8 hbasic
  have hlog := Real.log_le_log hT0 hcap
  rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow hN0,Real.log_exp] at hlog
  have ht : 32*R^3≤(2/3)*L-Real.log (T : ℝ) := by rw [hR3]; dsimp [L]; linarith
  obtain ⟨d,hd,hlo,hup,hlarge,hupper⟩ := quarter_root_dimension hR
  have hdR : (3 : ℝ)≤d := by exact_mod_cast hd
  have hg := quarter_root_gain hR hdR hlo hup ht
  rw [hR4,sub_sub_cancel,hR2] at hg
  obtain ⟨G,S,hS,hE⟩ := SphereScales.uniform_large_dimension (A := 1) hd hT hhalf
    (log_cap_of_power (by omega) (by omega) hbasic)
    (by simpa [L,← hR2] using hlarge) (by simpa [L,← hR2] using hupper)
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hpPos : 0<(N : ℝ)^(2/((d : ℝ)+1))*(T : ℝ)^((2*(d : ℝ)+1)*((d : ℝ)-1)/((d : ℝ)*((d : ℝ)+1)))/(T : ℝ)^2 := by positivity
  have hpoly : (T : ℝ)^2*Real.exp (16*Real.sqrt L)≤
      (N : ℝ)^(2/((d : ℝ)+1))*(T : ℝ)^((2*(d : ℝ)+1)*((d : ℝ)-1)/((d : ℝ)*((d : ℝ)+1))) := by
    rw [← TheoremFourRateAudit.log_polynomial_ratio hN0 hT0] at hg
    have hh := Real.exp_le_exp.mpr hg
    rw [Real.exp_log hpPos] at hh
    have hr := (le_div_iff₀ (sq_pos_of_pos hT0)).mp hh
    simpa only [mul_comm] using hr
  have hnat : (T : ℝ)^2*Real.exp (16*Real.sqrt L)≤
      (N : ℝ)^((2 : ℝ)/(d+1))*(T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) := by
    simpa only [Nat.cast_sub (show 1≤d by omega),Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hpoly
  have hh := (mul_le_mul_of_nonneg_right hnat (Real.exp_nonneg (-15*Real.sqrt L))).trans
    (by convert hE H hH hp using 1 <;> norm_num [L])
  have heq : ((T : ℝ)^2*Real.exp (16*Real.sqrt L))*Real.exp (-15*Real.sqrt L)=
      (T : ℝ)^2*Real.exp (Real.sqrt L) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  simpa only [heq,L] using hh

end LinearDistancePreservers.TheoremFourGeneral
