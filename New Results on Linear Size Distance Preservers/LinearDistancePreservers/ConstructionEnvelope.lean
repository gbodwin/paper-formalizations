import LinearDistancePreservers.HigherParameters
import LinearDistancePreservers.TheoremFourRateAudit

/-! Upper envelopes for the actual sharp-direction obstacle-product count
family. These are not upper bounds for arbitrary graph constructions. -/
namespace LinearDistancePreservers.ConstructionEnvelope

theorem product_power_envelope {M n b ell d : ℕ} (hd : 1 ≤ d)
    (hinner : ell*b^(d+1) ≤ n) :
    (M*n^d*b^(d*(d-1))*ell)^(d*(d+1)) ≤
      M^(d*(d-1))*(n^d*b^(d*(d-1)))^(d^2-1)*(M*ell*n^d)^(2*d) := by
  let D := d*(d+1)
  let a := d*(d-1)
  let e := d^2-1
  have hs := Nat.sub_add_cancel hd
  have hs2 := Nat.sub_add_cancel (show 1 ≤ d^2 by nlinarith)
  have ha : a+2*d=D := (HigherParameters.exponent_identities hd).1
  have he : e+(d+1)=D := (HigherParameters.exponent_identities hd).2.2
  have hb : a*e+(d+1)*a=a*D := by rw [← he]; ring
  have hn : d*e+d*(2*d)=d*D+a := by
    dsimp [a,e,D]
    nlinarith
  let C := M^D*n^(d*D)*b^(a*e)*ell^(2*d)
  have hleft : C*(ell*b^(d+1))^a = (M*n^d*b^a*ell)^D := by
    dsimp [C]
    rw [mul_pow,← pow_mul]
    calc
      _ = M^D*n^(d*D)*(b^(a*e)*b^((d+1)*a))*(ell^(2*d)*ell^a) := by ring
      _ = M^D*n^(d*D)*b^(a*D)*ell^D := by
        rw [← pow_add,← pow_add,hb,show 2*d+a=D by omega]
      _ = _ := by simp only [mul_pow,← pow_mul]
  have hright : M^a*(n^d*b^a)^e*(M*ell*n^d)^(2*d) = C*n^a := by
    simp only [mul_pow,← pow_mul]
    calc
      _ = (M^a*M^(2*d))*(n^(d*e)*n^(d*(2*d)))*b^(a*e)*ell^(2*d) := by ring
      _ = M^D*n^(d*D+a)*b^(a*e)*ell^(2*d) := by
        rw [← pow_add,← pow_add,ha,hn]
      _ = C*n^a := by rw [pow_add]; dsimp [C]; ring
  change (M*n^d*b^a*ell)^D ≤ M^a*(n^d*b^a)^e*(M*ell*n^d)^(2*d)
  rw [← hleft,hright]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinner _)

/-- Every graph produced with these exact counts lies below the same
polynomial envelope, regardless of improved constants or outer port sets. -/
theorem full_edge_power_envelope {M n b ell d N T E : ℕ} (hd : 1 ≤ d)
    (hell : 1 ≤ ell) (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M) (hvertices : M*ell*n^d ≤ N)
    (hterminals : M ≤ T) (hE : E=M*n^d*b^(d*(d-1))*(ell+1)) :
    E^(d*(d+1)) ≤ 2^(d*(d+1))*T^((2*d+1)*(d-1))*N^(2*d) := by
  let D := d*(d+1)
  let a := d*(d-1)
  let e := d^2-1
  have hs := Nat.sub_add_cancel hd
  have hs2 := Nat.sub_add_cancel (show 1 ≤ d^2 by nlinarith)
  have hexp : a+e=(2*d+1)*(d-1) := by dsimp [a,e]; nlinarith
  have hE' : E ≤ 2*(M*n^d*b^a*ell) := by
    rw [hE]
    have h := Nat.mul_le_mul_left (M*n^d*b^a) (show ell+1 ≤ 2*ell by omega)
    simpa [a,mul_assoc,mul_comm,mul_left_comm] using h
  have hp := product_power_envelope (M := M) hd hinner
  calc
    E^D ≤ (2*(M*n^d*b^a*ell))^D := Nat.pow_le_pow_left hE' _
    _ = 2^D*(M*n^d*b^a*ell)^D := mul_pow _ _ _
    _ ≤ 2^D*(M^a*(n^d*b^a)^e*(M*ell*n^d)^(2*d)) := Nat.mul_le_mul_left _ hp
    _ ≤ 2^D*(T^a*T^e*N^(2*d)) := by
      gcongr
      exact hports.trans hterminals
    _ = _ := by rw [← pow_add,hexp]; ring

/-- Real-power envelope obtained by the exact positive root. -/
theorem full_edge_envelope {M n b ell d N T E : ℕ} (hd : 1 ≤ d)
    (hell : 1 ≤ ell) (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M) (hvertices : M*ell*n^d ≤ N)
    (hterminals : M ≤ T) (hE : E=M*n^d*b^(d*(d-1))*(ell+1)) :
    (E : ℝ) ≤ 2*(N : ℝ)^((2 : ℝ)/(d+1))*
      (T : ℝ)^(((2*(d : ℝ)+1)*(d-1))/(d*(d+1))) := by
  let D := d*(d+1)
  let p := (2*d+1)*(d-1)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  have hn : ((N : ℝ)^((2 : ℝ)/(d+1)))^D = (N : ℝ)^(2*d) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    have he : (2/((d : ℝ)+1))*(D : ℝ)=((2*d : ℕ) : ℝ) := by
      dsimp [D]; push_cast; field_simp
    rw [he,Real.rpow_natCast]
  have hpcast : (p : ℝ)=(2*(d : ℝ)+1)*(d-1) := by
    dsimp [p]
    rw [Nat.cast_mul,Nat.cast_sub hd]
    push_cast
    rfl
  have ht : ((T : ℝ)^(((2*(d : ℝ)+1)*(d-1))/(d*(d+1))))^D = (T : ℝ)^p := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T)]
    have he : ((2*(d : ℝ)+1)*(d-1))/(d*(d+1))*(D : ℝ)=(p : ℝ) := by
      rw [hpcast]
      dsimp [D]; push_cast; field_simp
    rw [he,Real.rpow_natCast]
  have hh := full_edge_power_envelope hd hell hinner hports hvertices hterminals hE
  have hh' : (E : ℝ)^D ≤ (2 : ℝ)^D*(T : ℝ)^p*(N : ℝ)^(2*d) := by exact_mod_cast hh
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rw [mul_pow,mul_pow,hn,ht]
  simpa [mul_assoc,mul_comm,mul_left_comm] using hh'

/-- For this complete count family, a fixed square-root logarithmic terminal
 deficit permits only a bounded edge/terminal-square ratio. This bounds the
 entire constructed graph, not just its proved lower-bound expression. -/
theorem full_edge_sqrt_deficit {M n b ell d N T E : ℕ} (hd : 1 ≤ d)
    (hell : 1 ≤ ell) (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M) (hvertices : M*ell*n^d ≤ N)
    (hterminals : M ≤ T) (hE : E=M*n^d*b^(d*(d-1))*(ell+1))
    (hN : 1 < N) (hT : 0 < T) {t K : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hlog : Real.log (T : ℝ)=(2/3)*Real.log N-t)
    (hdeficit : t ≤ K*Real.sqrt (Real.log N)) :
    (E : ℝ) ≤ 2*(T : ℝ)^2*Real.exp (27*K^2/8) := by
  have he := full_edge_envelope hd hell hinner hports hvertices hterminals hE
  have hr := TheoremFourRateAudit.suppressed_expression_le
    (by exact_mod_cast hN : (1 : ℝ)<N)
    (by exact_mod_cast hT : (0 : ℝ)<T)
    (by exact_mod_cast hd : (1 : ℝ)≤d) ht hK hlog hdeficit (c := 0)
  simp only [zero_mul,neg_zero,Real.exp_zero,mul_one,sub_zero] at hr
  have hr' := (div_le_iff₀ (by positivity : (0 : ℝ)<(T : ℝ)^2)).mp hr
  nlinarith only [he,hr']

end LinearDistancePreservers.ConstructionEnvelope
