import LinearDistancePreservers.ConstructionEnvelope

/-! A count obstruction for an ideal unlayered straight-line inner family.
This does not construct an unlayered graph or bound arbitrary graph families. -/
namespace LinearDistancePreservers.UnlayeredEnvelope

/-- Removing a layer factor from vertices also divides the path capacity
by the path length. Even ideal outer capacity retains a polynomial envelope. -/
theorem edge_power_envelope {M n b ell d N T E : ℕ} (hd : 1 ≤ d)
    (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M*ell)
    (hvertices : M*n^d ≤ N) (hterminals : M ≤ T)
    (hE : E ≤ M*n^d*b^(d*(d-1))) :
    E^(d^2+1) ≤ T^((2*d-1)*(d-1))*N^(2*d) := by
  let a := d*(d-1)
  let D := d^2+1
  let beta := (2*d-1)*(d-1)
  have hdsub : d-1+1=d := Nat.sub_add_cancel hd
  have h2sub : 2*d-1+1=2*d := Nat.sub_add_cancel (by omega)
  have ha : a+d=d^2 := by dsimp [a]; nlinarith
  have hb : a*a+(d+1)*a=a*D := by
    calc
      _ = a*(a+d+1) := by ring
      _ = a*D := by rw [ha]
  have hn : d*a+d*(d+1)=d*D := by dsimp [a,D]; nlinarith
  have hn2 : a+d*(d+1)=2*d^2 := by dsimp [a]; nlinarith
  have hm : D+a=beta+2*d := by dsimp [D,a,beta]; nlinarith
  have hp : (n^d*b^a)^a*b^((d+1)*a) ≤ M^a*n^a := by
    calc
      _ ≤ (M*ell)^a*b^((d+1)*a) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hports _)
      _ = M^a*(ell*b^(d+1))^a := by simp only [mul_pow,← pow_mul]; ring
      _ ≤ M^a*n^a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinner _)
  have hp' : n^(d*a)*b^(a*D) ≤ M^a*n^a := by
    simpa only [mul_pow,← pow_mul,mul_assoc,← pow_add,hb] using hp
  have hmain : (M*n^d*b^a)^D ≤ M^beta*(M*n^d)^(2*d) := by
    have hh := Nat.mul_le_mul_right (M^D*n^(d*(d+1))) hp'
    calc
      _ = (n^(d*a)*b^(a*D))*(M^D*n^(d*(d+1))) := by
        simp only [mul_pow,← pow_mul]
        rw [← hn,pow_add]
        ring
      _ ≤ (M^a*n^a)*(M^D*n^(d*(d+1))) := hh
      _ = M^(D+a)*n^(a+d*(d+1)) := by simp only [pow_add]; ring
      _ = M^(beta+2*d)*n^(2*d^2) := by rw [hm,hn2]
      _ = M^beta*(M*n^d)^(2*d) := by
        simp only [mul_pow,← pow_mul,pow_add]
        have he : 2*d^2=d*(2*d) := by ring
        rw [he]
        ring
  calc
    E^D ≤ (M*n^d*b^a)^D := Nat.pow_le_pow_left hE _
    _ ≤ M^beta*(M*n^d)^(2*d) := hmain
    _ ≤ T^beta*N^(2*d) := by gcongr

theorem edge_envelope {M n b ell d N T E : ℕ} (hd : 1 ≤ d)
    (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M*ell)
    (hvertices : M*n^d ≤ N) (hterminals : M ≤ T)
    (hE : E ≤ M*n^d*b^(d*(d-1))) :
    (E : ℝ) ≤ (N : ℝ)^((2*(d : ℝ))/(d^2+1))*
      (T : ℝ)^(((2*(d : ℝ)-1)*(d-1))/(d^2+1)) := by
  let D := d^2+1
  let beta := (2*d-1)*(d-1)
  have hD : D ≠ 0 := by dsimp [D]; omega
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hcast : (D : ℝ)=(d : ℝ)^2+1 := by dsimp [D]; push_cast; rfl
  have hbcast : (beta : ℝ)=(2*(d : ℝ)-1)*(d-1) := by
    dsimp [beta]
    rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_sub hd]
    push_cast
    rfl
  have hn : ((N : ℝ)^((2*(d : ℝ))/(d^2+1)))^D = (N : ℝ)^(2*d) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    rw [← hcast,div_mul_cancel₀ _ hDr]
    norm_cast
  have ht : ((T : ℝ)^(((2*(d : ℝ)-1)*(d-1))/(d^2+1)))^D = (T : ℝ)^beta := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T)]
    rw [← hcast,div_mul_cancel₀ _ hDr,← hbcast,Real.rpow_natCast]
  have hp : (E : ℝ)^D ≤ (T : ℝ)^beta*(N : ℝ)^(2*d) := by
    exact_mod_cast edge_power_envelope hd hinner hports hvertices hterminals hE
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rw [mul_pow,hn,ht]
  simpa only [mul_comm] using hp

noncomputable def logRatio (d L t : ℝ) : ℝ :=
  ((3*d+1)*t-(2/3)*L)/(d^2+1)

/-- The unlayered count improvement still gives only O(t²/L) gain. -/
theorem logRatio_le {d L t : ℝ} (hd : 1 ≤ d) (hL : 0 < L) (ht : 0 ≤ t) :
    logRatio d L t ≤ 6*t^2/L := by
  have hnum : (3*d+1)*t ≤ 4*d*t := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) ht]
  have hh := mul_le_mul_of_nonneg_left hnum hL.le
  unfold logRatio
  apply (div_le_div_iff₀ (by positivity : 0 < d^2+1) hL).mpr
  nlinarith [sq_nonneg (3*d*t-L),sq_nonneg t]

theorem sqrt_deficit_le {d L t K : ℝ} (hd : 1 ≤ d) (hL : 0 < L)
    (ht : 0 ≤ t) (_hK : 0 ≤ K) (hdeficit : t ≤ K*Real.sqrt L) :
    logRatio d L t ≤ 6*K^2 := by
  have hsq : t^2 ≤ K^2*L := by
    have hh := pow_le_pow_left₀ ht hdeficit 2
    simpa only [mul_pow,Real.sq_sqrt hL.le] using hh
  apply (logRatio_le hd hL ht).trans
  apply (div_le_iff₀ hL).mpr
  nlinarith only [hsq]

/-- Exact connection to the alternative polynomial envelope. -/
theorem polynomial_sqrt_deficit {N T d t K : ℝ}
    (hN : 1 < N) (hT : 0 < T) (hd : 1 ≤ d)
    (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hlog : Real.log T=(2/3)*Real.log N-t)
    (hdeficit : t ≤ K*Real.sqrt (Real.log N)) :
    N^(2*d/(d^2+1))*T^((2*d-1)*(d-1)/(d^2+1)) ≤
      T^2*Real.exp (6*K^2) := by
  have hden : d^2+1 ≠ 0 := by positivity
  have he : (2*d/(d^2+1))*Real.log N+
      ((2*d-1)*(d-1)/(d^2+1))*Real.log T =
      2*Real.log T+logRatio d (Real.log N) t := by
    rw [hlog]
    unfold logRatio
    field_simp
    ring
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN),Real.rpow_def_of_pos hT,
    ← Real.exp_add]
  have hp : T^2 = Real.exp (2*Real.log T) := by
    rw [show (2 : ℝ)*Real.log T=Real.log T+Real.log T by ring,Real.exp_add,Real.exp_log hT]
    ring
  rw [hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [mul_comm (Real.log N),mul_comm (Real.log T),he]
  exact add_le_add_right (sqrt_deficit_le hd (Real.log_pos hN) ht hK hdeficit) _

/-- The entire specified ideal count family has bounded gain at every fixed
square-root-log deficit. This is not an upper bound for arbitrary graphs. -/
theorem full_edge_sqrt_deficit {M n b ell d N T E : ℕ} {t K : ℝ}
    (hd : 1 ≤ d) (hN : 1 < N) (hT : 0 < T)
    (hinner : ell*b^(d+1) ≤ n)
    (hports : n^d*b^(d*(d-1)) ≤ M*ell)
    (hvertices : M*n^d ≤ N) (hterminals : M ≤ T)
    (hE : E ≤ M*n^d*b^(d*(d-1)))
    (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hlog : Real.log (T : ℝ)=(2/3)*Real.log (N : ℝ)-t)
    (hdeficit : t ≤ K*Real.sqrt (Real.log (N : ℝ))) :
    (E : ℝ) ≤ (T : ℝ)^2*Real.exp (6*K^2) := by
  exact (edge_envelope hd hinner hports hvertices hterminals hE).trans
    (polynomial_sqrt_deficit (by exact_mod_cast hN) (by exact_mod_cast hT)
      (by exact_mod_cast hd) ht hK hlog hdeficit)

/-- Include two outer connectors per assigned path in the exact ideal
unlayered product counts. The constant three does not change the obstruction. -/
theorem full_product_sqrt_deficit {M n b ell d N T E P : ℕ} {t K : ℝ}
    (hd : 1 ≤ d) (hell : 1 ≤ ell) (hN : 1 < N) (hT : 0 < T)
    (hinner : ell*b^(d+1) ≤ n)
    (hpaths : P*ell=n^d*b^(d*(d-1))) (hports : P ≤ M)
    (hvertices : M*n^d ≤ N) (hterminals : M ≤ T)
    (hE : E ≤ M*n^d*b^(d*(d-1))+2*M*P)
    (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hlog : Real.log (T : ℝ)=(2/3)*Real.log (N : ℝ)-t)
    (hdeficit : t ≤ K*Real.sqrt (Real.log (N : ℝ))) :
    (E : ℝ) ≤ 3*(T : ℝ)^2*Real.exp (6*K^2) := by
  have hcapacity : n^d*b^(d*(d-1)) ≤ M*ell := by
    rw [← hpaths]
    exact Nat.mul_le_mul_right ell hports
  have hp : P ≤ n^d*b^(d*(d-1)) := by
    rw [← hpaths]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hc : E ≤ 3*(M*n^d*b^(d*(d-1))) := by nlinarith [Nat.mul_le_mul_left M hp]
  have hb := full_edge_sqrt_deficit hd hN hT hinner hcapacity hvertices hterminals
    (le_refl (M*n^d*b^(d*(d-1)))) ht hK hlog hdeficit
  calc
    (E : ℝ) ≤ 3*((M*n^d*b^(d*(d-1)) : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ 3*((T : ℝ)^2*Real.exp (6*K^2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end LinearDistancePreservers.UnlayeredEnvelope
