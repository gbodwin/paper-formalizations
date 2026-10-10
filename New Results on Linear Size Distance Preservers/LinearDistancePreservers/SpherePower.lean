import LinearDistancePreservers.SphereScales
import LinearDistancePreservers.RootRate
import LinearDistancePreservers.TheoremFourRateAudit

namespace LinearDistancePreservers.SphereScales

/-- The exact determinant identity of the elementary-sphere counts.
No asymptotic or dimension-dependent constant is suppressed. -/
theorem ideal_power_identity (d : ℕ) (hd : 3 ≤ d) (M K u v : ℝ) :
    M^(d*(d-2))*(K*u^d*v^(2*d-2))^((d+1)*(d-2))*
      (2*M*K*u^(d+1)*v^d)^(2*d-2) =
    (2 : ℝ)^(2*d-2)*K^(d-2)*
      (M*K*u^(d+1)*v^(2*d-2))^(d^2-2) := by
  let a := d*(d-2)
  let e := (d+1)*(d-2)
  let c := 2*d-2
  let D := d^2-2
  have hdsub := Nat.sub_add_cancel (show 2≤d by omega)
  have hcsub := Nat.sub_add_cancel (show 2≤2*d by omega)
  have hDsub := Nat.sub_add_cancel (show 2≤d^2 by nlinarith)
  have hm : a+c=D := by dsimp [a,c,D]; nlinarith
  have hk : e+c=D+(d-2) := by dsimp [e,c,D]; nlinarith
  have hu : d*e+(d+1)*c=(d+1)*D := by
    have he : e+d=D := by dsimp [e,D]; nlinarith
    have hc : c+d^2=(d+1)*d+(d-2) := by dsimp [c]; nlinarith
    dsimp [e,c,D]
    nlinarith
  have hv : c*e+d*c=c*D := by
    have he : e+d=D := by dsimp [e,D]; nlinarith
    rw [← he]
    ring
  change M^a*(K*u^d*v^c)^e*(2*M*K*u^(d+1)*v^d)^c =
    2^c*K^(d-2)*(M*K*u^(d+1)*v^c)^D
  calc
    _ = 2^c*M^(a+c)*K^(e+c)*u^(d*e+(d+1)*c)*v^(c*e+d*c) := by
      simp only [mul_pow,← pow_mul,pow_add]
      ring
    _ = 2^c*M^D*K^(D+(d-2))*u^((d+1)*D)*v^(c*D) := by rw [hm,hk,hu,hv]
    _ = _ := by simp only [mul_pow,← pow_mul,pow_add]; ring

end LinearDistancePreservers.SphereScales

namespace LinearDistancePreservers.SphereScales

/-- The elementary-sphere power coefficient has an exponential-in-d root,
with no lattice-volume or flatness constant. -/
theorem sphere_coefficient_bound {d : ℕ} (hd : 3 ≤ d) :
    2^((3*d-1)*(d^2-2)+(2*d-2))*d^(d*(d-2)) ≤
      (2^(3*d+1)*d)^(d^2-2) := by
  have hD : 2≤d^2 := by nlinarith
  have hs := Nat.sub_add_cancel hD
  have h3 := Nat.sub_add_cancel (show 1≤3*d by omega)
  have h2 := Nat.sub_add_cancel (show 2≤2*d by omega)
  have hd2 := Nat.sub_add_cancel (show 2≤d by omega)
  have he : (3*d-1)*(d^2-2)+(2*d-2) ≤ (3*d+1)*(d^2-2) := by nlinarith
  have ha : d*(d-2) ≤ d^2-2 := by nlinarith
  calc
    _ ≤ 2^((3*d+1)*(d^2-2))*d^(d^2-2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) he)
        (Nat.pow_le_pow_right (by omega) ha)
    _ = _ := by rw [mul_pow,← pow_mul]

/-- Exact positive-root conversion of the three-factor sphere rate. -/
theorem sphere_rate_of_power {N M Q E d : ℕ} (hd : 3 ≤ d)
    (h : (M : ℝ)^(d*(d-2))*(Q : ℝ)^((d+1)*(d-2))*(N : ℝ)^(2*d-2) ≤
      (2 : ℝ)^((3*d-1)*(d^2-2)+(2*d-2))*(d : ℝ)^(d*(d-2))*(E : ℝ)^(d^2-2)) :
    (N : ℝ)^(((2*d-2 : ℕ) : ℝ)/(d^2-2 : ℕ))*
      (M : ℝ)^(((d*(d-2) : ℕ) : ℝ)/(d^2-2 : ℕ))*
      (Q : ℝ)^((((d+1)*(d-2) : ℕ) : ℝ)/(d^2-2 : ℕ)) ≤
        (2^(3*d+1)*d : ℕ)*(E : ℝ) := by
  let D := d^2-2
  have hD : D≠0 := by
    dsimp [D]
    have hh : 9≤d^2 := by nlinarith
    omega
  have hDr : (D : ℝ)≠0 := by exact_mod_cast hD
  have hn : ((N : ℝ)^(((2*d-2 : ℕ) : ℝ)/D))^D=(N : ℝ)^(2*d-2) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have hm : ((M : ℝ)^(((d*(d-2) : ℕ) : ℝ)/D))^D=(M : ℝ)^(d*(d-2)) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have hq : ((Q : ℝ)^((((d+1)*(d-2) : ℕ) : ℝ)/D))^D=(Q : ℝ)^((d+1)*(d-2)) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg Q),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have hc : (2 : ℝ)^((3*d-1)*D+(2*d-2))*(d : ℝ)^(d*(d-2)) ≤
      ((2^(3*d+1)*d : ℕ) : ℝ)^D := by exact_mod_cast sphere_coefficient_bound hd
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rw [mul_pow,mul_pow,hn,hm,hq,mul_pow]
  calc
    _ ≤ (2 : ℝ)^((3*d-1)*D+(2*d-2))*(d : ℝ)^(d*(d-2))*(E : ℝ)^D := by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using h
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

end LinearDistancePreservers.SphereScales

namespace LinearDistancePreservers.SphereScales
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Fully parameter-selected elementary-sphere graph lower bound, with
its literal finite coefficient and no direction or geometric premise. -/
theorem capacity_power_bound {d M R Q N T : ℕ}
    (hd : 3 ≤ d) (hM : 0 < M) (hQ : 0 < Q) (hQM : Q ≤ M) (hR : 3*R ≤ M)
    (hcap : Q ≤ rothNumberNat R) (hMN : 4*M ≤ N)
    (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t=G.edist s t) →
        (M : ℝ)^(d*(d-2))*(Q : ℝ)^((d+1)*(d-2))*(N : ℝ)^(2*d-2) ≤
          (2 : ℝ)^((3*d-1)*(d^2-2)+(2*d-2))*(d : ℝ)^(d*(d-2))*
            (H.edgeFinset.card : ℝ)^(d^2-2) := by
  have hd0 : 0<d := by omega
  have hN : 0<N := by omega
  obtain ⟨u,v,hu,hv,hA,hB⟩ := exists_ideal_scales hd
    (by positivity : (0 : ℝ)<(N : ℝ)/(2*M*(d : ℝ)^d))
    (by positivity : (0 : ℝ)<(Q : ℝ)/(d : ℝ)^d)
  obtain ⟨G,S,hS,hE⟩ := capacity_of_ideal_scales hd hM hQM hR hcap hMN hT hTN hu hv hA hB
  have hQexpr : (Q : ℝ)=(d : ℝ)^d*u^d*v^(2*d-2) := by
    have hh := (eq_div_iff (by positivity : (d : ℝ)^d≠0)).mp hB
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.symm
  have hNexpr : (N : ℝ)=2*M*(d : ℝ)^d*u^(d+1)*v^d := by
    have hh := (eq_div_iff (by positivity : (2*(M : ℝ)*(d : ℝ)^d)≠0)).mp hA
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.symm
  have hZexpr : (M : ℝ)*(d : ℝ)^d*u^(d+1)*v^(2*d-2)=(M : ℝ)*Q*u := by
    rw [hQexpr,pow_succ]
    ring
  have hid := ideal_power_identity d hd (M : ℝ) ((d : ℝ)^d) u v
  rw [← hQexpr,← hNexpr,hZexpr,← pow_mul] at hid
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(M : ℝ)*Q*u)
    (hE H hH hp) (d^2-2)
  calc
    _ = (2 : ℝ)^(2*d-2)*(d : ℝ)^(d*(d-2))*((M : ℝ)*Q*u)^(d^2-2) := hid
    _ ≤ (2 : ℝ)^(2*d-2)*(d : ℝ)^(d*(d-2))*
        ((2 : ℝ)^(3*d-1)*(H.edgeFinset.card : ℝ))^(d^2-2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [mul_pow,← pow_mul]
      calc
        _ = ((2 : ℝ)^(2*d-2)*2^((3*d-1)*(d^2-2)))*
            (d : ℝ)^(d*(d-2))*(H.edgeFinset.card : ℝ)^(d^2-2) := by ring
        _ = _ := by rw [← pow_add,add_comm (2*d-2)]

theorem capacity_rate {d M R Q N T : ℕ}
    (hd : 3 ≤ d) (hM : 0 < M) (hQ : 0 < Q) (hQM : Q ≤ M) (hR : 3*R ≤ M)
    (hcap : Q ≤ rothNumberNat R) (hMN : 4*M ≤ N)
    (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t=G.edist s t) →
        (N : ℝ)^(((2*d-2 : ℕ) : ℝ)/(d^2-2 : ℕ))*
          (M : ℝ)^(((d*(d-2) : ℕ) : ℝ)/(d^2-2 : ℕ))*
          (Q : ℝ)^((((d+1)*(d-2) : ℕ) : ℝ)/(d^2-2 : ℕ)) ≤
            (2^(3*d+1)*d : ℕ)*(H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := capacity_power_bound hd hM hQ hQM hR hcap hMN hT hTN
  exact ⟨G,S,hS,fun H hH hp => sphere_rate_of_power hd (hE H hH hp)⟩

end LinearDistancePreservers.SphereScales

