import LinearDistancePreservers.TheoremFourPlanar

namespace LinearDistancePreservers.SphereScales
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- A dense common-sphere direction family with a coefficient only linear
in the dimension in the coordinate radius. No lattice-flatness input. -/
theorem direction_capacity {d b : ℕ} (hd : 3 ≤ d) (hb : 0 < b) :
    b^(d-2)*(d*(d*b-1)^2+1) ≤ (d*b)^d := by
  have hr : 0 < d*b := by positivity
  have hsub : d*b-1+1 = d*b := Nat.sub_add_cancel (by omega)
  have hbound : d*(d*b-1)^2+1 ≤ d*(d*b)^2 := by
    have hd1 : 1 ≤ d := by omega
    calc
      _ ≤ d*(d*b-1)^2+d := Nat.add_le_add_left hd1 _
      _ = d*((d*b-1)^2+1) := by ring
      _ ≤ d*((d*b-1)+1)^2 := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by rw [hsub]
  have he : d-2+2=d := Nat.sub_add_cancel (by omega)
  have hbpow : b^(d-2)*b^2=b^d := by rw [← pow_add,he]
  have hdP : d^3 ≤ d^d := Nat.pow_le_pow_right (by omega) hd
  calc
    _ ≤ b^(d-2)*(d*(d*b)^2) := Nat.mul_le_mul_left _ hbound
    _ = d^3*(b^(d-2)*b^2) := by rw [mul_pow]; ring
    _ = d^3*b^d := by rw [hbpow]
    _ ≤ d^d*b^d := Nat.mul_le_mul_right _ hdP
    _ = _ := (mul_pow _ _ _).symm

/-- The alternative elementary-sphere graph family, with exact prescribed
vertex/terminal counts and every edge forced by native terminal distances. -/
theorem graph_lower_bound {d b ell M R N T : ℕ}
    (hd : 3 ≤ d) (hb : 0 < b) (hell : 0 < ell) (hM : 0 < M)
    (hR : 3*R ≤ M)
    (hcap : (d*ell*b)^d*b^(d-2) ≤ rothNumberNat R)
    (hN : 2*M+M*ell*(d*ell*b)^d ≤ N)
    (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t=G.edist s t) →
        H.edgeFinset.card=M*(d*ell*b)^d*b^(d-2)*(ell+1) := by
  letI : NeZero (d*ell*b) := ⟨by positivity⟩
  letI : NeZero M := ⟨by omega⟩
  have hell' : ell-1+1=ell := Nat.sub_add_cancel hell
  obtain ⟨G,S,hS,hE⟩ := BehrendProduct.sphere_lower_bound_of_roth
    (d := d) (r := d*b) (x := b^(d-2)) (n := d*ell*b) (k := ell-1)
    (M := M) (R := R) (N := N) (T := T) (direction_capacity hd hb)
    (by rw [hell']; nlinarith) hR hcap (by simpa [hell'] using hN) hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  simpa [show ell-1+2=ell+1 by omega] using hE H hH hp

end LinearDistancePreservers.SphereScales


namespace LinearDistancePreservers.SphereScales

/-- The two positive real scales underlying the integer sphere family.
This solves both the vertex and port equations with determinant d²−2. -/
theorem exists_ideal_scales {d : ℕ} (hd : 3 ≤ d) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      u^(d+1)*v^d=A ∧ u^d*v^(2*d-2)=B := by
  let D : ℝ := (d : ℝ)^2-2
  let a : ℝ := ((2*d-2)*Real.log A-d*Real.log B)/D
  let b : ℝ := ((d+1)*Real.log B-d*Real.log A)/D
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : D ≠ 0 := by dsimp [D]; nlinarith
  have hD0 : (d : ℝ)^2-2 ≠ 0 := hD
  have hcast : ((2*d-2 : ℕ) : ℝ)=2*(d : ℝ)-2 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul]
    norm_num
  refine ⟨Real.exp a,Real.exp b,Real.exp_pos _,Real.exp_pos _,?_,?_⟩
  · rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
    convert Real.exp_log hA using 1
    congr 1
    dsimp [a,b,D]
    push_cast
    field_simp [hD0]
    ring
  · rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
    convert Real.exp_log hB using 1
    congr 1
    dsimp [a,b,D]
    rw [hcast]
    field_simp [hD0]
    ring

/-- Positive real scales have positive integer floors with at most a
factor-two loss, including the boundary scale one. -/
theorem floor_scale {x : ℝ} (hx : 1 ≤ x) :
    0 < ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) ≤ x ∧ x ≤ 2*(⌊x⌋₊ : ℝ) := by
  have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  have hle := Nat.floor_le (show 0 ≤ x by linarith)
  have hlt := Nat.lt_floor_add_one x
  refine ⟨by omega,hle,?_⟩
  have hfr : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf
  linarith

end LinearDistancePreservers.SphereScales

namespace LinearDistancePreservers.SphereScales

theorem port_count_identity (d ell b : ℕ) (hd : 2 ≤ d) :
    (d*ell*b)^d*b^(d-2)=d^d*ell^d*b^(2*d-2) := by
  have he : d+(d-2)=2*d-2 := by omega
  rw [mul_pow,mul_pow,mul_assoc,← pow_add,he]

theorem vertex_count_identity (d ell b : ℕ) :
    ell*(d*ell*b)^d=d^d*ell^(d+1)*b^d := by
  rw [mul_pow,mul_pow,pow_succ]
  ring

/-- Rounding both positive ideal scales loses at most 2^(3d-1) in
forced edges and never enlarges either count budget. -/
theorem rounded_scales {d : ℕ} (hd : 3 ≤ d) {u v : ℝ}
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ∃ ell b : ℕ, 0 < ell ∧ 0 < b ∧
      (ell : ℝ)^(d+1)*(b : ℝ)^d ≤ u^(d+1)*v^d ∧
      (ell : ℝ)^d*(b : ℝ)^(2*d-2) ≤ u^d*v^(2*d-2) ∧
      u^(d+1)*v^(2*d-2) ≤ (2 : ℝ)^(3*d-1)*
        ((ell : ℝ)^(d+1)*(b : ℝ)^(2*d-2)) := by
  obtain ⟨hel,hle,hue⟩ := floor_scale hu
  obtain ⟨hbl,hbe,hvb⟩ := floor_scale hv
  refine ⟨⌊u⌋₊,⌊v⌋₊,hel,hbl,?_,?_,?_⟩
  · gcongr
  · gcongr
  · calc
      _ ≤ (2*(⌊u⌋₊ : ℝ))^(d+1)*(2*(⌊v⌋₊ : ℝ))^(2*d-2) := by gcongr
      _ = (2 : ℝ)^((d+1)+(2*d-2))*((⌊u⌋₊ : ℝ)^(d+1)*(⌊v⌋₊ : ℝ)^(2*d-2)) := by
        simp only [mul_pow,pow_add]
        ring
      _ = _ := by rw [show (d+1)+(2*d-2)=3*d-1 by omega]

/-- The middle regime with natural budgets. Positive real scale equations
are rounded down, while a factor two reserves all outer vertices. -/
theorem middle_parameters {d M N Q : ℕ} (hd : 3 ≤ d) (hM : 0 < M)
    (hMN : 4*M ≤ N) {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hA : u^(d+1)*v^d=(N : ℝ)/(2*M*(d : ℝ)^d))
    (hB : u^d*v^(2*d-2)=(Q : ℝ)/(d : ℝ)^d) :
    ∃ ell b : ℕ, 0 < ell ∧ 0 < b ∧
      (d*ell*b)^d*b^(d-2) ≤ Q ∧
      2*M+M*ell*(d*ell*b)^d ≤ N ∧
      (M : ℝ)*Q*u ≤ (2 : ℝ)^(3*d-1)*
        ((M*(d*ell*b)^d*b^(d-2)*(ell+1) : ℕ) : ℝ) := by
  obtain ⟨ell,b,hell,hb,hvert,hport,hedge⟩ := rounded_scales hd hu hv
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hM0 : (0 : ℝ)<M := by exact_mod_cast hM
  have hden : (d : ℝ)^d ≠ 0 := by positivity
  have hp : (d*ell*b)^d*b^(d-2) ≤ Q := by
    rw [port_count_identity _ _ _ (by omega)]
    have hh := mul_le_mul_of_nonneg_left hport (by positivity : (0 : ℝ)≤(d : ℝ)^d)
    rw [hB,mul_div_cancel₀ _ hden] at hh
    have hh' : d^d*(ell^d*b^(2*d-2)) ≤ Q := by exact_mod_cast hh
    simpa only [mul_assoc] using hh'
  have hn : 2*M+M*ell*(d*ell*b)^d ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hvert
      (by positivity : (0 : ℝ)≤2*M*(d : ℝ)^d)
    rw [hA,mul_div_cancel₀ _ (by positivity : (2*(M : ℝ)*(d : ℝ)^d)≠0)] at hh
    have hh0 : 2*M*d^d*(ell^(d+1)*b^d) ≤ N := by exact_mod_cast hh
    have hh' : 2*M*(d^d*ell^(d+1)*b^d) ≤ N := by simpa only [mul_assoc] using hh0
    rw [← vertex_count_identity] at hh'
    have htwice : 2*(M*ell*(d*ell*b)^d) ≤ N := by simpa only [mul_assoc] using hh'
    omega
  refine ⟨ell,b,hell,hb,hp,hn,?_⟩
  have heq : (M : ℝ)*Q*u=(M : ℝ)*(d : ℝ)^d*(u^(d+1)*v^(2*d-2)) := by
    have hh := (eq_div_iff hden).mp hB
    rw [← hh,pow_succ]
    ring
  rw [heq]
  calc
    _ ≤ (M : ℝ)*(d : ℝ)^d*((2 : ℝ)^(3*d-1)*
          ((ell : ℝ)^(d+1)*(b : ℝ)^(2*d-2))) :=
      mul_le_mul_of_nonneg_left hedge (by positivity)
    _ = (2 : ℝ)^(3*d-1)*((M*(d*ell*b)^d*b^(d-2)*ell : ℕ) : ℝ) := by
      rw [mul_assoc M ((d*ell*b)^d) (b^(d-2)),port_count_identity _ _ _ (by omega)]
      push_cast
      rw [pow_succ]
      ring
    _ ≤ _ := by gcongr; omega

end LinearDistancePreservers.SphereScales


namespace LinearDistancePreservers.SphereScales
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- All three real-scale regimes have actual exact-size graph witnesses.
The only supplied equations are the two numerical ideal-scale identities. -/
theorem capacity_of_ideal_scales {d M R Q N T : ℕ}
    (hd : 3 ≤ d) (hM : 0 < M) (hQM : Q ≤ M) (hR : 3*R ≤ M)
    (hcap : Q ≤ rothNumberNat R) (hMN : 4*M ≤ N)
    (hT : 2*M ≤ T) (hTN : T ≤ N) {u v : ℝ} (hu0 : 0 < u) (hv0 : 0 < v)
    (hA : u^(d+1)*v^d=(N : ℝ)/(2*M*(d : ℝ)^d))
    (hB : u^d*v^(2*d-2)=(Q : ℝ)/(d : ℝ)^d) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t=G.edist s t) →
        (M : ℝ)*Q*u ≤ (2 : ℝ)^(3*d-1)*(H.edgeFinset.card : ℝ) := by
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hM0 : (0 : ℝ)<M := by exact_mod_cast hM
  have hF : (1 : ℝ)≤2^(3*d-1) := one_le_pow₀ (by norm_num)
  by_cases hu : 1 ≤ u
  · by_cases hv : 1 ≤ v
    · obtain ⟨ell,b,hell,hb,hport,hvert,hedge⟩ := middle_parameters hd hM hMN hu hv hA hB
      obtain ⟨G,S,hS,hE⟩ := graph_lower_bound hd hb hell hM hR
        (hport.trans hcap) hvert hT hTN
      refine ⟨G,S,hS,?_⟩
      intro H hH hp
      rw [hE H hH hp]
      exact hedge
    · obtain ⟨G,S,hS,hE⟩ := UnweightedPath.path_lower_bound (by omega) hTN
      refine ⟨G,S,hS,?_⟩
      intro H hH hp
      rw [hE H hH hp]
      have hQeq : (Q : ℝ)=(d : ℝ)^d*(u^d*v^(2*d-2)) := by
        have hh := (eq_div_iff (by positivity : (d : ℝ)^d≠0)).mp hB
        simpa only [mul_comm] using hh.symm
      have hNeq : (N : ℝ)/2=(M : ℝ)*(d : ℝ)^d*(u^(d+1)*v^d) := by
        have hh := (eq_div_iff (by positivity : (2*(M : ℝ)*(d : ℝ)^d)≠0)).mp hA
        nlinarith only [hh]
      have he : (M : ℝ)*Q*u=((N : ℝ)/2)*v^(d-2) := by
        rw [hQeq,hNeq,pow_succ,show 2*d-2=d+(d-2) by omega,pow_add]
        ring
      have hvp : v^(d-2) ≤ 1 := pow_le_one₀ hv0.le (by linarith)
      have hN2 : (2 : ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
      have hpath : (N : ℝ)/2 ≤ (N-1 : ℕ) := by
        rw [Nat.cast_sub (show 1≤N by omega)]
        norm_num
        linarith
      calc
        _ = ((N : ℝ)/2)*v^(d-2) := he
        _ ≤ (N : ℝ)/2 := by simpa using mul_le_mul_of_nonneg_left hvp (by positivity : (0 : ℝ)≤N/2)
        _ ≤ (N-1 : ℕ) := hpath
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hF
  · obtain ⟨G,S,hS,hE⟩ := UnweightedClique.clique_lower_bound (by omega) hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    rw [hE H hH hp]
    have hMM : (M : ℝ)*Q ≤ (M : ℝ)^2 := by
      have hh : (Q : ℝ)≤M := by exact_mod_cast hQM
      nlinarith only [mul_le_mul_of_nonneg_left hh hM0.le]
    have hc : (M : ℝ)^2 ≤ (T.choose 2 : ℕ) := by
      exact_mod_cast TheoremFourPlanar.square_le_choose hM hT
    calc
      _ ≤ (M : ℝ)*Q := by
        simpa using mul_le_mul_of_nonneg_left (show u≤1 by linarith) (by positivity : (0 : ℝ)≤(M : ℝ)*Q)
      _ ≤ (M : ℝ)^2 := hMM
      _ ≤ (T.choose 2 : ℕ) := hc
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hF

end LinearDistancePreservers.SphereScales

