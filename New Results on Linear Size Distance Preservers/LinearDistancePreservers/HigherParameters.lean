import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-! Complete integer parameter selection for the sharp general-dimensional
product. Path, clique, and middle regimes cover all prescribed sizes.
This arithmetic module assumes no direction-family or geometric theorem. -/
namespace LinearDistancePreservers.HigherParameters

/-- The two integer root scales used in every dimension. -/
theorem root_scales {N M Q c d : ℕ} (hM : 0 < M) (hc : 0 < c) (hd : 0 < d) :
    ∃ u v : ℕ, (c^d+2)*M*u^(d*(d+1)) ≤ N ∧
      N < (c^d+2)*M*(u+1)^(d*(d+1)) ∧
      c^d*v^(d^2) ≤ Q ∧ Q < c^d*(v+1)^(d^2) := by
  let u := Nat.nthRoot (d*(d+1)) (N/((c^d+2)*M))
  let v := Nat.nthRoot (d^2) (Q/(c^d))
  have hd0 : d*(d+1) ≠ 0 := by positivity
  have hds : d^2 ≠ 0 := by positivity
  have hu : u^(d*(d+1)) ≤ N/((c^d+2)*M) := Nat.pow_nthRoot_le (Or.inl hd0)
  have hu' : N/((c^d+2)*M) < (u+1)^(d*(d+1)) := Nat.lt_pow_nthRoot_add_one hd0 _
  have hv : v^(d^2) ≤ Q/(c^d) := Nat.pow_nthRoot_le (Or.inl hds)
  have hv' : Q/(c^d) < (v+1)^(d^2) := Nat.lt_pow_nthRoot_add_one hds _
  have hden : 0 < (c^d+2)*M := by positivity
  have hc' : 0 < c^d := by positivity
  refine ⟨u,v,?_,?_,?_,?_⟩
  · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hden).mp hu
  · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hden).mp hu'
  · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hc').mp hv
  · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hc').mp hv'

theorem port_identity (c t b d : ℕ) (hd : 1 ≤ d) :
    (c*t^d*b^(d+1))^d*b^(d*(d-1)) = c^d*(t*b)^ (d^2)*b^(d^2) := by
  have he : (d+1)*d+d*(d-1)=d^2+d^2 := by
    have := Nat.sub_add_cancel hd
    nlinarith
  simp only [mul_pow, ← pow_mul]
  calc
    c^d*t^(d*d)*b^((d+1)*d)*b^(d*(d-1)) =
      c^d*t^(d*d)*(b^((d+1)*d)*b^(d*(d-1))) := by ring
    _ = c^d*t^(d*d)*b^(d^2+d^2) := by rw [← pow_add,he]
    _ = _ := by rw [pow_add]; simp [pow_two,mul_assoc]


theorem vertex_identity (c t b d : ℕ) :
    t^d*(c*t^d*b^(d+1))^d = c^d*(t*b)^(d*(d+1)) := by
  simp only [mul_pow, ← pow_mul]
  calc
    t^d*(c^d*t^(d*d)*b^((d+1)*d)) =
      c^d*(t^d*t^(d*d))*b^((d+1)*d) := by ring
    _ = c^d*t^(d*(d+1))*b^((d+1)*d) := by rw [← pow_add]; congr 2; ring
    _ = _ := by rw [Nat.mul_comm (d+1) d]; ring

/-- Integer scales in the middle regime, with a dimension-dependent
rounding factor. Geometry is not assumed in this arithmetic theorem. -/
theorem middle_parameters {N M Q u v c d : ℕ}
    (hc : 0 < c) (hd : 1 ≤ d) (hu : 0 < u) (huv : u ≤ v) (hvu : v ≤ u^2)
    (hN : (c^d+2)*M*u^(d*(d+1)) ≤ N) (hQ : c^d*v^(d^2) ≤ Q) :
    ∃ b n k : ℕ, 0 < b ∧ 0 < n ∧
      (k+1)*(c*b^(d+1)) ≤ n ∧ n^d*b^(d*(d-1)) ≤ Q ∧
      2*M+M*(k+1)*n^d ≤ N ∧
      M*u^(2*d)*v^(d*(d-1)) ≤ 2^(2*d^2)*(M*n^d*b^(d*(d-1))*(k+2)) := by
  let b := v/u
  have hb : 0 < b := by
    have : 1 ≤ b := (Nat.le_div_iff_mul_le hu).mpr (by simpa using huv)
    omega
  have hub : u*b ≤ v := by simpa [b,Nat.mul_comm] using Nat.div_mul_le_self v u
  have hvb : v ≤ 2*u*b := by
    have hh := Nat.lt_mul_div_succ v hu
    change v < u*(b+1) at hh
    have hh' := Nat.mul_le_mul_left u hb
    nlinarith only [hh,hh']
  have hbu : b ≤ u := by
    by_contra h
    have hh := Nat.mul_le_mul_left u (show u+1 ≤ b by omega)
    nlinarith only [hh,hub,hvu,hu]
  let t := u/b
  have ht : 0 < t := by
    have : 1 ≤ t := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hbu)
    omega
  have htb : t*b ≤ u := by simpa [t] using Nat.div_mul_le_self u b
  have hut : u ≤ 2*t*b := by
    have hh := Nat.lt_mul_div_succ u hb
    change u < b*(t+1) at hh
    have hh' := Nat.mul_le_mul_left b ht
    nlinarith only [hh,hh']
  let n := c*t^d*b^(d+1)
  let k := t^d-1
  have htd : 0 < t^d := by positivity
  have hk : k+1 = t^d := by dsimp [k]; omega
  have hn : 0 < n := by dsimp [n]; positivity
  have huD : 1 ≤ u^(d*(d+1)) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hu))
  have hport : n^d*b^(d*(d-1)) ≤ Q := by
    calc
      _ = c^d*(t*b)^(d^2)*b^(d^2) := port_identity c t b d hd
      _ ≤ c^d*u^(d^2)*b^(d^2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htb _))
      _ = c^d*(u*b)^(d^2) := by rw [mul_pow]; ring
      _ ≤ c^d*v^(d^2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hub _)
      _ ≤ Q := hQ
  have hvert : 2*M+M*(k+1)*n^d ≤ N := by
    calc
      _ = 2*M+M*(c^d*(t*b)^(d*(d+1))) := by rw [hk]; dsimp [n]; rw [mul_assoc,vertex_identity]
      _ ≤ 2*M+M*(c^d*u^(d*(d+1))) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htb _))) _
      _ ≤ (c^d+2)*M*u^(d*(d+1)) := by nlinarith only [Nat.mul_le_mul_left (2*M) huD]
      _ ≤ N := hN
  have hexp : 2*d+d*(d-1)=d*(d+1) := by
    have := Nat.sub_add_cancel hd
    nlinarith
  have hexp' : d*(d-1)+d*(d+1)=2*d^2 := by
    have := Nat.sub_add_cancel hd
    nlinarith
  have hbase : M*u^(2*d)*v^(d*(d-1)) ≤ 2^(2*d^2)*(M*t^(d*(d+1))*b^(2*d^2)) := by
    calc
      _ ≤ M*u^(2*d)*(2*u*b)^(d*(d-1)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvb _)
      _ = 2^(d*(d-1))*M*u^(d*(d+1))*b^(d*(d-1)) := by
        simp only [mul_pow]
        calc
          _ = 2^(d*(d-1))*M*(u^(2*d)*u^(d*(d-1)))*b^(d*(d-1)) := by ring
          _ = _ := by rw [← pow_add,hexp]
      _ ≤ 2^(d*(d-1))*M*(2*t*b)^(d*(d+1))*b^(d*(d-1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hut _))
      _ = 2^(2*d^2)*(M*t^(d*(d+1))*b^(2*d^2)) := by
        simp only [mul_pow]
        calc
          _ = (2^(d*(d-1))*2^(d*(d+1)))*M*t^(d*(d+1))*
            (b^(d*(d-1))*b^(d*(d+1))) := by ring
          _ = _ := by rw [← pow_add,← pow_add,hexp']; ring
  have hedge : M*t^(d*(d+1))*b^(2*d^2) ≤ M*n^d*b^(d*(d-1))*(k+2) := by
    have hk' : t^d ≤ k+2 := by omega
    have hc' : 0 < c^d := by positivity
    calc
      _ ≤ c^d*(M*t^(d*(d+1))*b^(2*d^2)) := Nat.le_mul_of_pos_left _ hc'
      _ = M*n^d*b^(d*(d-1))*t^d := by
        have he : n^d*t^d = c^d*(t*b)^(d*(d+1)) := by
          rw [mul_comm]; exact vertex_identity c t b d
        calc
          _ = M*(c^d*(t*b)^(d*(d+1)))*b^(d*(d-1)) := by
            simp only [mul_pow]
            rw [← hexp',pow_add]
            ring
          _ = _ := by rw [← he]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hk'
  refine ⟨b,n,k,hb,hn,?_,hport,hvert,hbase.trans (Nat.mul_le_mul_left _ hedge)⟩
  rw [hk]
  dsimp [n]
  exact le_of_eq (by ring)


theorem upper_scales {N M Q u v c d : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hN : N < (c^d+2)*M*(u+1)^(d*(d+1))) (hQ : Q < c^d*(v+1)^(d^2)) :
    N ≤ ((c^d+2)*2^(d*(d+1)))*M*u^(d*(d+1)) ∧
      Q ≤ (c^d*2^(d^2))*v^(d^2) := by
  have hu' := Nat.pow_le_pow_left (show u+1 ≤ 2*u by omega) (d*(d+1))
  have hv' := Nat.pow_le_pow_left (show v+1 ≤ 2*v by omega) (d^2)
  constructor
  · apply hN.le.trans
    simpa [mul_pow,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left ((c^d+2)*M) hu'
  · apply hQ.le.trans
    simpa [mul_pow,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left (c^d) hv'

theorem exponent_identities {d : ℕ} (hd : 1 ≤ d) :
    d*(d-1)+2*d=d*(d+1) ∧
    d^2*(d^2-1)=(d*(d-1))*(d*(d+1)) ∧
    d^2-1+(d+1)=d*(d+1) := by
  have h1 := Nat.sub_add_cancel hd
  have hd2 : 1 ≤ d^2 := by nlinarith
  have h2 := Nat.sub_add_cancel hd2
  constructor
  · nlinarith
  constructor
  · have hh : d^2-1=(d-1)*(d+1) := by nlinarith
    rw [hh]
    ring
  · nlinarith

theorem product_identity (M CN CQ u v d : ℕ) (hd : 1 ≤ d) :
    M^(d*(d-1))*(CQ*v^(d^2))^(d^2-1)*(CN*M*u^(d*(d+1)))^(2*d) =
      CQ^(d^2-1)*CN^(2*d)*(M*u^(2*d)*v^(d*(d-1)))^(d*(d+1)) := by
  obtain ⟨hm,hv,_⟩ := exponent_identities hd
  simp only [mul_pow, ← pow_mul]
  calc
    _ = CQ^(d^2-1)*CN^(2*d)*(M^(d*(d-1))*M^(2*d))*
      u^((d*(d+1))*(2*d))*v^(d^2*(d^2-1)) := by ring
    _ = _ := by
      rw [← pow_add,hm,hv,Nat.mul_comm (d*(d+1)) (2*d)]
      ring

theorem product_rate {N M Q u v E CN CQ C d : ℕ} (hd : 1 ≤ d)
    (hN : N ≤ CN*M*u^(d*(d+1))) (hQ : Q ≤ CQ*v^(d^2))
    (hE : M*u^(2*d)*v^(d*(d-1)) ≤ C*E) :
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤
      (CQ^(d^2-1)*CN^(2*d)*C^(d*(d+1)))*E^(d*(d+1)) := by
  calc
    _ ≤ M^(d*(d-1))*(CQ*v^(d^2))^(d^2-1)*(CN*M*u^(d*(d+1)))^(2*d) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)) (Nat.pow_le_pow_left hN _)
    _ = CQ^(d^2-1)*CN^(2*d)*(M*u^(2*d)*v^(d*(d-1)))^(d*(d+1)) := product_identity _ _ _ _ _ _ hd
    _ ≤ CQ^(d^2-1)*CN^(2*d)*(C*E)^(d*(d+1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE _)
    _ = _ := by rw [mul_pow]; ring


theorem path_rate {N M Q u v c d : ℕ} (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hlo : (c^d+2)*M*u^(d*(d+1)) ≤ N)
    (hQ : Q < c^d*(v+1)^(d^2)) (hv : v < u) :
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤
      ((c^d)^(d^2-1)*2^(d*(d+1)))*(N-1)^(d*(d+1)) := by
  obtain ⟨hm,he,_⟩ := exponent_identities hd
  have hqu : Q ≤ c^d*u^(d^2) := by
    exact hQ.le.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : v+1 ≤ u) _))
  have hmu : M*u^(d*(d+1)) ≤ N := by
    calc
      _ ≤ (c^d+2)*(M*u^(d*(d+1))) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ N := by simpa [mul_assoc] using hlo
  calc
    _ ≤ M^(d*(d-1))*(c^d*u^(d^2))^(d^2-1)*N^(2*d) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqu _))
    _ = (c^d)^(d^2-1)*(M*u^(d*(d+1)))^(d*(d-1))*N^(2*d) := by
      simp only [mul_pow, ← pow_mul]
      rw [he,Nat.mul_comm (d*(d+1)) (d*(d-1))]
      ring
    _ ≤ (c^d)^(d^2-1)*N^(d*(d-1))*N^(2*d) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmu _))
    _ = (c^d)^(d^2-1)*N^(d*(d+1)) := by rw [mul_assoc,← pow_add,hm]
    _ ≤ (c^d)^(d^2-1)*(2*(N-1))^(d*(d+1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : N ≤ 2*(N-1)) _)
    _ = _ := by rw [mul_pow]; ring

theorem clique_small_scale {N M Q CN d : ℕ} (hd : 1 ≤ d) (hM : 0 < M)
    (hQ : Q ≤ M) (hN : N ≤ CN*M) :
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤ CN^(2*d)*(M^2)^(d*(d+1)) := by
  obtain ⟨hm,_,_⟩ := exponent_identities hd
  have he : d*(d-1)+(d^2-1)+2*d ≤ 2*(d*(d+1)) := by nlinarith [Nat.sub_le (d^2) 1]
  calc
    _ ≤ M^(d*(d-1))*M^(d^2-1)*(CN*M)^(2*d) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)) (Nat.pow_le_pow_left hN _)
    _ = CN^(2*d)*M^(d*(d-1)+(d^2-1)+2*d) := by
      rw [mul_pow,pow_add,pow_add]; ring
    _ ≤ CN^(2*d)*M^(2*(d*(d+1))) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1 ≤ M) he)
    _ = _ := by rw [pow_mul M 2 (d*(d+1))]

theorem clique_rate {N M Q u v c CN d : ℕ} (hc : 0 < c) (hd : 1 ≤ d)
    (hQ : Q ≤ M) (hN : N ≤ CN*M*u^(d*(d+1)))
    (hlo : c^d*v^(d^2) ≤ Q) (hvu : u^2 ≤ v) :
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤ CN^(2*d)*(M^2)^(d*(d+1)) := by
  obtain ⟨hm,_,he⟩ := exponent_identities hd
  have huQ : u^(2*d^2) ≤ Q := by
    calc
      _ = (u^2)^(d^2) := by rw [pow_mul]
      _ ≤ v^(d^2) := Nat.pow_le_pow_left hvu _
      _ ≤ c^d*v^(d^2) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ Q := hlo
  calc
    _ ≤ M^(d*(d-1))*Q^(d^2-1)*(CN*M*u^(d*(d+1)))^(2*d) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN _)
    _ = CN^(2*d)*M^(d*(d+1))*Q^(d^2-1)*(u^(2*d^2))^(d+1) := by
      simp only [mul_pow, ← pow_mul]
      calc
        _ = CN^(2*d)*(M^(d*(d-1))*M^(2*d))*Q^(d^2-1)*u^((d*(d+1))*(2*d)) := by ring
        _ = _ := by rw [← pow_add,hm]; congr 1; congr 1; ring
    _ ≤ CN^(2*d)*M^(d*(d+1))*Q^(d^2-1)*Q^(d+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left huQ _)
    _ = CN^(2*d)*M^(d*(d+1))*Q^(d*(d+1)) := by rw [mul_assoc,← pow_add,he]
    _ ≤ CN^(2*d)*M^(d*(d+1))*M^(d*(d+1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
    _ = _ := by
      rw [mul_assoc,← pow_add,show d*(d+1)+d*(d+1)=2*(d*(d+1)) by omega,pow_mul M 2 (d*(d+1))]


/-- One explicit coefficient covers all four rounding regimes. Its size
is deliberately coarse; it depends only on dimension and the box constant. -/
def factor (c d : ℕ) : ℕ :=
  (c^d+2)^(2*d) + (c^d)^(d^2-1)*2^(d*(d+1)) +
    ((c^d+2)*2^(d*(d+1)))^(2*d) +
    (c^d*2^(d^2))^(d^2-1)*((c^d+2)*2^(d*(d+1)))^(2*d)*
      (2^(2*d^2))^(d*(d+1))

theorem factor_pos (c d : ℕ) : 0 < factor c d := by
  unfold factor
  positivity

/-- Every prescribed size lies in a path, clique, or capacity-fitting
product regime, with no geometry or rounding assumptions. -/
theorem parameters_or_baselines {N M Q c d : ℕ} (hc : 0 < c) (hd : 1 ≤ d)
    (hN : 2 ≤ N) (hM : 0 < M) (hQ : Q ≤ M) :
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤ factor c d*(N-1)^(d*(d+1)) ∨
    M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤ factor c d*(M^2)^(d*(d+1)) ∨
    ∃ b n k : ℕ, 0 < b ∧ 0 < n ∧ (k+1)*(c*b^(d+1)) ≤ n ∧
      n^d*b^(d*(d-1)) ≤ Q ∧ 2*M+M*(k+1)*n^d ≤ N ∧
      M^(d*(d-1))*Q^(d^2-1)*N^(2*d) ≤
        factor c d*(M*n^d*b^(d*(d-1))*(k+2))^(d*(d+1)) := by
  have hsmall : (c^d+2)^(2*d) ≤ factor c d := by unfold factor; omega
  have hpath : (c^d)^(d^2-1)*2^(d*(d+1)) ≤ factor c d := by unfold factor; omega
  have hclique : ((c^d+2)*2^(d*(d+1)))^(2*d) ≤ factor c d := by unfold factor; omega
  have hprod : (c^d*2^(d^2))^(d^2-1)*((c^d+2)*2^(d*(d+1)))^(2*d)*
      (2^(2*d^2))^(d*(d+1)) ≤ factor c d := by unfold factor; omega
  obtain ⟨u,v,huN,hNu,hvQ,hQv⟩ := root_scales (N := N) (Q := Q) hM hc (by omega : 0 < d)
  by_cases hu : u = 0
  · right; left
    subst u
    simp only [Nat.zero_add,one_pow,mul_one] at hNu
    exact (clique_small_scale hd hM hQ hNu.le).trans (Nat.mul_le_mul_right _ hsmall)
  have hup : 0 < u := by omega
  by_cases hvu : v < u
  · exact Or.inl ((path_rate hd hN huN hQv hvu).trans (Nat.mul_le_mul_right _ hpath))
  have huv : u ≤ v := by omega
  obtain ⟨hNup,hQup⟩ := upper_scales hup (by omega) hNu hQv
  by_cases huv2 : u^2 ≤ v
  · exact Or.inr (Or.inl ((clique_rate hc hd hQ hNup hvQ huv2).trans
      (Nat.mul_le_mul_right _ hclique)))
  obtain ⟨b,n,k,hb,hn,hinner,hport,hvert,hedge⟩ :=
    middle_parameters hc hd hup huv (by omega) huN hvQ
  exact Or.inr (Or.inr ⟨b,n,k,hb,hn,hinner,hport,hvert,
    (product_rate hd hNup hQup hedge).trans (Nat.mul_le_mul_right _ hprod)⟩)

end LinearDistancePreservers.HigherParameters
