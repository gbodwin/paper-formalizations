import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integer parameter selection for the sharp planar product. Sixth- and
fourth-root scales separate the path, clique, and capacity-fitting regimes. -/
namespace LinearDistancePreservers.PlanarParameters

theorem root_scales {N M Q : ℕ} (hM : 0 < M) :
    ∃ u v : ℕ, 83*M*u^6 ≤ N ∧ N < 83*M*(u+1)^6 ∧
      81*v^4 ≤ Q ∧ Q < 81*(v+1)^4 := by
  let u := Nat.nthRoot 6 (N/(83*M))
  let v := Nat.nthRoot 4 (Q/81)
  have hu : u^6 ≤ N/(83*M) := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hu' : N/(83*M) < (u+1)^6 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hv : v^4 ≤ Q/81 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hv' : Q/81 < (v+1)^4 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hden : 0 < 83*M := by positivity
  refine ⟨u,v,?_,?_,?_,?_⟩
  · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hden).mp hu
  · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hden).mp hu'
  · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0 < 81)).mp hv
  · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (by decide : 0 < 81)).mp hv'

/-- Capacity-fitting parameters with a coarse but absolute rounding loss. -/
theorem middle_parameters {N M Q u v : ℕ}
    (hu : 0 < u) (huv : u ≤ v) (hvu : v ≤ u^2)
    (hN : 83*M*u^6 ≤ N) (hQ : 81*v^4 ≤ Q) :
    ∃ B x n k : ℕ, 0 < n ∧ 4*x ≤ B^2 ∧ (k+1)*(B^3+1) ≤ n ∧
      n^2*x ≤ Q ∧ 2*M+M*(k+1)*n^2 ≤ N ∧
      M*u^4*v^2 ≤ 256*(M*n^2*x*(k+2)) := by
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
  let n := 9*t^2*b^3
  let k := t^2-1
  have ht2 : 0 < t^2 := by positivity
  have hk : k+1 = t^2 := by
    dsimp [k]
    omega
  have hn : 0 < n := by dsimp [n]; positivity
  have hb3 : 1 ≤ b^3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hb))
  have hu6 : 1 ≤ u^6 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hu))
  have hport : n^2*b^2 ≤ Q := by
    calc
      _ = 81*(t*b)^4*b^4 := by dsimp [n]; ring
      _ ≤ 81*u^4*b^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htb 4))
      _ = 81*(u*b)^4 := by ring
      _ ≤ 81*v^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hub 4)
      _ ≤ Q := hQ
  have hvert : 2*M+M*(k+1)*n^2 ≤ N := by
    calc
      _ = 2*M+81*M*(t*b)^6 := by rw [hk]; dsimp [n]; ring
      _ ≤ 2*M+81*M*u^6 := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htb 6)) _
      _ ≤ 83*M*u^6 := by nlinarith only [Nat.mul_le_mul_left (2*M) hu6]
      _ ≤ N := hN
  have hbase : M*u^4*v^2 ≤ 256*(M*t^6*b^8) := by
    calc
      _ ≤ M*u^4*(2*u*b)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvb 2)
      _ = 4*M*u^6*b^2 := by ring
      _ ≤ 4*M*(2*t*b)^6*b^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hut 6))
      _ = _ := by ring
  have hedge : M*t^6*b^8 ≤ M*n^2*b^2*(k+2) := by
    have hk' : t^2 ≤ k+2 := by omega
    calc
      _ ≤ 81*(M*t^6*b^8) := Nat.le_mul_of_pos_left _ (by decide)
      _ = M*n^2*b^2*t^2 := by dsimp [n]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hk'
  refine ⟨2*b,b^2,n,k,hn,?_,?_,hport,hvert,hbase.trans (Nat.mul_le_mul_left _ hedge)⟩
  · nlinarith only []
  · rw [hk]
    dsimp [n]
    have hh : (2*b)^3+1 ≤ 9*b^3 := by nlinarith only [hb3]
    simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left (t^2) hh

theorem upper_scales {N M Q u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hN : N < 83*M*(u+1)^6) (hQ : Q < 81*(v+1)^4) :
    N ≤ 8192*M*u^6 ∧ Q ≤ 2048*v^4 := by
  have hu' := Nat.pow_le_pow_left (show u+1 ≤ 2*u by omega) 6
  have hv' := Nat.pow_le_pow_left (show v+1 ≤ 2*v by omega) 4
  constructor
  · have hh := Nat.mul_le_mul_left (83*M) hu'
    nlinarith only [hN,hh,Nat.zero_le (M*u^6)]
  · have hh := Nat.mul_le_mul_left 81 hv'
    nlinarith only [hQ,hh,Nat.zero_le (v^4)]

theorem path_rate {N M Q u v : ℕ} (hN : 2 ≤ N)
    (hlo : 83*M*u^6 ≤ N) (hQ : Q < 81*(v+1)^4) (hv : v < u) :
    M^2*Q^3*N^4 ≤ 16777216^6*(N-1)^6 := by
  have hqu : Q ≤ 81*u^4 := by
    have hh := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left (show v+1 ≤ u by omega) 4)
    omega
  have hmu : M*u^6 ≤ N := by nlinarith only [hlo,Nat.zero_le (M*u^6)]
  calc
    _ ≤ M^2*(81*u^4)^3*N^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqu 3))
    _ = 81^3*(M*u^6)^2*N^4 := by ring
    _ ≤ 81^3*N^2*N^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmu 2))
    _ = 81^3*N^6 := by ring
    _ ≤ 81^3*(2*(N-1))^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
    _ ≤ _ := by ring_nf; omega

theorem clique_small_scale {N M Q : ℕ} (hM : 0 < M)
    (hQ : Q ≤ M) (hN : N ≤ 83*M) :
    M^2*Q^3*N^4 ≤ 16777216^6*(M^2)^6 := by
  have hM3 : 1 ≤ M^3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hM))
  calc
    _ ≤ M^2*M^3*(83*M)^4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 3)) (Nat.pow_le_pow_left hN 4)
    _ = 83^4*M^9 := by ring
    _ ≤ 83^4*M^9*M^3 := Nat.le_mul_of_pos_right _ hM3
    _ ≤ _ := by ring_nf; omega

theorem clique_rate {N M Q u v : ℕ} (hQ : Q ≤ M)
    (hN : N ≤ 8192*M*u^6) (hlo : 81*v^4 ≤ Q) (hvu : u^2 ≤ v) :
    M^2*Q^3*N^4 ≤ 16777216^6*(M^2)^6 := by
  have huQ : u^8 ≤ Q := by
    have hh := Nat.pow_le_pow_left hvu 4
    have hh' : v^4 ≤ Q := by nlinarith only [hlo,Nat.zero_le (v^4)]
    calc
      _ = (u^2)^4 := by ring
      _ ≤ v^4 := hh
      _ ≤ Q := hh'
  calc
    _ ≤ M^2*Q^3*(8192*M*u^6)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 4)
    _ = 8192^4*M^6*Q^3*(u^8)^3 := by ring
    _ ≤ 8192^4*M^6*Q^3*Q^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left huQ 3)
    _ = 8192^4*M^6*Q^6 := by ring
    _ ≤ 8192^4*M^6*M^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 6)
    _ ≤ _ := by ring_nf; omega

theorem product_rate {N M Q u v E : ℕ}
    (hN : N ≤ 8192*M*u^6) (hQ : Q ≤ 2048*v^4)
    (hE : M*u^4*v^2 ≤ 256*E) :
    M^2*Q^3*N^4 ≤ 16777216^6*E^6 := by
  calc
    _ ≤ M^2*(2048*v^4)^3*(8192*M*u^6)^4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 3)) (Nat.pow_le_pow_left hN 4)
    _ = (2048^3*8192^4)*(M*u^4*v^2)^6 := by ring
    _ ≤ (2048^3*8192^4)*(256*E)^6 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 6)
    _ ≤ _ := by ring_nf; omega

/-- All prescribed sizes fall into a path, clique, or legal product regime. -/
theorem parameters_or_baselines {N M Q : ℕ} (hN : 2 ≤ N) (hM : 0 < M)
    (hQ : Q ≤ M) :
    M^2*Q^3*N^4 ≤ 16777216^6*(N-1)^6 ∨
    M^2*Q^3*N^4 ≤ 16777216^6*(M^2)^6 ∨
    ∃ B x n k : ℕ, 0 < n ∧ 4*x ≤ B^2 ∧ (k+1)*(B^3+1) ≤ n ∧
      n^2*x ≤ Q ∧ 2*M+M*(k+1)*n^2 ≤ N ∧
      M^2*Q^3*N^4 ≤ 16777216^6*(M*n^2*x*(k+2))^6 := by
  obtain ⟨u,v,huN,hNu,hvQ,hQv⟩ := root_scales (N := N) (Q := Q) hM
  by_cases hu : u = 0
  · right; left
    subst u
    norm_num at hNu
    exact clique_small_scale hM hQ hNu.le
  have hup : 0 < u := by omega
  by_cases hvu : v < u
  · exact Or.inl (path_rate hN huN hQv hvu)
  have huv : u ≤ v := by omega
  obtain ⟨hNup,hQup⟩ := upper_scales hup (by omega) hNu hQv
  by_cases huv2 : u^2 ≤ v
  · exact Or.inr (Or.inl (clique_rate hQ hNup hvQ huv2))
  obtain ⟨B,x,n,k,hn,hx,hinner,hport,hvert,hedge⟩ :=
    middle_parameters hup huv (by omega) huN hvQ
  exact Or.inr (Or.inr ⟨B,x,n,k,hn,hx,hinner,hport,hvert,product_rate hNup hQup hedge⟩)

end LinearDistancePreservers.PlanarParameters
