import LightSpanners.EndpointSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

include C

/-- Averaging the actual medium-counting inequality over all independently
retained chord sets gives the exact sampling lower bound. -/
theorem sampled_counting_lower (U : Finset (Sym2 V))
    (hU : ∀ e∈U,e∈G.edgeSet ∧ e∉C.cycle.edges)
    {eps p : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k) (hp0 : 0≤p) (hp1 : p≤1)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    eps/4*(p*∑ e∈U,w e)-(Fintype.card V:ℝ)≤
      p^k*(C.safeEndpoints eps k U).card := by
  have hbound := Finset.sum_le_sum (s := U.powerset) (fun S hS =>
    mul_le_mul_of_nonneg_left (C.medium_counting S
      (fun e he => hU e (Finset.mem_powerset.mp hS he)) heps hk hG)
      (FiniteSampling.mass_nonneg U S hp0 hp1))
  rw [C.expected_endpoint_count U p heps hk hG] at hbound
  have hsum : (∑ S∈U.powerset, FiniteSampling.mass U p S*
      (eps/4*(∑ e∈S,w e)-(Fintype.card V:ℝ))) =
      eps/4*(p*∑ e∈U,w e)-(Fintype.card V:ℝ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have heq : (∑ S∈U.powerset, FiniteSampling.mass U p S*(eps/4*(∑ e∈S,w e))) =
        eps/4*∑ S∈U.powerset, FiniteSampling.mass U p S*(∑ e∈S,w e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    rw [heq,FiniteSampling.expected_sum,← Finset.sum_mul,FiniteSampling.sum_mass,one_mul]
  rwa [hsum] at hbound

/-- Source-threshold full counting: density at least 5/epsilon yields the
actual endpoint-family count n/4 times the kth power of epsilon*d/5. -/
theorem full_counting (U : Finset (Sym2 V))
    (hU : ∀ e∈U,e∈G.edgeSet ∧ e∉C.cycle.edges)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (hweight : 5/eps*(Fintype.card V:ℝ)≤∑ e∈U,w e) :
    (Fintype.card V:ℝ)/4*(eps*(∑ e∈U,w e)/(5*Fintype.card V))^k≤
      (C.safeEndpoints eps k U).card := by
  let n : ℝ := Fintype.card V
  let W := ∑ e∈U,w e
  have hn : 0<n := by
    have hh := C.three_le_card
    dsimp [n]
    exact_mod_cast (show 0<Fintype.card V by omega)
  have hW : 0<W := (by positivity : 0<5/eps*n).trans_le hweight
  let p := 5*n/(eps*W)
  have hp : 0<p := by dsimp [p]; positivity
  have hp1 : p≤1 := by
    apply (div_le_one (by positivity : 0<eps*W)).mpr
    have hh := mul_le_mul_of_nonneg_left hweight heps.le
    have he : eps*(5/eps*n)=5*n := by field_simp
    rw [he] at hh
    linarith
  have hlower := C.sampled_counting_lower U hU heps hk hp.le hp1 hG
  have hexact : eps/4*(p*W)-n=n/4 := by dsimp [p]; field_simp <;> ring
  change eps/4*(p*W)-n≤p^k*(C.safeEndpoints eps k U).card at hlower
  rw [hexact] at hlower
  have hinv : eps*W/(5*n)=p⁻¹ := by dsimp [p]; field_simp <;> ring
  change n/4*(eps*W/(5*n))^k≤_
  rw [hinv,inv_pow,← div_eq_mul_inv]
  exact (div_le_iff₀ (pow_pos hp k)).mpr (by simpa [mul_comm] using hlower)

/-- Finite-uniform form of Theorem 5.1, retaining the indispensable unit-cycle
weight n for unrestricted positive epsilon. -/
theorem unit_cycle_weight_bound {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    totalWeight G w≤(Fintype.card V:ℝ)+
      8/eps*(Fintype.card V:ℝ)*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  let U := G.edgeFinset.filter (fun e => e∉C.cycle.edges)
  let W := ∑ e∈U,w e
  let n : ℝ := Fintype.card V
  have hU : ∀ e∈U,e∈G.edgeSet ∧ e∉C.cycle.edges := by simp [U]
  have hW : W=totalWeight G w-n := C.noncycle_weight
  have hnNat : 3≤Fintype.card V := C.three_le_card
  have hn : 0<n := by dsimp [n]; exact_mod_cast (show 0<Fintype.card V by omega)
  have hn1 : 1≤n := by dsimp [n]; exact_mod_cast (show 1≤Fintype.card V by omega)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hroot : 1≤n^((k:ℝ)⁻¹) := Real.one_le_rpow hn1 (by positivity)
  by_cases hlarge : 8/eps*n≤W
  · have hW0 : 0<W := (by positivity : 0<8/eps*n).trans_le hlarge
    let p := 8*n/(eps*W)
    have hp0 : 0<p := by dsimp [p]; positivity
    have hp1 : p≤1 := by
      apply (div_le_one (by positivity : 0<eps*W)).mpr
      have hh := mul_le_mul_of_nonneg_left hlarge heps.le
      have he : eps*(8/eps*n)=8*n := by field_simp
      rw [he] at hh
      linarith
    have hlower := C.sampled_counting_lower U hU heps hk hp0.le hp1 hG
    have hexact : eps/4*(p*W)-n=n := by dsimp [p]; field_simp <;> ring
    change eps/4*(p*W)-n≤p^k*(C.safeEndpoints eps k U).card at hlower
    rw [hexact] at hlower
    have hcard : ((C.safeEndpoints eps k U).card:ℝ)≤n*n := by
      have hh := Finset.card_le_univ (C.safeEndpoints eps k U)
      simpa [n,Fintype.card_prod] using (show ((C.safeEndpoints eps k U).card:ℝ)≤Fintype.card (V×V) by exact_mod_cast hh)
    have hb : n≤p^k*(n*n) := hlower.trans (mul_le_mul_of_nonneg_left hcard (pow_nonneg hp0.le k))
    have hnorm : 1≤n*p^k := (mul_le_mul_iff_right₀ hn).mp (by nlinarith [hb])
    have hinv : p⁻¹≤n^((k:ℝ)⁻¹) := by
      apply (Real.le_rpow_inv_iff_of_pos (by positivity) hn.le hkR).mpr
      rw [Real.rpow_natCast,inv_pow,inv_eq_one_div]
      apply (div_le_iff₀ (pow_pos hp0 k)).mpr
      exact hnorm
    have hwid : W=(8/eps*n)*p⁻¹ := by dsimp [p]; field_simp <;> ring
    have hwle : W≤8/eps*n*n^((k:ℝ)⁻¹) := by
      rw [hwid]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    linarith [hW]
  · have hwsmall := le_of_lt (lt_of_not_ge hlarge)
    have hh := mul_le_mul_of_nonneg_left hroot (by positivity : 0≤8/eps*n)
    linarith [hW]

/-- The usual finite-uniform display follows in the standard small-epsilon
range, with an explicit universal constant. -/
theorem unit_cycle_weight_bound_small_epsilon {eps : ℝ} {k : ℕ}
    (heps : 0<eps) (heps1 : eps≤1) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    totalWeight G w≤9/eps*(Fintype.card V:ℝ)^(1+1/(k:ℝ)) := by
  let n : ℝ := Fintype.card V
  have hnNat := C.three_le_card
  have hn : 0<n := by dsimp [n]; exact_mod_cast (show 0<Fintype.card V by omega)
  have hn1 : 1≤n := by dsimp [n]; exact_mod_cast (show 1≤Fintype.card V by omega)
  have hroot := Real.one_le_rpow hn1 (show (0:ℝ)≤(k:ℝ)⁻¹ by positivity)
  have hb := C.unit_cycle_weight_bound heps hk hG
  have hinv : 1≤1/eps := (le_div_iff₀ heps).mpr (by linarith)
  have hbaseline : n≤1/eps*n*n^((k:ℝ)⁻¹) := by
    have h1 := mul_le_mul_of_nonneg_right hinv hn.le
    have h2 := mul_le_mul_of_nonneg_left hroot (by positivity : 0≤1/eps*n)
    nlinarith
  have heq : n^(1+1/(k:ℝ))=n*n^((k:ℝ)⁻¹) := by
    rw [Real.rpow_add hn,Real.rpow_one,one_div]
  change totalWeight G w≤9/eps*n^(1+1/(k:ℝ))
  rw [heq]
  change totalWeight G w≤n+8/eps*n*n^((k:ℝ)⁻¹) at hb
  calc
    _ ≤ n+8/eps*n*n^((k:ℝ)⁻¹) := hb
    _ ≤ 1/eps*n*n^((k:ℝ)⁻¹)+8/eps*n*n^((k:ℝ)⁻¹) := add_le_add hbaseline le_rfl
    _ = _ := by ring

end LightSpanners.UnitSpanningCycle
