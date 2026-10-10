import LightSpanners.MediumCounting
import LightSpanners.FiniteSampling

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Dispersion identifies exactly which sampled chord sets retain a fixed
endpoint pair. Claim 3 makes the survival exponent the actual chord count k. -/
theorem endpoint_survival (U : Finset (Sym2 V)) (a : V×V) (p : ℝ)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    (∑ S ∈ U.powerset, FiniteSampling.mass U p S *
      (if a∈C.safeEndpoints eps k S then 1 else 0)) =
    p^k*(if a∈C.safeEndpoints eps k U then 1 else 0) := by
  by_cases ha : a∈C.safeEndpoints eps k U
  · obtain ⟨q,hq,hqU⟩ := C.mem_safeEndpoints.mp ha
    let R := (C.chordEdges q).toFinset
    have hRU : R⊆U := fun e he => hqU e (List.mem_toFinset.mp he)
    have hRcard : R.card=k := by
      change (C.chordEdges q).toFinset.card=k
      rw [List.toFinset_card_of_nodup (hq.chordEdges_nodup C heps hk hG)]
      exact hq.1
    have hiff (S : Finset (Sym2 V)) : a∈C.safeEndpoints eps k S ↔ R⊆S := by
      constructor
      · intro hS
        obtain ⟨r,hr,hrS⟩ := C.mem_safeEndpoints.mp hS
        have heq := hq.unique C hr heps hk hG
        intro e he
        apply hrS e
        rw [← heq]
        exact List.mem_toFinset.mp he
      · intro hS
        exact C.mem_safeEndpoints.mpr ⟨q,hq,fun e he => hS (List.mem_toFinset.mpr he)⟩
    simp only [ha,if_true,mul_one]
    simp_rw [hiff,mul_ite,mul_one,mul_zero]
    rw [← Finset.sum_filter,FiniteSampling.sum_mass_containing U R p hRU,hRcard]
  · rw [if_neg ha,mul_zero]
    apply Finset.sum_eq_zero
    intro S hS
    have hn : a∉C.safeEndpoints eps k S :=
      fun hs => ha (C.safeEndpoints_mono (Finset.mem_powerset.mp hS) hs)
    simp [hn]

/-- Exact finite expected endpoint count; the ambient endpoint set is at most
n², and each actual k-chord word survives independently with mass p^k. -/
theorem expected_endpoint_count (U : Finset (Sym2 V)) (p : ℝ)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    (∑ S ∈ U.powerset, FiniteSampling.mass U p S *
      ((C.safeEndpoints eps k S).card:ℝ)) =
    p^k*(C.safeEndpoints eps k U).card := by
  have hcard (S : Finset (Sym2 V)) : ((C.safeEndpoints eps k S).card:ℝ)=
      ∑ a : V×V, if a∈C.safeEndpoints eps k S then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [safeEndpoints]
  simp_rw [hcard,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact C.endpoint_survival U a p heps hk hG

end LightSpanners.UnitSpanningCycle
