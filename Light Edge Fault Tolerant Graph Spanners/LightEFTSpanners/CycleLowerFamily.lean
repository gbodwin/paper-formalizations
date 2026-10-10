import LightEFTSpanners.CycleCompetitiveLower
import LightEFTSpanners.FaultBudgetSaturation

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

/-- The vertex count is independent of the chosen finite enumeration. -/
theorem cycle_vertex_card_at (m f : ℕ)
    (i : Fintype (Vertex (I:=Fin f) (cycleGraph (m+3)))) :
    @Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3))) i=(m+3)+(m+3)*f := by
  rw [← Nat.card_eq_fintype_card]
  simpa only [← Nat.card_eq_fintype_card] using cycle_vertex_count m f

/-- An explicit infinite-in-m family with a genuine optimal denominator.
For fixed positive f,k, all m with 2k≤m+2 are allowed. -/
theorem cycle_lower_family (m f k q : ℕ) (hf : 0<f) (hk : 0<k) (hq : q≤2*f-1)
    (hm : 2*k≤m+2) :
    ∃ Q : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
      IsMinimumFTPreserver
        (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
        Q (coreWeight (cycleGraph (m+3)) ((m+2)/k)) q ∧
      ∀ H : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
        IsEFTSpanner
          (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
          H (coreWeight (cycleGraph (m+3)) ((m+2)/k)) k f →
        (m+2:ℝ)/(2*f*k) ≤
          competitiveLightness H Q (coreWeight (cycleGraph (m+3)) ((m+2)/k)) := by
  classical
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hW : (2:ℝ)≤(m+2)/k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast hm
  have hmul : (k:ℝ)*((m+2)/k)=m+2 := by field_simp [hkR.ne']
  have hgap : (k:ℝ)*((m+2)/k)<2*(m+2) := by
    rw [hmul]
    have hmR : (0:ℝ)<m+2 := by positivity
    linarith
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver
    (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
    (coreWeight (cycleGraph (m+3)) ((m+2)/k)) q
  refine ⟨Q,hQ,fun H hH => ?_⟩
  have hh := cycle_competitive_lower m f q hf hq ((m+2)/k) k hW hgap hH hQ
  simpa only [div_div,mul_comm (k:ℝ) (2*(f:ℝ))] using hh
/-- Eligibility is nonvacuous: the input itself is an actual EFT k-spanner. -/
theorem cycle_input_self_spanner (m f k : ℕ) (hk : 0<k) :
    IsEFTSpanner
      (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      (coreWeight (cycleGraph (m+3)) ((m+2)/k)) k f := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  apply self_eftSpanner
  · intro e
    exact (coreWeight_positive (cycleGraph (m+3)) (by positivity) e).le
  · exact_mod_cast (Nat.succ_le_iff.mpr hk)

/-- Relate the explicit finite lower ratio to the actual number of vertices.
The constant is uniform in all positive integer f,k and every core size. -/
theorem cycle_lower_ratio_in_vertices (m f k : ℕ) (hf : 0<f) (hk : 0<k) :
    ((m+3)+(m+3)*f:ℝ)/(8*(f:ℝ)^2*k)≤(m+2:ℝ)/(2*f*k) := by
  have hfR : (1:ℝ)≤f := by exact_mod_cast (Nat.succ_le_iff.mpr hf)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hmR : (0:ℝ)≤m := Nat.cast_nonneg m
  have hfpos : (0:ℝ)<f := by linarith
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<8*(f:ℝ)^2*k)
    (by positivity : (0:ℝ)<2*f*k)).mpr
  have hb : (m+3:ℝ)+(m+3)*f≤2*(m+3)*f := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ)≤m+3) (sub_nonneg.mpr hfR)]
  have hb' := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ)≤2*f*k)
  have hc : (m+3:ℝ)≤2*(m+2) := by linarith
  have hc' := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ)≤4*(f:ℝ)^2*k)
  nlinarith only [hb',hc']

/-- Source-scale finite form on the actual number of vertices, with any
competition budget at most 2f−1. The denominator is a proved finite minimum. -/
theorem cycle_lower_in_actual_vertices (m f k q : ℕ) (hf : 0<f) (hk : 0<k)
    (hq : q≤2*f-1) (hm : 2*k≤m+2) :
    ∃ Q : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
      IsMinimumFTPreserver
        (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
        Q (coreWeight (cycleGraph (m+3)) ((m+2)/k)) q ∧
      ∀ H : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
        IsEFTSpanner
          (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
          H (coreWeight (cycleGraph (m+3)) ((m+2)/k)) k f →
        (Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3))):ℝ)/(8*(f:ℝ)^2*k) ≤
          competitiveLightness H Q (coreWeight (cycleGraph (m+3)) ((m+2)/k)) := by
  obtain ⟨Q,hQ,hh⟩ := cycle_lower_family m f k q hf hk hq hm
  refine ⟨Q,hQ,fun H hH => ?_⟩
  have hb := (cycle_lower_ratio_in_vertices m f k hf hk).trans (hh H hH)
  simpa only [cycle_vertex_card_at,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hb

/-- For fixed f,k, the displayed finite-domain family has unbounded order. -/
theorem cycle_family_unbounded (f k N : ℕ) :
    ∃ m : ℕ,2*k≤m+2 ∧ N≤Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3))) := by
  refine ⟨N+2*k,by omega,?_⟩
  rw [cycle_vertex_card_at]
  omega
end LightEFTSpanners.ParallelSubdivision
