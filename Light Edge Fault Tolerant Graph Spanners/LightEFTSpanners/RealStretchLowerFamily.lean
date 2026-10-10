import LightEFTSpanners.CycleLowerFamily
import Mathlib.Algebra.Order.Floor.Ring

namespace LightEFTSpanners
open SimpleGraph LightSpanners

theorem IsEFTSpanner.stretch_mono {V : Type*} {G H : SimpleGraph V}
    {w : Sym2 V → ℝ} {t s : ℝ} {f : ℕ}
    (h : IsEFTSpanner G H w t f) (hts : t≤s) (hw : ∀ e,0≤w e) :
    IsEFTSpanner G H w s f := by
  refine ⟨h.1,fun F hF => ⟨(h.2 F hF).1,?_⟩⟩
  intro u v p
  obtain ⟨r,hr⟩ := (h.2 F hF).2 u v p
  exact ⟨r,hr.trans (mul_le_mul_of_nonneg_right hts (walkWeight_nonneg w hw p))⟩

namespace ParallelSubdivision
attribute [local instance] Classical.propDecidable

/-- Real stretch is not silently restricted to integer values. Rounding upward
loses at most a factor two for t≥1, and all constants remain explicit. -/
theorem cycle_real_lower_family (m f q : ℕ) (hf : 0<f) (hq : q≤2*f-1)
    (t : ℝ) (ht : 1≤t) (hm : 2*⌈t⌉₊≤m+2) :
    ∃ Q : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
      IsMinimumFTPreserver
        (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
        Q (coreWeight (cycleGraph (m+3)) ((m+2)/⌈t⌉₊)) q ∧
      ∀ H : SimpleGraph (Vertex (I:=Fin f) (cycleGraph (m+3))),
        IsEFTSpanner
          (graph (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
          H (coreWeight (cycleGraph (m+3)) ((m+2)/⌈t⌉₊)) t f →
        (Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3))):ℝ)/(16*(f:ℝ)^2*t) ≤
          competitiveLightness H Q (coreWeight (cycleGraph (m+3)) ((m+2)/⌈t⌉₊)) := by
  classical
  have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hk : 0<⌈t⌉₊ := Nat.ceil_pos.mpr htpos
  have hkR : (0:ℝ)<⌈t⌉₊ := by exact_mod_cast hk
  have hfR : (0:ℝ)<f := by exact_mod_cast hf
  have hceil : (⌈t⌉₊:ℝ)≤2*t := by
    have hc := Nat.ceil_lt_add_one htpos.le
    linarith
  obtain ⟨Q,hQ,hh⟩ := cycle_lower_in_actual_vertices m f ⌈t⌉₊ q hf hk hq hm
  refine ⟨Q,hQ,fun H hH => ?_⟩
  have hw : ∀ e,0≤coreWeight (I:=Fin f) (cycleGraph (m+3)) ((m+2)/⌈t⌉₊) e := by
    intro e
    exact (coreWeight_positive (cycleGraph (m+3)) (by positivity) e).le
  have hb := hh H (hH.stretch_mono (Nat.le_ceil t) hw)
  apply le_trans ?_ hb
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hceil (by positivity : (0:ℝ)≤8*(f:ℝ)^2)]

/-- Nonvacuity at the original real stretch, not merely at its ceiling. -/
theorem cycle_real_input_self_spanner (m f : ℕ) (t : ℝ) (ht : 1≤t) :
    IsEFTSpanner
      (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      (graph (I:=Fin f) (cycleGraph (m+3)) ⊔ coreGraph (cycleGraph (m+3)) (cycleGraph (m+3)))
      (coreWeight (cycleGraph (m+3)) ((m+2)/⌈t⌉₊)) t f := by
  have hk : 0<⌈t⌉₊ := Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one ht)
  have hkR : (0:ℝ)<⌈t⌉₊ := by exact_mod_cast hk
  exact self_eftSpanner _ _ (fun e => (coreWeight_positive _ (by positivity) e).le) ht f

/-- For every fixed real t≥1 and f, the admissible family has unbounded order. -/
theorem cycle_real_family_unbounded (f N : ℕ) (t : ℝ) :
    ∃ m : ℕ,2*⌈t⌉₊≤m+2 ∧ N≤Fintype.card (Vertex (I:=Fin f) (cycleGraph (m+3))) :=
  cycle_family_unbounded f ⌈t⌉₊ N
end ParallelSubdivision
end LightEFTSpanners
