import LightEFTSpanners.NativeEdgeLevels

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

theorem edgeInside_restrict_iff (G : Graph V E) (F : Set E)
    (R : Setoid G.vertexSet) {e : E} (he : e∈F) :
    edgeInside (G.restrict F) R e ↔ edgeInside G R e := by
  constructor
  · rintro ⟨a,b,hl,hR⟩
    exact ⟨a,b,hl.2,hR⟩
  · rintro ⟨a,b,hl,hR⟩
    exact ⟨a,b,⟨he,hl⟩,hR⟩

/-- Restriction keeps an actual retained identity's level exactly; the ambient
partition still has the same actual vertex domain. -/
theorem edgeLevel_restrict (G : Graph V E) (F : Set E)
    (R : ℕ → Setoid G.vertexSet) (N : ℕ) {e : E} (he : e∈F) :
    edgeLevel (G.restrict F) R N e=edgeLevel G R N e := by
  have h : internalStages (G.restrict F) R N e=internalStages G R N e := by
    ext i
    simp only [internalStages,mem_filter,edgeInside_restrict_iff G F (R i) he]
  simp only [edgeLevel,h]

theorem not_inside_terminal_of_level_lt (G : Graph V E)
    (R : ℕ → Setoid G.vertexSet) (N : ℕ) {e : E}
    (hlt : edgeLevel G R N e<N) : ¬edgeInside G (R N) e := by
  intro hi
  have hm : N∈internalStages G R N e := mem_filter.mpr ⟨mem_range.mpr (by omega),hi⟩
  have hn : (internalStages G R N e).Nonempty := ⟨N,hm⟩
  have hle := le_max' (internalStages G R N e) N hm
  have heq : edgeLevel G R N e=(internalStages G R N e).max' hn := by
    simp only [edgeLevel,dite_eq_left hn]
  rw [←heq] at hle
  omega

/-- Once an edge crosses a stage, extending the finite terminal sentinel does
not change its level. This identifies a local exchange minimum with the same
original partition sequence used by the global proof. -/
theorem edgeLevel_truncate (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (hR : Antitone R) {m N : ℕ} (hmN : m≤N) {e : E}
    (hout : ¬edgeInside G (R m) e) : edgeLevel G R N e=edgeLevel G R m e := by
  have h : internalStages G R N e=internalStages G R m e := by
    ext i
    simp only [internalStages,mem_filter,mem_range]
    constructor
    · rintro ⟨_,hin⟩
      have hi : i<m := by
        by_contra! hn
        exact hout (edgeInside_mono G (hR hn) hin)
      exact ⟨by omega,hin⟩
    · rintro ⟨hi,hin⟩
      exact ⟨by omega,hin⟩
  simp only [edgeLevel,h]
end LightEFTSpanners.MultigraphCuts
