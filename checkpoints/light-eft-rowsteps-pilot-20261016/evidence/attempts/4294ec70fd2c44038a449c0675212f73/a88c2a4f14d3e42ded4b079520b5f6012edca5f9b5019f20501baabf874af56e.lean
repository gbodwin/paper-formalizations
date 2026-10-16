import LightEFTSpanners.PartitionRefinementTermination

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Both endpoints of an actual native edge occupy one partition class.
The condition is independent of the choice of orientation or endpoint proofs. -/
def edgeInside (G : Graph V E) (R : Setoid G.vertexSet) (e : E) : Prop :=
  ∃ a b : G.vertexSet,G.IsLink e a.val b.val ∧ R.r a b

theorem edgeInside_iff (G : Graph V E) (R : Setoid G.vertexSet)
    {e : E} {a b : G.vertexSet} (he : G.IsLink e a.val b.val) :
    edgeInside G R e ↔ R.r a b := by
  constructor
  · rintro ⟨u,v,huv,hR⟩
    rcases he.eq_and_eq_or_eq_and_eq huv with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have ha' : a=u := Subtype.ext ha
      have hb' : b=v := Subtype.ext hb
      simpa only [ha',hb'] using hR
    · have ha' : a=v := Subtype.ext ha
      have hb' : b=u := Subtype.ext hb
      simpa only [ha',hb'] using R.symm hR
  · exact fun h => ⟨a,b,he,h⟩

theorem edgeInside_mono (G : Graph V E) {R S : Setoid G.vertexSet} (h : R≤S) {e : E} :
    edgeInside G R e → edgeInside G S e := by
  rintro ⟨a,b,he,hR⟩
  exact ⟨a,b,he,h hR⟩

/-- All stages up to the finite terminal stage at which the edge is internal. -/
noncomputable def internalStages (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) (e : E) : Finset ℕ := (range (N+1)).filter (fun i => edgeInside G (R i) e)

/-- The last internal stage. The terminal value N represents an edge still
internal at termination; only values below N are called finite levels. -/
noncomputable def edgeLevel (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) (e : E) : ℕ :=
  if h : (internalStages G R N e).Nonempty then (internalStages G R N e).max' h else 0

theorem internalStages_nonempty (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) {e : E} (he : edgeInside G (R 0) e) : (internalStages G R N e).Nonempty := by
  exact ⟨0,mem_filter.mpr ⟨mem_range.mpr (by omega),he⟩⟩

theorem edgeLevel_mem (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) {e : E} (he : edgeInside G (R 0) e) :
    edgeLevel G R N e∈internalStages G R N e := by
  have hn := internalStages_nonempty G R N he
  simp only [edgeLevel,dite_eq_left hn]
  exact max'_mem _ hn

theorem edgeLevel_le (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) {e : E} (he : edgeInside G (R 0) e) : edgeLevel G R N e≤N := by
  have hm := (mem_filter.mp (edgeLevel_mem G R N he)).1
  exact Nat.le_of_lt_succ (mem_range.mp hm)

/-- A genuine crossing terminal edge has a finite level and is internal at
that exact stage but split at the next one. No termination or level oracle is
assumed: the level is the maximum of an explicitly finite stage set. -/
theorem finite_edgeLevel_boundary (G : Graph V E) (R : ℕ → Setoid G.vertexSet)
    (N : ℕ) {e : E} (he : edgeInside G (R 0) e) (hfinal : ¬edgeInside G (R N) e) :
    edgeLevel G R N e<N ∧ edgeInside G (R (edgeLevel G R N e)) e ∧
      ¬edgeInside G (R (edgeLevel G R N e+1)) e := by
  have hmem := edgeLevel_mem G R N he
  have hin := (mem_filter.mp hmem).2
  have hle := edgeLevel_le G R N he
  have hlt : edgeLevel G R N e<N := by
    by_contra! hn
    have heq : edgeLevel G R N e=N := by omega
    exact hfinal (heq ▸ hin)
  refine ⟨hlt,hin,?_⟩
  intro hnext
  have hmemnext : edgeLevel G R N e+1∈internalStages G R N e :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),hnext⟩
  have hmax := le_max' (internalStages G R N e) _ hmemnext
  have hn := internalStages_nonempty G R N he
  have hlevel : edgeLevel G R N e=(internalStages G R N e).max' hn := by
    simp only [edgeLevel,dite_eq_left hn]
  rw [← hlevel] at hmax
  omega
end LightEFTSpanners.MultigraphCuts
