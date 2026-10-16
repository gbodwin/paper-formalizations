import LightEFTSpanners.NativeCutUncrossing

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Actual finite multigraph degree, stored as an integer for parity
arithmetic. A loop contributes two; each other incident original ID one. -/
noncomputable def nativeDegree (G : Graph V E) (v : V) : ℤ :=
  ∑ e : E,if G.IsLink e v v then 2 else if G.Inc e v then 1 else 0

omit [Fintype E] in
theorem degreeTerm_of_link (G : Graph V E) {e : E} {a b : V}
    (h : G.IsLink e a b) (v : V) :
    (if G.IsLink e v v then (2:ℤ) else if G.Inc e v then 1 else 0)=
      (if v=a then 1 else 0)+(if v=b then 1 else 0) := by
  have hi : G.Inc e v ↔ v=a ∨ v=b := by
    constructor
    · exact fun hv => hv.eq_or_eq_of_isLink h
    · rintro (rfl|rfl)
      · exact h.inc_left
      · exact h.inc_right
  simp only [h.isLink_iff,hi]
  by_cases ha : v=a <;> by_cases hb : v=b <;> simp_all [eq_comm]

/-- Sum of actual degrees in a finite set equals twice its inner-edge
count plus its actual edge cut. Unused IDs contribute zero. -/
theorem native_handshake (G : Graph V E) (S : Finset V) :
    ∑ v∈S,nativeDegree G v=
      2*(∑ e : E,if ∃ a b,G.IsLink e a b ∧ a∈S ∧ b∈S then (1:ℤ) else 0)+
      cutSize G (S:Set V) := by
  classical
  simp only [nativeDegree,cutSize_sum,mul_sum,←sum_add_distrib]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases he : e∈G.edgeSet
  · obtain ⟨a,b,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have hin : (∃ u v,G.IsLink e u v ∧ u∈S ∧ v∈S) ↔ a∈S ∧ b∈S := by
      constructor
      · rintro ⟨u,v,huv,hu,hv⟩
        rcases h.eq_and_eq_or_eq_and_eq huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hu,hv⟩
        · exact ⟨hv,hu⟩
      · exact fun hab => ⟨a,b,h,hab⟩
    simp only [degreeTerm_of_link G h,sum_add_distrib,sum_ite_eq',hin,h.mem_edgeCut_iff,
      Finset.mem_coe]
    by_cases ha : a∈S <;> by_cases hb : b∈S <;> simp [ha,hb]
  · have hn (v w : V) : ¬G.IsLink e v w := fun h => he h.edge_mem
    have hi (v : V) : ¬G.Inc e v := fun h => he h.edge_mem
    have hc : e∉G.edgeCut (S:Set V) := fun h => he (Graph.edgeCut_subset_edgeSet h)
    simp only [hn,hi,hc,ite_false,sum_const_zero,add_zero]
    simp

/-- The usual even-degree Eulerian condition forces every actual cut to be
even. This discharges the cut-parity premise from graph-local degrees. -/
theorem even_cut_of_even_degrees (G : Graph V E) [Fintype V]
    (hdeg : ∀ v,Even (nativeDegree G v)) (S : Set V) : Even (cutSize G S) := by
  classical
  have he : Even (∑ v∈S.toFinset,nativeDegree G v) := by
    induction S.toFinset using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert v T hv ih => simpa only [sum_insert hv] using (hdeg v).add ih
  have hh := native_handshake G S.toFinset
  rw [Set.coe_toFinset] at hh
  rw [hh] at he
  simp only [Set.mem_toFinset] at he
  have htwo : Even (2*(∑ e : E,if ∃ a b,G.IsLink e a b ∧ a∈S ∧ b∈S then (1:ℤ) else 0)) := ⟨_,by ring⟩
  have h := he.sub htwo
  simpa only [add_sub_cancel_left] using h
/-- Conversely, singleton cuts recover the usual even-degree condition;
loops contribute two and therefore do not alter parity. -/
theorem even_degrees_of_even_cuts (G : Graph V E)
    (hcut : ∀ S : Set V,Even (cutSize G S)) (v : V) : Even (nativeDegree G v) := by
  classical
  have h := native_handshake G ({v}:Finset V)
  simp only [sum_singleton] at h
  rw [h]
  exact (show Even ((2:ℤ)*_) from ⟨_,by ring⟩).add (hcut _)
end LightEFTSpanners.MultigraphCuts
