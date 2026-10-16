import LightEFTSpanners.NativeCutUncrossing
import LightEFTSpanners.EvenSplittingMass

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- The native graph on vertices other than the distinguished center none.
All original inner edge IDs are retained, including loops and multiplicities. -/
def centerCore (G : Graph (Option V) E) : Graph V E where
  vertexSet := {v | some v∈G.vertexSet}
  IsLink e u v := G.IsLink e (some u) (some v)
  isLink_symm := by intro e _; exact ⟨fun x y h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e u v a b h h'
    exact (h.left_eq_or_eq h').imp Option.some.inj Option.some.inj
  left_mem_of_isLink := by intro e x y h; exact h.left_mem

/-- Nonloop incident edge identities at the center. Center loops have no cut
contribution and are intentionally absent from this type. -/
abbrev CenterInc (G : Graph (Option V) E) := {e : E // ∃ v,G.IsLink e none (some v)}

noncomputable instance (priority := 2000) centerIncFintype [Fintype E]
    (G : Graph (Option V) E) : Fintype (CenterInc G) := Fintype.ofFinite _

noncomputable def centerEnd (G : Graph (Option V) E) (i : CenterInc G) : V :=
  Classical.choose i.property

theorem centerEnd_link (G : Graph (Option V) E) (i : CenterInc G) :
    G.IsLink i.val none (some (centerEnd G i)) := Classical.choose_spec i.property

/-- Finite terminal sets, viewed as center-free sets of actual ambient vertices. -/
def liftSet (S : Finset V) : Set (Option V) := {v | ∃ u∈S,v=some u}

@[simp] theorem none_not_liftSet (S : Finset V) : none∉liftSet S := by simp [liftSet]
@[simp] theorem some_mem_liftSet (S : Finset V) (v : V) : some v∈liftSet S ↔ v∈S := by
  simp [liftSet]

theorem core_cut_link (G : Graph (Option V) E) {e : E} {a b : V}
    (h : G.IsLink e (some a) (some b)) (S : Finset V) :
    e∈(centerCore G).edgeCut (S:Set V) ↔ (a∈S ∧ b∉S) ∨ (b∈S ∧ a∉S) :=
  (show (centerCore G).IsLink e a b from h).mem_edgeCut_iff

theorem center_inc_unique (G : Graph (Option V) E) (i : CenterInc G) {v : V}
    (h : G.IsLink i.val none (some v)) : centerEnd G i=v := by
  rcases (centerEnd_link G i).eq_and_eq_or_eq_and_eq h with h' | h'
  · exact Option.some.inj h'.2
  · cases h'.1

/-- Native center-free cuts split exactly into the surviving core cut and
one unit for each original center-edge identity with its endpoint in the set. -/
theorem cutSize_center_decomposition [Fintype E] (G : Graph (Option V) E)
    [DecidableEq V] (S : Finset V) :
    cutSize G (liftSet S)=cutSize (centerCore G) (S:Set V)+mass (centerEnd G) S := by
  classical
  have hm : mass (centerEnd G) S=
      ∑ e : E,if h : ∃ v,G.IsLink e none (some v) then
        (if centerEnd G ⟨e,h⟩∈S then (1:ℤ) else 0) else 0 := by
    let P : E → Prop := fun e => ∃ v,G.IsLink e none (some v)
    let f : E → ℤ := fun e => if h : P e then
      (if centerEnd G ⟨e,h⟩∈S then 1 else 0) else 0
    have h := Fintype.sum_subtype_add_sum_subtype P f
    have hFI : Subtype.fintype P=centerIncFintype G := Subsingleton.elim _ _
    rw [hFI] at h
    have hyes : (∑ e : {e // P e},f e.val)=mass (centerEnd G) S := by
      unfold mass
      apply sum_congr rfl
      intro e _
      simp [f,e.property]
    have hno : (∑ e : {e // ¬P e},f e.val)=0 := by
      apply sum_eq_zero
      intro e _
      simp [f,e.property]
    rw [hyes,hno,add_zero] at h
    exact h
  rw [hm,cutSize_sum,cutSize_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e∈G.edgeSet
  · obtain ⟨a,b,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    cases a with
    | none =>
      cases b with
      | none =>
        have hi : ¬∃ v,G.IsLink e none (some v) := by
          rintro ⟨v,hv⟩
          rcases h.eq_and_eq_or_eq_and_eq hv with hh | hh <;> simp_all
        have hc : e∉(centerCore G).edgeCut (S:Set V) := by
          rintro ⟨u,v,huv,_,_⟩
          rcases h.left_eq_or_eq huv with hh | hh <;> simp_all
        simp [h.mem_edgeCut_iff,hi,hc]
      | some v =>
        have hi : ∃ v,G.IsLink e none (some v) := ⟨v,h⟩
        have hv : centerEnd G ⟨e,hi⟩=v := center_inc_unique G ⟨e,hi⟩ h
        have hc : e∉(centerCore G).edgeCut (S:Set V) := by
          rintro ⟨u,w,huw,_,_⟩
          rcases h.left_eq_or_eq huw with hh | hh <;> simp_all
        simp [h.mem_edgeCut_iff,hi,hv,hc]
    | some u =>
      cases b with
      | none =>
        have hi : ∃ v,G.IsLink e none (some v) := ⟨u,h.symm⟩
        have hu : centerEnd G ⟨e,hi⟩=u := center_inc_unique G ⟨e,hi⟩ h.symm
        have hc : e∉(centerCore G).edgeCut (S:Set V) := by
          rintro ⟨v,w,hvw,_,_⟩
          rcases h.symm.left_eq_or_eq hvw with hh | hh <;> simp_all
        simp [h.mem_edgeCut_iff,hi,hu,hc]
      | some v =>
        have hi : ¬∃ w,G.IsLink e none (some w) := by
          rintro ⟨w,hw⟩
          rcases hw.left_eq_or_eq h with hh | hh <;> simp_all
        simp [h.mem_edgeCut_iff,core_cut_link G h S,hi]
  · have hnc : e∉G.edgeCut (liftSet S) := fun h => he (Graph.edgeCut_subset_edgeSet h)
    have hncore : e∉(centerCore G).edgeCut (S:Set V) := by
      rintro ⟨a,b,h,_,_⟩
      exact he (show G.IsLink e (some a) (some b) from h).edge_mem
    have hni : ¬∃ v,G.IsLink e none (some v) := by rintro ⟨v,h⟩;exact he h.edge_mem
    simp [hnc,hncore,hni]
end LightEFTSpanners.EvenSplitting
