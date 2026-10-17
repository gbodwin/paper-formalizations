import LightEFTSpanners.NativeCenterDecomposition

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Literal splitting of two original nonloop center edges. Old surviving
edges keep their IDs as `some e`; the one fresh edge has ID `none`. Equal
other endpoints are allowed and produce a loop, never a collapsed edge. -/
def centerSplit (G : Graph (Option V) E) (i j : CenterInc G) : Graph (Option V) (Option E) where
  vertexSet := G.vertexSet
  IsLink f x y := match f with
    | some e => G.IsLink e x y ∧ e≠i.val ∧ e≠j.val
    | none => (x=some (centerEnd G i) ∧ y=some (centerEnd G j)) ∨
        (x=some (centerEnd G j) ∧ y=some (centerEnd G i))
  isLink_symm := by
    intro f _
    refine ⟨?_⟩
    intro x y h
    cases f with
    | some e => exact ⟨h.1.symm,h.2⟩
    | none => exact h.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro f x y a b h h'
    cases f with
    | some e => exact h.1.left_eq_or_eq h'.1
    | none => rcases h with h | h <;> rcases h' with h' | h' <;> simp_all
  left_mem_of_isLink := by
    intro f x y h
    cases f with
    | some e => exact h.1.left_mem
    | none =>
      rcases h with h | h
      · rw [h.1]; exact (centerEnd_link G i).right_mem
      · rw [h.1]; exact (centerEnd_link G j).right_mem

theorem centerSplit_old_cut (G : Graph (Option V) E) (i j : CenterInc G)
    (S : Set (Option V)) (e : E) :
    some e∈(centerSplit G i j).edgeCut S ↔ e∈G.edgeCut S ∧ e≠i.val ∧ e≠j.val := by
  constructor
  · rintro ⟨x,y,⟨h,hi,hj⟩,hx,hy⟩
    exact ⟨⟨x,y,h,hx,hy⟩,hi,hj⟩
  · rintro ⟨⟨x,y,h,hx,hy⟩,hi,hj⟩
    exact ⟨x,y,⟨h,hi,hj⟩,hx,hy⟩

theorem centerSplit_new_cut (G : Graph (Option V) E) (i j : CenterInc G)
    (S : Finset V) :
    none∈(centerSplit G i j).edgeCut (liftSet S) ↔
      (centerEnd G i∈S ∧ centerEnd G j∉S) ∨
      (centerEnd G j∈S ∧ centerEnd G i∉S) := by
  have h : (centerSplit G i j).IsLink none (some (centerEnd G i)) (some (centerEnd G j)) :=
    Or.inl ⟨rfl,rfl⟩
  simpa only [some_mem_liftSet] using (h.mem_edgeCut_iff (S:=liftSet S))

/-- Exact native cut change: a center-free cut loses two precisely when it
contains both other endpoints, and otherwise is unchanged. -/
theorem centerSplit_cutSize [Fintype E] [DecidableEq V]
    (G : Graph (Option V) E) (i j : CenterInc G) (hij : i≠j) (S : Finset V) :
    cutSize G (liftSet S)=cutSize (centerSplit G i j) (liftSet S)+
      (if centerEnd G i∈S ∧ centerEnd G j∈S then 2 else 0) := by
  classical
  have heij : i.val≠j.val := fun h => hij (Subtype.ext h)
  have hi : i.val∈G.edgeCut (liftSet S) ↔ centerEnd G i∈S := by
    simp [(centerEnd_link G i).mem_edgeCut_iff]
  have hj : j.val∈G.edgeCut (liftSet S) ↔ centerEnd G j∈S := by
    simp [(centerEnd_link G j).mem_edgeCut_iff]
  have hterm (e : E) :
      (if e∈G.edgeCut (liftSet S) then (1:ℤ) else 0)=
      (if e∈G.edgeCut (liftSet S) ∧ e≠i.val ∧ e≠j.val then 1 else 0)+
      (if e=i.val then (if centerEnd G i∈S then 1 else 0) else 0)+
      (if e=j.val then (if centerEnd G j∈S then 1 else 0) else 0) := by
    by_cases hei : e=i.val
    · subst e; simp [hi,heij]
    · by_cases hej : e=j.val
      · subst e; simp [hj,Ne.symm heij]
      · simp [hei,hej]
  have hsum := sum_congr rfl (fun e (_ : e∈(univ:Finset E)) => hterm e)
  simp only [sum_add_distrib] at hsum
  simp only [sum_ite_eq',mem_univ,ite_true] at hsum
  rw [cutSize_sum,cutSize_sum,Fintype.sum_option]
  simp only [centerSplit_old_cut,centerSplit_new_cut]
  by_cases hiS : centerEnd G i∈S <;> by_cases hjS : centerEnd G j∈S <;>
    simp only [hiS,hjS,not_true_eq_false,not_false_eq_true,and_self,and_false,
      false_and,or_self,or_false,false_or,ite_true,ite_false] at * <;> omega
end LightEFTSpanners.EvenSplitting
