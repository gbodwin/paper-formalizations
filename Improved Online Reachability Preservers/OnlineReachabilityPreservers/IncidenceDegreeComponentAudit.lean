import OnlineReachabilityPreservers.IncidenceCyclePairAudit
import OnlineReachabilityPreservers.IncidenceDegreeComponentCleaning

/-! Whole deleted-vertex groups avoid the half-six split obstruction. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset SimpleGraph
open scoped Sigma.Lex

private abbrev TransposedNode := Fin 20 ⊕ Fin 10
private abbrev transposedRows := incidenceTranspose mixedCycleRows
private abbrev transposedGraph := pathIncidenceGraph transposedRows
private def terminal : TransposedNode := .inl 3

private instance transposedAdjDecidable : DecidableRel transposedGraph.Adj
  | .inl x, .inr i => decidable_of_iff (x ∈ mixedCycleRows i) mem_incidenceTranspose.symm
  | .inr i, .inl x => decidable_of_iff (x ∈ mixedCycleRows i) mem_incidenceTranspose.symm
  | .inl _, .inl _ => isFalse id
  | .inr _, .inr _ => isFalse id

private def componentColor : TransposedNode → Fin 7
  | .inl x => ![1,1,1,6,0,2,3,4,5,6,6,6,6,6,6,6,6,6,6,6] x
  | .inr i => ![0,1,2,3,1,0,4,5,1,1] i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem componentColor_edge : ∀ a b, a ≠ terminal → b ≠ terminal →
    transposedGraph.Adj a b → componentColor a = componentColor b := by decide

private theorem componentColor_walk {u v : TransposedNode} (w : transposedGraph.Walk u v)
    (avoids : terminal ∉ w.support) : componentColor u = componentColor v := by
  induction w with
  | nil => rfl
  | @cons a b z edge tail ih =>
    have first : a ≠ terminal := fun eq => avoids (eq ▸ (SimpleGraph.Walk.cons edge tail).start_mem_support)
    have rest : terminal ∉ tail.support := by
      intro on
      exact avoids (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr on)
    have second : b ≠ terminal := fun eq => rest (eq ▸ tail.start_mem_support)
    exact (componentColor_edge a b first second edge).trans (ih rest)

private theorem transposed_marks (x : Fin 20) :
    (transposedRows x).toFinset = occurrences (fun i => (mixedCycleRows i).toFinset) x := by
  ext i
  simp only [List.mem_toFinset,mem_incidenceTranspose,mem_occurrences]

private theorem componentColor_fiber_small : ∀ (i : Fin 10),
    ((transposedRows 3).toFinset.filter fun j => componentColor (.inr j) = componentColor (.inr i)).card ≤ 2 := by
  simp only [transposed_marks]
  decide

private theorem other_degrees_small : ∀ (x : Fin 20), x ≠ 3 → (transposedRows x).toFinset.card ≤ 2 := by
  simp only [transposed_marks]
  decide

/-- Every deleted-vertex group and every deleted-row group in the
half-six splitting example has size at most two. -/
theorem mixedCycleRows_incidence_group_sizes :
    (∀ x i, (incidenceVertexDeletionGroup mixedCycleRows x i).card ≤ 2) ∧
      (∀ i x, (incidenceRowDeletionGroup mixedCycleRows i x).card ≤ 2) := by
  constructor
  · intro x i
    change (incidenceRowDeletionGroup transposedRows x i).card ≤ 2
    by_cases critical : x = 3
    · subst x
      refine (card_le_card (t := (transposedRows 3).toFinset.filter
        (fun j => componentColor (.inr j) = componentColor (.inr i))) ?_).trans (componentColor_fiber_small i)
      intro j on
      obtain ⟨member,w,avoids⟩ := mem_incidenceRowDeletionGroup.mp on
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr member,(componentColor_walk w avoids).symm⟩
    · have sub : incidenceRowDeletionGroup transposedRows x i ⊆ (transposedRows x).toFinset :=
        fun j on => List.mem_toFinset.mpr (mem_incidenceRowDeletionGroup.mp on).1
      exact (card_le_card sub).trans (other_degrees_small x critical)
  · intro i x
    have sub : incidenceRowDeletionGroup mixedCycleRows i x ⊆ (mixedCycleRows i).toFinset :=
      fun y on => List.mem_toFinset.mpr (mem_incidenceRowDeletionGroup.mp on).1
    exact (card_le_card sub).trans (List.toFinset_card_le _)

/-- With degree width four, whole-component copies of the half-six
example preserve every half cutoff and the original row projections. -/
theorem mixedCycleRows_incidence_degree_copies (k : ℕ) :
    ∃ (sizes : Fin 20 → ℕ) (copies : Fin 10 → List (Σₗ v : Fin 20, Fin (sizes v))),
      (∀ i, (copies i).Nodup) ∧ HalfBridgeFree (BeforeIn copies) k ∧
      (∀ i, (copies i).map Sigma.fst = mixedCycleRows i) ∧
      (∀ v, (occurrences (fun i => (copies i).toFinset) v).card ≤ 4) := by
  obtain ⟨sizes,copies,simple,legal,projects,degree,_⟩ :=
    copies_of_incidence_vertex_deletion_group_room (half := true) (width := 4)
      mixedCycleRows_original_widths.1 (mixedCycleRows_halfFree k)
      (fun x i _ => (mixedCycleRows_incidence_group_sizes.1 x i).trans (by decide))
  exact ⟨sizes,copies,simple,legal,projects,degree⟩

/-- At the exact original widths, the two component bounds give an
indexed frozen witness at every half cutoff. -/
theorem mixedCycleRows_frozen_half_from_incidence_components (k : ℕ) :
    ∃ n' ≤ 20, ∃ p' ≤ 10, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (BeforeIn clean) k ∧
      20 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 20 ∧ frozenListCaps 20 10 20 clean := by
  have mass := mixedCycleRows_original_widths.2.1
  have dense : 20 ≤ ∑ i, (mixedCycleRows i).length := mass.ge
  have long := (by decide : 10 ≤ 20).trans dense
  have result := regularization_list_frozen_of_incidence_deletion_group_rooms (half := true)
    mixedCycleRows mixedCycleRows_original_widths.1 (mixedCycleRows_halfFree k) (by decide) (by decide) dense long
    (by
      dsimp only
      rw [mass]
      intro x i _
      exact (mixedCycleRows_incidence_group_sizes.1 x i).trans (by decide))
    (by
      dsimp only
      rw [mass]
      intro i x _
      exact (mixedCycleRows_incidence_group_sizes.2 i x).trans (by decide))
  simpa only [mass,localOrderAdmissible,ite_true] using result

end OnlineReachabilityPreservers.SourceAudit
