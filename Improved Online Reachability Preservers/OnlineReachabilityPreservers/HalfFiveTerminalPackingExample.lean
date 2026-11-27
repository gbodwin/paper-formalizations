import OnlineReachabilityPreservers.HalfFiveTerminalPacking
import OnlineReachabilityPreservers.HalfBridgeArrivalOrderAudit

/-! Keep the reversed endpoints together at the prescribed path width. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

private theorem widthReorder_collision_protected_empty (v : Fin 6) :
    halfFiveCollisionProtectedRows widthReorderRows v = ∅ := by
  classical
  have empty : halfFiveCollisionRankGraph widthReorderRows v = ∅ :=
    halfFiveCollisionRankGraph_empty_of_no_terminal_three (fun b _ =>
      ((widthReorderRows_full_free 3) (k := 1) (by decide)).false b)
  ext i
  simp [halfFiveCollisionProtectedRows,empty,Edge]

private theorem widthReorder_shared_in_core :
    ∀ (i j : Fin 10) (x : Fin 6), i ≠ j → x ∈ widthReorderRows i → x ∈ widthReorderRows j →
      x ∈ ({0,1,2,3} : Finset (Fin 6)) := by
  decide +kernel

private def widthPackedCore : Finset WidthReorderVertex :=
  univ.filter fun v => v.fst ∈ ({0,1,2,3} : Finset (Fin 6))

private theorem widthPackedCore_card : widthPackedCore.card = 4 := by
  decide +kernel

private theorem widthPacked_mem_projects {i : Fin 10} {v : WidthReorderVertex}
    (on : v ∈ halfFiveCollisionPackedPaths widthReorderRows 6 i) : v.fst ∈ widthReorderRows i := by
  have image := List.mem_map_of_mem (f := fun v : WidthReorderVertex => v.fst) on
  rwa [halfFiveCollisionPackedPaths_project] at image

private theorem widthPacked_reverse_protected_bound (i : Fin 10) :
    (halfFiveReverseProtectedVertices (halfFiveCollisionPackedPaths widthReorderRows 6) i).card ≤ 4 := by
  classical
  have contained : halfFiveReverseProtectedVertices (halfFiveCollisionPackedPaths widthReorderRows 6) i ⊆
      widthPackedCore := by
    intro v on
    simp only [halfFiveReverseProtectedVertices,mem_filter] at on
    obtain ⟨_,j,apart,u,h⟩ := on
    have shared : v.fst ∈ widthReorderRows i ∧ v.fst ∈ widthReorderRows j := by
      rcases h with ⟨forward,backward⟩ | ⟨forward,backward⟩
      · exact ⟨widthPacked_mem_projects forward.1,widthPacked_mem_projects backward.2.1⟩
      · exact ⟨widthPacked_mem_projects forward.2.1,widthPacked_mem_projects backward.1⟩
    exact mem_filter.mpr ⟨mem_univ _,widthReorder_shared_in_core i j v.fst apart shared.1 shared.2⟩
  exact (card_le_card contained).trans_eq widthPackedCore_card

/-- The noncontiguous packing preserves half-five in the original arrival
order at both prescribed widths on the six-vertex example. -/
theorem widthReorder_protected_packing_halfFree :
    let M := ∑ i, (widthReorderRows i).length
    HalfBridgeFree (BeforeIn (halfFiveReversePackedPaths (halfFiveCollisionPackedPaths widthReorderRows (4*M/6))
      (4*M/10))) 5 := by
  dsimp only
  rw [widthReorderRows_parameters.2]
  change HalfBridgeFree (BeforeIn (halfFiveReversePackedPaths (halfFiveCollisionPackedPaths widthReorderRows 6) 4)) 5
  have simple := widthReorderRows_parameters.1
  have copiedSimple (i : Fin 10) : (halfFiveCollisionPackedPaths widthReorderRows 6 i).Nodup :=
    List.Nodup.of_map (fun v => v.fst) ((halfFiveCollisionPackedPaths_project widthReorderRows 6 i).symm ▸ simple i)
  have copied : HalfBridgeFree (BeforeIn (halfFiveCollisionPackedPaths widthReorderRows 6)) 5 :=
    halfFiveCollisionPackedPaths_halfFree simple (widthReorderRows_full_free 5).halfFree (fun v => by
      rw [widthReorder_collision_protected_empty]
      decide)
  exact halfFiveReversePackedPaths_halfFree copiedSimple copied widthPacked_reverse_protected_bound

/-- The new packing and the ordinary splitting run at the same two
widths. The ordinary fixed order admits a half-four, while the packed
fixed order excludes half-bridges through five. -/
theorem widthReorder_prescribed_packing_check :
    ¬ HalfBridgeFree (BeforeIn widthReorderPieces) 4 ∧
      HalfBridgeFree (BeforeIn (halfFiveReversePackedPaths (halfFiveCollisionPackedPaths widthReorderRows 6) 4)) 5 := by
  refine ⟨widthReorderPieces_not_halfFree_four,?_⟩
  have safe := widthReorder_protected_packing_halfFree
  dsimp only at safe
  rw [widthReorderRows_parameters.2] at safe
  exact safe

/-- Both width packings give the indexed frozen witness in this example. -/
theorem widthReorder_protected_packing_frozen :
    ∃ n' ≤ 6, ∃ p' ≤ 10, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (BeforeIn clean) 5 ∧
      10 ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 10 ∧ frozenListCaps 6 10 10 clean := by
  have mass := widthReorderRows_parameters.2
  have dense : 6 ≤ ∑ i, (widthReorderRows i).length := by rw [mass]; decide
  have long : 10 ≤ ∑ i, (widthReorderRows i).length := mass.ge
  have witness := regularization_list_frozen_half_five_of_small_collision_and_reverse_supports
    widthReorderRows_parameters.1 (widthReorderRows_full_free 5).halfFree (by decide) (by decide) dense long
    (by
      dsimp only
      rw [mass]
      intro v
      rw [widthReorder_collision_protected_empty]
      decide)
    (by
      dsimp only
      rw [mass]
      exact widthPacked_reverse_protected_bound)
  simpa only [mass] using witness

end OnlineReachabilityPreservers.SourceAudit
