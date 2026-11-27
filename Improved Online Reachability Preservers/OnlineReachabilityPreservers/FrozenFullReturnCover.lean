import OnlineReachabilityPreservers.FullReturnIncidenceCover
import OnlineReachabilityPreservers.FrozenQuadraticTrimming

/-! Freeze the original caps after an incidence cover repairs the standard pieces. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem erased_rectangle_mass_loss {V J : Type*} [LinearOrder V] [Fintype V] [DecidableEq J]
    (pieces : J → List V) (simple : ∀ j, (pieces j).Nodup)
    (A : Finset V) (B : Finset J) (deleted : Finset (J × V)) :
    let erased := erasePieceIncidences pieces deleted
    (∑ j ∈ B, ((pieces j).toFinset ∩ A).card) ≤
      (∑ j ∈ B, ((erased j).toFinset ∩ A).card) + deleted.card := by
  let erased := erasePieceIncidences pieces deleted
  have step (j : J) : ((pieces j).toFinset ∩ A).card + (erased j).length ≤
      ((erased j).toFinset ∩ A).card + (pieces j).length := by
    let original := (pieces j).toFinset
    let kept := (erased j).toFinset
    have sub : (erased j).Sublist (pieces j) := erasePieceIncidences_sublist pieces deleted j
    have subset : kept ⊆ original := fun v present => List.mem_toFinset.mpr (sub.subset (List.mem_toFinset.mp present))
    have cutSubset : kept ∩ A ⊆ original ∩ A := by
      intro v h
      obtain ⟨inside,onA⟩ := mem_inter.mp h
      exact mem_inter.mpr ⟨subset inside,onA⟩
    have lossSubset : (original ∩ A) \ (kept ∩ A) ⊆ original \ kept := by
      intro v h
      obtain ⟨originalA,missing⟩ := mem_sdiff.mp h
      obtain ⟨inside,onA⟩ := mem_inter.mp originalA
      exact mem_sdiff.mpr ⟨inside,fun remains => missing (mem_inter.mpr ⟨remains,onA⟩)⟩
    have originalCount := card_sdiff_add_card_eq_card subset
    have cutCount := card_sdiff_add_card_eq_card cutSubset
    have lossBound := card_le_card lossSubset
    change (original ∩ A).card + (erased j).length ≤ (kept ∩ A).card + (pieces j).length
    rw [← List.toFinset_card_of_nodup (simple j), ← List.toFinset_card_of_nodup (sub.nodup (simple j))]
    change (original ∩ A).card + kept.card ≤ (kept ∩ A).card + original.card
    omega
  have byRows := sum_le_sum (s := B) (fun j _ => step j)
  simp only [sum_add_distrib] at byRows
  have lost := erasePieceIncidences_mass_add_loss simple B deleted
  change (∑ j ∈ B, (erased j).length) + (pieceIncidences pieces B ∩ deleted).card = _ at lost
  have used : (pieceIncidences pieces B ∩ deleted).card ≤ deleted.card := card_le_card inter_subset_right
  change (∑ j ∈ B, ((pieces j).toFinset ∩ A).card) ≤
    (∑ j ∈ B, ((erased j).toFinset ∩ A).card) + deleted.card
  omega

/-- A crossed-return cover on the original-width pieces, with cost at
most five sixteenths of the input mass. -/
def HasSmallCrossedReturnWidthCover {n p : ℕ} (paths : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  ∃ deleted : Finset (ListBlockIndex copies L × ListVertexBlockIndex paths D),
    CrossedParentReturnIncidenceCover copies (splitListPaths copies L) Sigma.fst (cutoff-5) deleted ∧
      16*deleted.card ≤ 5*M

/-- The original-width pieces can be cropped within both original budgets
with at most one sixth loss. A small incidence cover on those pieces
permits frozen full-bridge cleaning at the original cutoff. -/
theorem regularization_list_frozen_full_after_width_return_cover {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (budget : 8*max n p < (∑ i, (paths i).length) → HasSmallCrossedReturnWidthCover paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 48*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',vertices,p',rows,clean,cleanSimple,cleanFree,keeps,within,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree (by omega) hn hp dense long low
    exact ⟨n',vertices,p',rows,clean,cleanSimple,cleanFree,by omega,within,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let Vertex := ListVertexBlockIndex paths D
  let Piece := ListBlockIndex copies L
  let pieces : Piece → List Vertex := listRegularizedPaths paths D L
  obtain ⟨deleted,cover,cost⟩ := budget (lt_of_not_ge low)
  let erased := erasePieceIncidences pieces deleted
  have pieceSimple (j : Piece) := listRegularizedPaths_simple paths simple D L j
  have rowSub (j : Piece) : (erased j).Sublist (pieces j) := erasePieceIncidences_sublist pieces deleted j
  have erasedSimple (j : Piece) := (rowSub j).nodup (pieceSimple j)
  have copyFree : BridgeFree (Before copies) cutoff :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have erasedFree : BridgeFree (Before erased) cutoff :=
    fullBridgeFree_after_crossed_parent_return_erasure (I := Fin p) (V := Vertex) Sigma.fst pieceSimple
      (fun {j _ _} forward => listBefore_of_sublist (paths := fun i : Piece => copies i.fst)
        (splitListVertices_simple paths D j.fst (simple j.fst)) List.filter_sublist forward)
      (fun {_ _ _} => splitListPaths_disjoint) copyFree large deleted cover
  obtain ⟨A,vertexBudget,B,pathBudget,retained⟩ :=
    listRegularizedPaths_exists_original_budget_rectangle paths simple hn hp dense long
  let kept := restrictListPaths erased A B
  have keptSimple (i : B) : (kept i).Nodup := restrictListPath_nodup (erasedSimple i.val) A
  have keptFree : BridgeFree (Before kept) cutoff := restrictListPaths_fullFree erasedSimple erasedFree A B
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have keptLength (i : B) : (kept i).length ≤ L := calc
    _ = ((erased i.val).toFinset ∩ A).card := restrictListPath_length (erasedSimple i.val) A
    _ ≤ (erased i.val).length := (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
    _ ≤ (pieces i.val).length := (rowSub i.val).length_le
    _ ≤ L := length i.val
  have erasedDegree (v : Vertex) : (occurrences (fun j => (erased j).toFinset) v).card ≤ D := by
    apply le_trans _ (degree v)
    apply card_le_card
    intro j on
    have marked := (mem_occurrences (marks := fun q : Piece => (erased q).toFinset)).mp on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((rowSub j).subset (List.mem_toFinset.mp marked)))
  have keptDegree (v : A) : (occurrences (fun j => (kept j).toFinset) v).card ≤ D := by
    have projected : (fun j => (kept j).toFinset) = rectanglePaths (fun j => (erased j).toFinset) A B :=
      funext (restrictListPaths_toFinset erased A B)
    rw [projected]
    exact (rectanglePaths_degree_le (fun j => (erased j).toFinset) A B v).trans (erasedDegree v.val)
  have keptMass : (∑ j, (kept j).length) = ∑ j ∈ B, ((erased j).toFinset ∩ A).card := by
    rw [← Finset.sum_attach B (fun j => ((erased j).toFinset ∩ A).card)]
    exact sum_congr rfl fun j _ => restrictListPath_length (erasedSimple j.val) A
  have keptUpper : (∑ j, (kept j).length) ≤ M := by
    rw [keptMass]
    exact (sum_le_sum (fun j _ => (card_le_card inter_subset_left).trans (List.toFinset_card_le (erased j)))).trans
      ((sum_le_sum_of_subset (subset_univ B)).trans ((sum_le_sum fun j _ => (rowSub j).length_le).trans mass.le))
  have lost := erased_rectangle_mass_loss pieces pieceSimple A B deleted
  have floor : 50*M ≤ 96*(∑ j, (kept j).length) := by
    change 5*M ≤ 6*(∑ j ∈ B, ((pieces j).toFinset ∩ A).card) at retained
    change 16*deleted.card ≤ 5*M at cost
    change (∑ j ∈ B, ((pieces j).toFinset ∩ A).card) ≤
      (∑ j ∈ B, ((erased j).toFinset ∩ A).card) + deleted.card at lost
    rw [← keptMass] at lost
    omega
  exact regularization_list_frozen_after_caps_with_ratios_of_mass (half := false) (k := cutoff)
    (retention := 48) (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1) kept keptSimple keptFree
    hn hp dense long (by decide) (by decide) (by decide) (by decide)
    (by simpa only [one_mul,Fintype.card_coe] using vertexBudget)
    (by simpa only [one_mul,Fintype.card_coe] using pathBudget)
    keptLength keptDegree keptUpper (by simpa only [one_mul] using floor)

/-- The full-bridge repair also gives the feasible literal witness. -/
theorem regularization_list_frozen_full_distinct_after_width_return_cover {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (budget : 8*max n p < (∑ i, (paths i).length) → HasSmallCrossedReturnWidthCover paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 48*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 48)
    paths distinct nonempty simple free (by omega) hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_after_width_return_cover paths simple free large hn hp dense long budget)

end OnlineReachabilityPreservers
