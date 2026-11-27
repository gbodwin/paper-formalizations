import OnlineReachabilityPreservers.FrozenFullReturnCover

/-! Test crossed returns only within the rectangle that will be kept. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Keep the original piece labels while restricting both supports. -/
noncomputable def listPiecesInRectangle {J V : Type*} [DecidableEq J] [DecidableEq V]
    (pieces : J → List V) (A : Finset V) (B : Finset J) (j : J) : List V :=
  if j ∈ B then (pieces j).filter fun v => decide (v ∈ A) else []

private theorem listPiecesInRectangle_sublist {J V : Type*} [DecidableEq J] [DecidableEq V]
    (pieces : J → List V) (A : Finset V) (B : Finset J) (j : J) :
    (listPiecesInRectangle pieces A B j).Sublist (pieces j) := by
  unfold listPiecesInRectangle
  split
  · exact List.filter_sublist
  · exact List.nil_sublist _

private theorem mem_listPiecesInRectangle {J V : Type*} [DecidableEq J] [DecidableEq V]
    {pieces : J → List V} {A : Finset V} {B : Finset J} {j : J} {v : V} :
    v ∈ listPiecesInRectangle pieces A B j ↔ j ∈ B ∧ v ∈ pieces j ∧ v ∈ A := by
  by_cases active : j ∈ B <;> simp [listPiecesInRectangle,active]

/-- Within both original budgets, the rectangle mass pays for a return
cover, peeling at the two original averages, and the desired retention. -/
def HasCrossedReturnCoverWithinRectangle {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff retention : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  ∃ A : Finset (ListVertexBlockIndex paths D), A.card ≤ n ∧
    ∃ B : Finset (ListBlockIndex copies L), B.card ≤ p ∧
      ∃ deleted : Finset (ListBlockIndex copies L × ListVertexBlockIndex paths D),
        CrossedParentReturnIncidenceCover copies (listPiecesInRectangle pieces A B)
          Sigma.fst (cutoff-5) deleted ∧
        (M:ℝ)/retention + (M:ℝ)/(4*(n:ℝ))*A.card + (M:ℝ)/(4*(p:ℝ))*B.card + deleted.card ≤
          ((∑ j ∈ B, ((pieces j).toFinset ∩ A).card : ℕ):ℝ)

/-- Cover only the returns supported on the chosen rectangle. Charge
peeling to the sizes of its two supports at the original averages. -/
theorem regularization_list_frozen_full_of_supported_width_return_cover {n p cutoff retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (positive : 0 < retention)
    (certificate : HasCrossedReturnCoverWithinRectangle paths cutoff retention) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let Vertex := ListVertexBlockIndex paths D
  let Piece := ListBlockIndex copies L
  let pieces : Piece → List Vertex := listRegularizedPaths paths D L
  obtain ⟨A,vertexBudget,B,pathBudget,deleted,cover,enough⟩ := certificate
  let masked := listPiecesInRectangle pieces A B
  let erased := erasePieceIncidences masked deleted
  have pieceSimple (j : Piece) := listRegularizedPaths_simple paths simple D L j
  have maskSub (j : Piece) : (masked j).Sublist (pieces j) := listPiecesInRectangle_sublist pieces A B j
  have maskSimple (j : Piece) := (maskSub j).nodup (pieceSimple j)
  have erasedSub (j : Piece) : (erased j).Sublist (pieces j) :=
    (erasePieceIncidences_sublist masked deleted j).trans (maskSub j)
  have erasedSimple (j : Piece) := (erasedSub j).nodup (pieceSimple j)
  have copyFree : BridgeFree (Before copies) cutoff :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have maskSteps {j x y} (step : Before masked j x y) : Before copies j.fst x y :=
    listBefore_of_sublist (paths := fun i : Piece => copies i.fst)
      (splitListVertices_simple paths D j.fst (simple j.fst)) List.filter_sublist
      (listBefore_of_sublist (pieceSimple j) (maskSub j) step)
  have erasedFree : BridgeFree (Before erased) cutoff :=
    fullBridgeFree_after_crossed_parent_return_erasure (I := Fin p) (V := Vertex) Sigma.fst maskSimple
      (fun {_ _ _} => maskSteps)
      (fun {_ _ _} apart same first last => splitListPaths_disjoint apart same
        ((maskSub _).subset first) ((maskSub _).subset last)) copyFree large deleted cover
  let kept := restrictListPaths erased A B
  have keptSimple (i : B) : (kept i).Nodup := restrictListPath_nodup (erasedSimple i.val) A
  have keptFree : BridgeFree (Before kept) cutoff := restrictListPaths_fullFree erasedSimple erasedFree A B
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have keptLength (i : B) : (kept i).length ≤ L := calc
    _ = ((erased i.val).toFinset ∩ A).card := restrictListPath_length (erasedSimple i.val) A
    _ ≤ (erased i.val).length := (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
    _ ≤ (pieces i.val).length := (erasedSub i.val).length_le
    _ ≤ L := length i.val
  have keptDegree (v : A) : (occurrences (fun j => (kept j).toFinset) v).card ≤ D := by
    have degreeBound : (occurrences (fun j => (erased j).toFinset) v.val).card ≤ D := by
      refine (card_le_card ?_).trans (degree v.val)
      intro j on
      have marked := (mem_occurrences (marks := fun q : Piece => (erased q).toFinset)).mp on
      exact mem_occurrences.mpr (List.mem_toFinset.mpr ((erasedSub j).subset (List.mem_toFinset.mp marked)))
    have projected : (fun j => (kept j).toFinset) = rectanglePaths (fun j => (erased j).toFinset) A B :=
      funext (restrictListPaths_toFinset erased A B)
    rw [projected]
    exact (rectanglePaths_degree_le (fun j => (erased j).toFinset) A B v).trans degreeBound
  have onA (j : Piece) : (erased j).toFinset ⊆ A := by
    intro v present
    exact (mem_listPiecesInRectangle.mp (mem_erasePieceIncidences.mp (List.mem_toFinset.mp present)).1).2.2
  have retainedMass : (∑ j, (kept j).length) = ∑ j ∈ B, (erased j).length := by
    rw [← Finset.sum_attach B (fun j => (erased j).length)]
    refine sum_congr rfl fun j _ => ?_
    calc
      (kept j).length = ((erased j.val).toFinset ∩ A).card := restrictListPath_length (erasedSimple j.val) A
      _ = (erased j.val).toFinset.card := congrArg Finset.card (inter_eq_left.mpr (onA j.val))
      _ = (erased j.val).length := List.toFinset_card_of_nodup (erasedSimple j.val)
  have rawMass : (∑ j ∈ B, (masked j).length) = ∑ j ∈ B, ((pieces j).toFinset ∩ A).card := by
    refine sum_congr rfl fun j jIn => ?_
    rw [← List.toFinset_card_of_nodup (maskSimple j)]
    congr 1
    ext v
    change v ∈ (listPiecesInRectangle pieces A B j).toFinset ↔ v ∈ (pieces j).toFinset ∩ A
    simp only [List.mem_toFinset,mem_listPiecesInRectangle,jIn,true_and,mem_inter]
  have loss := erasePieceIncidences_mass_add_loss maskSimple B deleted
  change (∑ j ∈ B, (erased j).length) + _ = (∑ j ∈ B, (masked j).length) at loss
  rw [← retainedMass,rawMass] at loss
  have fewer : (pieceIncidences masked B ∩ deleted).card ≤ deleted.card := card_le_card inter_subset_right
  have after : (∑ j ∈ B, ((pieces j).toFinset ∩ A).card) ≤ (∑ j, (kept j).length) + deleted.card := by omega
  have keptUpper : (∑ j, (kept j).length) ≤ M := by
    rw [retainedMass]
    exact (sum_le_sum_of_subset (subset_univ B)).trans ((sum_le_sum fun j _ => (erasedSub j).length_le).trans mass.le)
  have degreeSum : (∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card) = ∑ i, (kept i).length := by
    rw [sum_occurrences]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (keptSimple i)
  apply regularization_list_frozen_after_kept_vertices (half := false) kept keptSimple keptFree
    hn hp dense long positive (univ : Finset A) (by simpa only [card_univ, Fintype.card_coe] using vertexBudget)
    (by simpa only [Fintype.card_coe] using pathBudget) keptLength keptDegree keptUpper
  simp only [card_univ,Fintype.card_coe]
  change (M:ℝ)/retention ≤ ((∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card : ℕ):ℝ) -
    (M:ℝ)/(4*(n:ℝ))*A.card - (M:ℝ)/(4*(p:ℝ))*B.card
  rw [degreeSum]
  have afterReal : ((∑ j ∈ B, ((pieces j).toFinset ∩ A).card : ℕ):ℝ) ≤
      ((∑ j, (kept j).length : ℕ):ℝ) + deleted.card := by exact_mod_cast after
  change (M:ℝ)/retention + (M:ℝ)/(4*(n:ℝ))*A.card + (M:ℝ)/(4*(p:ℝ))*B.card + deleted.card ≤
    ((∑ j ∈ B, ((pieces j).toFinset ∩ A).card : ℕ):ℝ) at enough
  linarith only [afterReal,enough]

/-- The supported cover also gives the feasible literal witness. -/
theorem regularization_list_frozen_full_distinct_of_supported_width_return_cover {n p cutoff retention : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (retentionBound : 8 ≤ retention) (certificate : HasCrossedReturnCoverWithinRectangle paths cutoff retention) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ retention*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := retention)
    paths distinct nonempty simple free (by omega) hn hp dense retentionBound
    (fun long => regularization_list_frozen_full_of_supported_width_return_cover
      paths simple free large hn hp dense long (by omega) certificate)

end OnlineReachabilityPreservers
