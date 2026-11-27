import OnlineReachabilityPreservers.CutConflictMatching

/-! Count the half-five conflicts remaining inside a chosen support rectangle. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- The actual incidences on the selected degree copies and path pieces. -/
noncomputable def degreeFirstRectangleIncidences {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ)
    (vertices : Finset (ListVertexBlockIndex paths D))
    (pieces : Finset (ListBlockIndex (splitListVertices paths D) L)) :
    Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) :=
  (pieceIncidences (listRegularizedPaths paths D L) univ).filter fun a =>
    a.1 ∈ pieces ∧ a.2 ∈ vertices

set_option maxHeartbeats 1200000 in
/-- Peel a repaired rectangle using the original averages and its actual
vertex and path counts. -/
theorem regularization_list_frozen_half_five_after_rectangle_cover {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (A : Finset (ListVertexBlockIndex paths (4*(∑ i, (paths i).length)/n))) (vertexBudget : A.card ≤ n)
    (B : Finset (ListBlockIndex (splitListVertices paths (4*(∑ i, (paths i).length)/n))
      (4*(∑ i, (paths i).length)/p))) (pathBudget : B.card ≤ p)
    (cover : Finset (ListBlockIndex (splitListVertices paths (4*(∑ i, (paths i).length)/n))
      (4*(∑ i, (paths i).length)/p) × ListVertexBlockIndex paths (4*(∑ i, (paths i).length)/n)))
    (coverSub : let M := ∑ i, (paths i).length
      cover ⊆ degreeFirstRectangleIncidences paths (4*M/n) (4*M/p) A B)
    (repairFree : let M := ∑ i, (paths i).length
      let raw := listRegularizedPaths paths (4*M/n) (4*M/p)
      let support := degreeFirstRectangleIncidences paths (4*M/n) (4*M/p) A B
      HalfBridgeFree (Before (erasePieceIncidences raw (pieceIncidences raw univ \ (support \ cover)))) 5)
    (enough : let M := ∑ i, (paths i).length
      (M:ℝ)/5000+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+cover.card ≤
        (degreeFirstRectangleIncidences paths (4*M/n) (4*M/p) A B).card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  let raw := listRegularizedPaths paths D L
  let all := pieceIncidences raw univ
  let support := degreeFirstRectangleIncidences paths D L A B
  have inside {j : J} {v : V} : (j,v) ∈ support ↔ (j,v) ∈ all ∧ j ∈ B ∧ v ∈ A := by
    exact mem_filter
  let deleted := all \ (support \ cover)
  let repaired := erasePieceIncidences raw deleted
  let rows (j : B) := repaired j.val
  let K := ∑ j : B, (rows j).length
  have rawSimple (j : J) : (raw j).Nodup := listRegularizedPaths_simple paths simple D L j
  have repairSimple (j : J) : (repaired j).Nodup :=
    (erasePieceIncidences_sublist raw deleted j).nodup (rawSimple j)
  have rowSimple (i : B) : (rows i).Nodup := repairSimple i.val
  have rowFree : HalfBridgeFree (Before rows) 5 := by
    intro k small b earlier
    exact repairFree small (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) earlier
  have exactIncidences : pieceIncidences repaired B = support \ cover := by
    ext a
    rcases a with ⟨j,v⟩
    constructor
    · intro present
      obtain ⟨_,onRow⟩ := mem_pieceIncidences.mp present
      obtain ⟨old,kept⟩ := mem_erasePieceIncidences.mp onRow
      by_contra! outside
      exact kept (mem_sdiff.mpr ⟨mem_pieceIncidences.mpr ⟨mem_univ _,old⟩,outside⟩)
    · intro present
      obtain ⟨inRaw,onPiece,_⟩ := inside.mp (mem_sdiff.mp present).1
      refine mem_pieceIncidences.mpr ⟨onPiece,mem_erasePieceIncidences.mpr ⟨(mem_pieceIncidences.mp inRaw).2,?_⟩⟩
      exact fun erased => (mem_sdiff.mp erased).2 present
  have vertexSupport {j : B} {v : V} (on : v ∈ rows j) : v ∈ A := by
    have incident : (j.val,v) ∈ pieceIncidences repaired B := mem_pieceIncidences.mpr ⟨j.property,on⟩
    rw [exactIncidences] at incident
    exact (inside.mp (mem_sdiff.mp incident).1).2.2
  have rowSum : K = ∑ j ∈ B, (repaired j).length := sum_attach B (fun j => (repaired j).length)
  have exactK : K+cover.card = support.card := by
    rw [rowSum,← pieceIncidences_card repairSimple B,exactIncidences]
    exact card_sdiff_add_card_eq_card coverSub
  have degrees : (∑ v ∈ A, (occurrences (fun i => (rows i).toFinset) v).card) = K := by
    let weight (v : V) := (occurrences (fun i => (rows i).toFinset) v).card
    have zero {v : V} (outside : v ∉ A) : weight v = 0 := by
      apply card_eq_zero.mpr
      ext j
      simp only [notMem_empty,iff_false]
      intro on
      have present : v ∈ rows j :=
        List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (rows i).toFinset)).mp on)
      exact outside (vertexSupport present)
    calc
      _ = ∑ v : V, weight v := sum_subset (subset_univ _) (fun v _ => zero)
      _ = ∑ j : B, (rows j).toFinset.card := sum_occurrences _
      _ = K := sum_congr rfl (fun j _ => List.toFinset_card_of_nodup (rowSimple j))
  obtain ⟨rawMass,rawLength,rawDegree⟩ :=
    regularization_list_mass_caps paths simple D L (four_average_width hn dense).1 (four_average_width hp long).1
  have length (j : B) : (rows j).length ≤ L :=
    (erasePieceIncidences_sublist raw deleted j.val).length_le.trans (rawLength j.val)
  have degree (v : V) : (occurrences (fun i => (rows i).toFinset) v).card ≤ D := by
    refine (card_le_card_of_injOn Subtype.val ?_ ?_).trans (rawDegree v)
    · intro j on
      have present : v ∈ rows j :=
        List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (rows i).toFinset)).mp on)
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_erasePieceIncidences.mp present).1)
    · intro j _ k _ eq
      exact Subtype.ext eq
  have upper : K ≤ M := calc
    _ = ∑ j ∈ B, (repaired j).length := rowSum
    _ ≤ ∑ j ∈ B, (raw j).length :=
      sum_le_sum (fun j _ => (erasePieceIncidences_sublist raw deleted j).length_le)
    _ ≤ ∑ j : J, (raw j).length := sum_le_sum_of_subset (subset_univ B)
    _ = M := rawMass
  refine regularization_list_frozen_after_kept_vertices (half := true) (k := 5) (retention := 5000)
    rows rowSimple rowFree hn hp dense long (by decide) A vertexBudget
    (by simpa only [Fintype.card_coe] using pathBudget) length degree upper ?_
  change (M:ℝ)/5000 ≤
    ((∑ v ∈ A, (occurrences (fun i : B => (rows i).toFinset) v).card : ℕ):ℝ)-
      (M:ℝ)/(4*(n:ℝ))*A.card-(M:ℝ)/(4*(p:ℝ))*(Fintype.card B:ℝ)
  rw [degrees,Fintype.card_coe]
  change (M:ℝ)/5000+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+cover.card ≤
    (support.card:ℝ) at enough
  have actual : (K:ℝ)+(cover.card:ℝ) = (support.card:ℝ) := by exact_mod_cast exactK
  linarith only [enough,actual]

set_option maxHeartbeats 1200000 in
/-- A retained rectangle needs to cover only the conflicts between its own
incidences. Charge its actual row and vertex counts when peeling. -/
theorem regularization_list_frozen_half_five_of_degree_first_rectangle {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let L := 4*M/p
      ∃ A : Finset (ListVertexBlockIndex paths D), A.card ≤ n ∧
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L), B.card ≤ p ∧
        ∀ matching, CutMatching (DegreeFirstCutConflict paths D L)
          (degreeFirstRectangleIncidences paths D L A B) matching →
          (M:ℝ)/5000+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+matching.card ≤
            (degreeFirstRectangleIncidences paths D L A B).card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  obtain ⟨A,vertexBudget,B,pathBudget,matchingBound⟩ := bound
  let support := degreeFirstRectangleIncidences paths D L A B
  let rank (a : J × V) : ℕ := a.1.fst.val
  have increases {a b : J × V} (edge : DegreeFirstCutConflict paths D L a b) : rank a < rank b :=
    (edge.partner simple).1
  obtain ⟨cover,coverSub,matching,count,covers,matched⟩ :=
    exists_cut_cover_and_matching (DegreeFirstCutConflict paths D L) rank (fun {_ _} => increases)
      (fun {_ _ _} => DegreeFirstCutConflict.out_unique simple free) support
  let raw := listRegularizedPaths paths D L
  let all := pieceIncidences raw univ
  let deleted := all \ (support \ cover)
  have deletedCover {a b} (edge : DegreeFirstCutConflict paths D L a b) :
      a ∈ deleted ∨ b ∈ deleted := by
    have aRaw : a ∈ all := mem_pieceIncidences.mpr ⟨mem_univ _,edge.left_mem⟩
    have bRaw : b ∈ all := mem_pieceIncidences.mpr ⟨mem_univ _,edge.right_mem⟩
    by_cases aKept : a ∈ support \ cover
    · have bNot : b ∉ support \ cover := by
        intro bKept
        exact (covers a (mem_sdiff.mp aKept).1 b (mem_sdiff.mp bKept).1 edge).elim
          (mem_sdiff.mp aKept).2 (mem_sdiff.mp bKept).2
      exact Or.inr (mem_sdiff.mpr ⟨bRaw,bNot⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨aRaw,aKept⟩)
  refine regularization_list_frozen_half_five_after_rectangle_cover paths simple hn hp dense long
    A vertexBudget B pathBudget cover coverSub
    (eraseDegreeFirstConflicts_halfFree paths simple free D L deleted sdiff_subset (fun {_ _} => deletedCover)) ?_
  rw [count]
  exact matchingBound matching matched

end OnlineReachabilityPreservers
