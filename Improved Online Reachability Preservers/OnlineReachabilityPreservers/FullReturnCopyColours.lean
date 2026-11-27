import OnlineReachabilityPreservers.FullReturnRadius
import OnlineReachabilityPreservers.CommonPartitionCleaning

/-! Refine vertex copies to separate a corner of each short crossed return. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

variable {I J V C : Type*}

/-- Tag every vertex occurrence with the chosen colour on its row. -/
def colourListRows (rows : I → List V) (colour : I → V → C) (i : I) : List (V ×ₗ C) :=
  (rows i).map fun v => toLex (v,colour i v)

theorem colourListRows_length (rows : I → List V) (colour : I → V → C) (i : I) :
    (colourListRows rows colour i).length = (rows i).length := by
  simp [colourListRows]

theorem colourListRows_simple (rows : I → List V) (colour : I → V → C)
    {i : I} (simple : (rows i).Nodup) : (colourListRows rows colour i).Nodup :=
  simple.map (fun _ _ equal => congrArg (fun w => (ofLex w).1) equal)

theorem mem_colourListRows {rows : I → List V} {colour : I → V → C} {i : I} {w : V ×ₗ C} :
    w ∈ colourListRows rows colour i ↔ (ofLex w).1 ∈ rows i ∧ (ofLex w).2 = colour i (ofLex w).1 := by
  constructor
  · intro on
    obtain ⟨v,inside,rfl⟩ := List.mem_map.mp on
    exact ⟨inside,rfl⟩
  · rintro ⟨on,equal⟩
    exact List.mem_map.mpr ⟨(ofLex w).1,on,ofLex.injective (Prod.ext rfl equal.symm)⟩

section Comparison

variable [DecidableEq V] [DecidableEq C]

private theorem colourListRows_step_project {rows : I → List V} {colour : I → V → C}
    {i : I} {u v : V ×ₗ C} (simple : (rows i).Nodup)
    (step : Before (colourListRows rows colour) i u v) : Before rows i (ofLex u).1 (ofLex v).1 := by
  let project (w : V ×ₗ C) := (ofLex w).1
  have undo (j : I) : (colourListRows rows colour j).map project = rows j := by
    simp [colourListRows,project,List.map_map,Function.comp_def]
  have forward := listBefore_map project ((undo i).symm ▸ simple) step
  unfold SourceAudit.BeforeIn at forward ⊢
  simpa only [undo] using forward

private theorem colourListRows_step_lift {rows : I → List V} (colour : I → V → C)
    {i : I} {x y : V} (simple : (rows i).Nodup) (step : Before rows i x y) :
    Before (colourListRows rows colour) i (toLex (x,colour i x)) (toLex (y,colour i y)) := by
  let tag (v : V) := toLex (v,colour i v)
  have same : (rows i).map tag = colourListRows rows colour i := rfl
  have forward := listBefore_map tag (same.symm ▸ colourListRows_simple rows colour simple) step
  unfold SourceAudit.BeforeIn at forward ⊢
  simpa only [same] using forward

/-- Every original tested return has a corner at which its two
occurrences use different colours. This is expressed as the failure
of a single assignment to all corners that agrees with their row tags. -/
def NoColourCompatibleCrossedReturn (parents : I → List V) (pieces : J → List V)
    (parent : J → I) (colour : I → V → C) (radius : ℕ) : Prop :=
  ∀ ⦃i j : J⦄ {d : ℕ}, i ≠ j → parent i = parent j → d ≤ radius →
    ∀ (v : Fin (d+1) → V) (a : Fin d → J),
      (∀ t, parent i ≠ parent (a t)) → Function.Injective (parent ∘ a) →
      v 0 ∈ pieces i → v (Fin.last d) ∈ pieces j →
      Before parents (parent i) (v (Fin.last d)) (v 0) →
      (∀ t, Before pieces (a t) (v t.castSucc) (v t.succ)) →
      ∀ c : Fin (d+1) → C,
        c 0 = colour (parent i) (v 0) → c (Fin.last d) = colour (parent j) (v (Fin.last d)) →
        (∀ t, c t.castSucc = colour (parent (a t)) (v t.castSucc) ∧
          c t.succ = colour (parent (a t)) (v t.succ)) → False

/-- Projection and lifting give an exact test for the returns after
copy refinement. A return survives precisely when all its corners can
use the same tag on both occurrences. -/
theorem noCrossedParentReturnUpTo_colourListRows_iff
    {parents : I → List V} {pieces : J → List V} (parent : J → I) (colour : I → V → C) (radius : ℕ)
    (parentSimple : ∀ i, (parents i).Nodup) (pieceSimple : ∀ i, (pieces i).Nodup) :
    NoCrossedParentReturnUpTo (colourListRows parents colour) (colourListRows pieces (colour ∘ parent))
      parent radius ↔ NoColourCompatibleCrossedReturn parents pieces parent colour radius := by
  constructor
  · intro safe i j d apart same short v a other injective first last backward along c start finish agrees
    let w (t : Fin (d+1)) := toLex (v t,c t)
    have finishOnParent : c (Fin.last d) = colour (parent i) (v (Fin.last d)) :=
      finish.trans (congrArg (fun k => colour k (v (Fin.last d))) same.symm)
    refine safe apart same short w a other injective (mem_colourListRows.mpr ⟨first,start⟩)
      (mem_colourListRows.mpr ⟨last,finish⟩) ?_ ?_
    · simpa only [w,start,finishOnParent] using colourListRows_step_lift colour (parentSimple (parent i)) backward
    · intro t
      simpa only [w,(agrees t).1,(agrees t).2,Function.comp_apply] using
        colourListRows_step_lift (colour ∘ parent) (pieceSimple (a t)) (along t)
  · intro safe i j d apart same short w a other injective first last backward along
    let v (t : Fin (d+1)) := (ofLex (w t)).1
    let c (t : Fin (d+1)) := (ofLex (w t)).2
    exact safe apart same short v a other injective (mem_colourListRows.mp first).1 (mem_colourListRows.mp last).1
      (colourListRows_step_project (parentSimple (parent i)) backward)
      (fun t => colourListRows_step_project (pieceSimple (a t)) (along t)) c
      (mem_colourListRows.mp first).2 (mem_colourListRows.mp last).2
      (fun t => ⟨(mem_colourListRows.mp (along t).1).2,(mem_colourListRows.mp (along t).2.1).2⟩)

/-- A separating choice of colours on the parent occurrences repairs
the width pieces at the same full cutoff. Every incidence is retained. -/
theorem fullBridgeFree_colourListPieces [LinearOrder I]
    {parents : I → List V} {pieces : J → List V} {cutoff : ℕ} (parent : J → I) (colour : I → V → C)
    (simple : ∀ i, (parents i).Nodup) (sub : ∀ j, (pieces j).Sublist (parents (parent j)))
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (free : BridgeFree (Before parents) cutoff) (large : 7 ≤ cutoff)
    (safe : NoColourCompatibleCrossedReturn parents pieces parent colour (cutoff-5)) :
    BridgeFree (Before (colourListRows pieces (colour ∘ parent))) cutoff := by
  let taggedParents := colourListRows parents colour
  let taggedPieces := colourListRows pieces (colour ∘ parent)
  have parentFree : BridgeFree (Before taggedParents) cutoff :=
    free.split_list_vertices_any (fun w : V ×ₗ C => (ofLex w).1)
      (fun {i _ _} step => colourListRows_step_project (simple i) step)
  have step {j x y} (forward : Before taggedPieces j x y) : Before taggedParents (parent j) x y :=
    listBefore_of_sublist (paths := taggedParents ∘ parent) (cut := taggedPieces)
      (colourListRows_simple parents colour (simple (parent j))) ((sub j).map _) forward
  refine fullBridgeFree_of_short_parent_returns parent (fun {_ _ _} => step) ?_ ?_ parentFree large
  · intro i j x apart same first last
    exact disjoint apart same (mem_colourListRows.mp first).1 (mem_colourListRows.mp last).1
  · exact (noCrossedParentReturnUpTo_colourListRows_iff parent colour (cutoff-5) simple
      (fun j => (sub j).nodup (simple (parent j)))).mpr safe

end Comparison

open Finset

/-- Tagging incidences cannot increase the degree of a vertex copy. -/
theorem colourListRows_degree_le [Fintype I] [DecidableEq V] [DecidableEq C]
    (rows : I → List V) (colour : I → V → C) (w : V ×ₗ C) :
    (occurrences (fun i => (colourListRows rows colour i).toFinset) w).card ≤
      (occurrences (fun i => (rows i).toFinset) (ofLex w).1).card := by
  apply card_le_card
  intro i on
  simp only [mem_occurrences,List.mem_toFinset] at on ⊢
  exact (mem_colourListRows.mp on).1

/-- Refine the standard vertex copies without changing the path width
blocks. The short-return test must pass and the occupied refined
vertices must fit within four thirds of the original vertex budget. -/
def HasCrossedReturnWidthColours {n p : ℕ} (paths : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  ∃ (q : ℕ) (colour : Fin p → ListVertexBlockIndex paths D → Fin q),
    NoColourCompatibleCrossedReturn copies pieces Sigma.fst colour (cutoff-5) ∧
      3*(activeListVertices (colourListRows pieces (colour ∘ Sigma.fst))).card ≤ 4*n

/-- With room for the refined vertex support, separating return corners
keeps the whole mass before trimming. Frozen cleaning retains one
sixteenth of the input with both original budgets and the same cutoff. -/
theorem regularization_list_frozen_full_of_width_return_colours {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasCrossedReturnWidthColours paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',va,p',pa,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree (by omega) hn hp dense long low
    exact ⟨n',va,p',pa,clean,cleanSimple,cleanFree,by omega,upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let W := ListVertexBlockIndex paths D
  let copies := splitListVertices paths D
  let J := ListBlockIndex copies L
  let pieces : J → List W := listRegularizedPaths paths D L
  obtain ⟨q,colour,safe,vertexRoom⟩ := repair (lt_of_not_ge low)
  let tags : J → List (W ×ₗ Fin q) := colourListRows pieces (colour ∘ Sigma.fst)
  have parentSimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have fullParents : BridgeFree (Before copies) cutoff :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have taggedFree : BridgeFree (Before tags) cutoff :=
    fullBridgeFree_colourListPieces Sigma.fst colour parentSimple
      (fun _ => List.filter_sublist) (fun {_ _ _} => splitListPaths_disjoint) fullParents large safe
  have taggedSimple (j : J) : (tags j).Nodup :=
    colourListRows_simple pieces _ (listRegularizedPaths_simple paths simple D L j)
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,rowBudget,_⟩ := four_average_width hp long
  have rawCount := (regularization_list_counts paths simple dPos lPos).2
  simp only [Fintype.card_fin] at rawCount
  change Fintype.card J ≤ p+M/L at rawCount
  have smallIndex : (activeListIndices tags).card ≤ Fintype.card J := card_le_univ _
  have rowRoom : 3*(activeListIndices tags).card ≤ 4*p := by
    change 3*(M/L) ≤ p at rowBudget
    omega
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  apply regularization_list_frozen_after_caps_with_room (half := false) (activeListPaths tags)
    (activeListPaths_simple tags taggedSimple) (activeListPaths_admissible tags taggedSimple taggedFree)
    hn hp dense long
  · rw [Fintype.card_coe]
    simpa only [tags,pieces,listRegularizedPaths] using vertexRoom
  · simpa only [Fintype.card_coe] using rowRoom
  · intro j
    rw [activeListPaths_length tags taggedSimple,colourListRows_length]
    exact length j.val
  · intro v
    exact (activeListPaths_degree_le tags v).trans
      ((colourListRows_degree_le pieces (colour ∘ Sigma.fst) v.val).trans (degree (ofLex v.val).1))
  · rw [activeListPaths_mass tags taggedSimple]
    simp_rw [tags,colourListRows_length]
    exact mass

/-- The same return separation gives a feasible literal cleaning witness. -/
theorem regularization_list_frozen_full_distinct_of_width_return_colours {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (repair : 8*max n p < (∑ i, (paths i).length) → HasCrossedReturnWidthColours paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 16*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 16)
    paths distinct nonempty simple free (by omega) hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_width_return_colours paths simple free large hn hp dense long repair)

end OnlineReachabilityPreservers
