import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.ReverseIntersectionCopies

/-! Repair terminal returns created by consecutive arrival blocks at vertices. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

open Finset

variable {n p : ℕ}

section ArrivalBlocks

variable {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V]

private theorem partnerCopy_index {paths : I → List V} {width : ℕ} {i : I}
    {v : ListVertexBlockIndex paths width} (present : v ∈ splitListVertices paths width i) :
    v.snd.val = (predecessors (occurrences (fun r => (paths r).toFinset) v.fst) i).card/width := by
  unfold splitListVertices at present
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp present
  rfl

/-- Inside the same original vertex, earlier rows receive no later block number. -/
theorem splitListVertices_block_mono {paths : I → List V} {width : ℕ} {i j : I}
    {u v : ListVertexBlockIndex paths width} (same : u.fst = v.fst) (earlier : i ≤ j)
    (presentU : u ∈ splitListVertices paths width i) (presentV : v ∈ splitListVertices paths width j) :
    u.snd.val ≤ v.snd.val := by
  rw [partnerCopy_index presentU,partnerCopy_index presentV,same]
  apply Nat.div_le_div_right
  apply card_le_card
  intro a member
  obtain ⟨mem,previous⟩ := mem_filter.mp member
  exact mem_filter.mpr ⟨mem,previous.trans_le earlier⟩

omit [LinearOrder I] in
private theorem partnerCopy_eq {paths : I → List V} {width : ℕ}
    {u v : ListVertexBlockIndex paths width}
    (same : u.fst = v.fst) (sameBlock : u.snd.val = v.snd.val) : u = v := by
  rcases u with ⟨a,i⟩
  rcases v with ⟨b,j⟩
  change a = b at same
  subst b
  obtain rfl := Fin.ext sameBlock
  rfl

/-- An occupied block after the first requires original degree greater than the width. -/
private theorem partnerCopy_width_lt {paths : I → List V} {width : ℕ}
    {i : I} {v : ListVertexBlockIndex paths width}
    (present : v ∈ splitListVertices paths width i) (positive : 0 < v.snd.val) :
    width < (occurrences (fun r => (paths r).toFinset) v.fst).card := by
  let uses := occurrences (fun r => (paths r).toFinset) v.fst
  have atI : i ∈ uses := mem_occurrences.mpr (List.mem_toFinset.mpr (by
    rw [← splitListVertices_project paths width i]
    exact List.mem_map_of_mem present))
  have before : (predecessors uses i).card < uses.card := by
    refine (card_le_card ?_).trans_lt (card_erase_lt_of_mem atI)
    intro a h
    obtain ⟨inside,earlier⟩ := mem_filter.mp h
    exact mem_erase.mpr ⟨earlier.ne,inside⟩
  have floor : width ≤ (predecessors uses i).card := by
    by_contra! small
    have zero := Nat.div_eq_of_lt small
    rw [partnerCopy_index present] at positive
    exact (Nat.not_lt_zero 0) (zero ▸ positive)
  exact floor.trans_lt before

/-- A degree split preserves half-five exclusion when its overfull
vertices use a common original reverse-partner color on the retained rows. -/
theorem splitListVertices_halfFive_of_original_colors {p : ℕ}
    (paths : Fin p → List V) (rows : I → List V) (parent : I → Fin p)
    (originalFree : HalfBridgeFree (Before paths) 5) (free : HalfBridgeFree (Before rows) 5)
    (simple : ∀ i, (rows i).Nodup) (monotone : Monotone parent)
    (parentStep : ∀ {i x y}, Before rows i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ rows i → x ∈ rows j → False)
    (width : ℕ) (color : V → Bool)
    (selected : ∀ {v i}, width < (occurrences (fun j => (rows j).toFinset) v).card →
      v ∈ rows i → reversePartnerColor paths v (parent i) = color v) :
    HalfBridgeFree (Before (splitListVertices rows width)) 5 := by
  let copies := splitListVertices rows width
  let project (v : ListVertexBlockIndex rows width) := v.fst
  have step {i x y} (found : Before copies i x y) : Before rows i (project x) (project y) :=
    splitListVertices_step (simple i) found
  intro d cutoff b earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before rows) 4 := fun _ bound => free (bound.trans (by decide))
    have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => step)
    exact safe (by omega) b earlier
  have size : d = 3 := by omega
  subst d
  obtain ⟨same, riverBefore⟩ :=
    free.project_half_five_terminal_collision project (fun {_ _ _} => step) b earlier
  change (b.vertex 2).fst = (b.vertex 4).fst at same
  have earlierBlock := splitListVertices_block_mono same.symm riverBefore.le b.riverStep.2.1 (b.arcStep 1).2.1
  have blocksDifferent : (b.vertex 4).snd.val ≠ (b.vertex 2).snd.val := by
    intro eq
    exact (by decide : (4:Fin 5) ≠ 2) (b.distinctVertices (partnerCopy_eq same.symm eq))
  have distinctOrdered : (b.vertex 4).snd.val < (b.vertex 2).snd.val := earlierBlock.lt_of_ne blocksDifferent
  have riverBeforeReturn : b.river < b.arc 2 := lt_of_not_ge fun closer =>
    distinctOrdered.not_ge (splitListVertices_block_mono same closer (b.arcStep 2).1 b.riverStep.2.1)
  let corner := project (b.vertex 2)
  let other := project (b.vertex 3)
  have heavy : width < (occurrences (fun j => (rows j).toFinset) corner).card :=
    partnerCopy_width_lt (b.arcStep 2).1 ((Nat.zero_le ((b.vertex 4).snd.val)).trans_lt distinctOrdered)
  have forward : Before rows (b.arc 3) other corner := by
    change Before rows (b.arc 3) (b.vertex 3).fst (b.vertex 2).fst
    rw [same]
    exact step (b.arcStep 3)
  have backward : Before rows (b.arc 2) corner other := step (b.arcStep 2)
  have arrives : b.arc 3 < b.arc 2 := earlier.trans riverBeforeReturn
  have different : parent (b.arc 3) ≠ parent (b.arc 2) :=
    fun eq => apart arrives.ne eq forward.1 backward.2.1
  have linked : LaterReversePartner paths corner (parent (b.arc 3)) (parent (b.arc 2)) :=
    ⟨lt_of_le_of_ne (monotone arrives.le) different,other,parentStep forward,parentStep backward⟩
  exact reversePartnerColor_ne originalFree (by decide) linked
    ((selected heavy forward.2.1).trans (selected heavy backward.1).symm)

end ArrivalBlocks

/-- A parent vertex and a block number determine its copied vertex. -/
theorem vertexBlock_eq_of_same_label {paths : Fin p → List (Fin n)} {width : ℕ}
    {u v : ListVertexBlockIndex paths width}
    (same : u.fst = v.fst) (sameBlock : u.snd.val = v.snd.val) : u = v :=
  partnerCopy_eq same sameBlock

/-- An occupied block after the first requires original degree greater than the width. -/
theorem degree_width_lt_of_positive_block {paths : Fin p → List (Fin n)} {width : ℕ}
    {i : Fin p} {v : ListVertexBlockIndex paths width}
    (present : v ∈ splitListVertices paths width i) (positive : 0 < v.snd.val) :
    width < (occurrences (fun r => (paths r).toFinset) v.fst).card :=
  partnerCopy_width_lt present positive

/-- Keep all occurrences of low-degree vertices and one color at each
vertex exceeding the original width. -/
noncomputable def halfFiveDegreeRepair (paths : Fin p → List (Fin n)) (width : ℕ) (color : Bool) (i : Fin p) :
    List (ListVertexBlockIndex paths width) :=
  (splitListVertices paths width i).filter fun v => decide (
    (occurrences (fun r => (paths r).toFinset) v.fst).card ≤ width ∨
      reversePartnerColor paths v.fst i ≠ color)

/-- Repair keeps a copied incidence at light vertices or in the retained color. -/
theorem mem_halfFiveDegreeRepair {paths : Fin p → List (Fin n)} {width : ℕ} {color : Bool} {i : Fin p}
    {v : ListVertexBlockIndex paths width} :
    v ∈ halfFiveDegreeRepair paths width color i ↔ v ∈ splitListVertices paths width i ∧
      ((occurrences (fun r => (paths r).toFinset) v.fst).card ≤ width ∨
        reversePartnerColor paths v.fst i ≠ color) := by
  simp [halfFiveDegreeRepair]

/-- Consecutive arrival blocks make the earlier arc of a terminal return
enter the split vertex. Keeping either color at overfull vertices therefore
blocks both copied endpoints from surviving in such a return. -/
theorem halfFiveDegreeRepair_halfFree (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (width : ℕ) (color : Bool) :
    HalfBridgeFree (Before (halfFiveDegreeRepair paths width color)) 5 := by
  let copies := splitListVertices paths width
  let repaired := halfFiveDegreeRepair paths width color
  let project (v : ListVertexBlockIndex paths width) := v.fst
  have copyStep {i x y} (h : Before repaired i x y) : Before copies i x y :=
    listBefore_of_sublist (splitListVertices_simple paths width i (simple i)) List.filter_sublist h
  have step {i x y} (h : Before repaired i x y) : Before paths i (project x) (project y) :=
    splitListVertices_step (simple i) (copyStep h)
  intro d cutoff b earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
    have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => step)
    exact safe (by omega) b earlier
  have size : d = 3 := by omega
  subst d
  obtain ⟨same, riverBefore⟩ :=
    free.project_half_five_terminal_collision project (fun {_ _ _} => step) b earlier
  change (b.vertex 2).fst = (b.vertex 4).fst at same
  have atReturn := (mem_halfFiveDegreeRepair.mp (b.arcStep 2).1).1
  have atLast := mem_halfFiveDegreeRepair.mp (b.arcStep 3).2.1
  have earlierBlock := splitListVertices_block_mono same.symm riverBefore.le
    (mem_halfFiveDegreeRepair.mp b.riverStep.2.1).1 (mem_halfFiveDegreeRepair.mp (b.arcStep 1).2.1).1
  have blocksDifferent : (b.vertex 4).snd.val ≠ (b.vertex 2).snd.val := by
    intro eq
    exact (by decide : (4:Fin 5) ≠ 2) (b.distinctVertices (vertexBlock_eq_of_same_label same.symm eq))
  have distinctOrdered : (b.vertex 4).snd.val < (b.vertex 2).snd.val := earlierBlock.lt_of_ne blocksDifferent
  have riverBeforeReturn : b.river < b.arc 2 := lt_of_not_ge fun closer =>
    distinctOrdered.not_ge (splitListVertices_block_mono same closer atReturn
      (mem_halfFiveDegreeRepair.mp b.riverStep.2.1).1)
  have targetHeavy := degree_width_lt_of_positive_block atReturn
    ((Nat.zero_le ((b.vertex 4).snd.val)).trans_lt distinctOrdered)
  have atReturnColor := (mem_halfFiveDegreeRepair.mp (b.arcStep 2).1).2.resolve_left
    (not_le_of_gt targetHeavy)
  have atLastColor₀ := atLast.2.resolve_left (fun small => by
    let degree (w : Fin n) := (occurrences (fun r => (paths r).toFinset) w).card
    have atFour : degree (b.vertex 4).fst ≤ width := small
    have atTwo : width < degree (b.vertex 2).fst := targetHeavy
    have sizeEq : degree (b.vertex 2).fst = degree (b.vertex 4).fst := congrArg degree same
    exact atTwo.not_ge (sizeEq.symm ▸ atFour))
  have atLastColor : reversePartnerColor paths (project (b.vertex 2)) (b.arc 3) ≠ color := by
    change reversePartnerColor paths (b.vertex 2).fst (b.arc 3) ≠ color
    rw [same]
    exact atLastColor₀
  have incoming : Before paths (b.arc 3) (project (b.vertex 3)) (project (b.vertex 2)) := by
    change Before paths (b.arc 3) (b.vertex 3).fst (b.vertex 2).fst
    rw [same]
    exact step (b.arcStep 3)
  have linked : LaterReversePartner paths (project (b.vertex 2)) (b.arc 3) (b.arc 2) :=
    ⟨earlier.trans riverBeforeReturn,project (b.vertex 3),incoming,step (b.arcStep 2)⟩
  have sameColor {x y c : Bool} (left : x ≠ c) (right : y ≠ c) : x = y := by
    cases x <;> cases y <;> cases c <;> simp_all
  exact reversePartnerColor_ne free (by decide) linked (sameColor atLastColor atReturnColor)

end OnlineReachabilityPreservers
