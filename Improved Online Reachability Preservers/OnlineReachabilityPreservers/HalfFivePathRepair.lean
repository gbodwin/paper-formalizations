import OnlineReachabilityPreservers.FrozenHalfFourConflicts

/-! Repair opposite intersections that cross a width cut in one row. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

variable {p : ℕ} {V J : Type*} [DecidableEq V]

/-- At a common corner, a reverse comparison crosses a cut in one parent
and survives inside a piece of the other parent. The edge follows arrival order. -/
def OppositeWidthConflict (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) (a b : J × V) : Prop :=
  a.2 = b.2 ∧ parent a.1 < parent b.1 ∧ ∃ x,
    ((∃ i : J, i ≠ a.1 ∧ parent i = parent a.1 ∧ x ∈ pieces i ∧ a.2 ∈ pieces a.1 ∧
        Before paths (parent a.1) x a.2 ∧ Before pieces b.1 b.2 x) ∨
      (∃ j : J, j ≠ b.1 ∧ parent j = parent b.1 ∧ x ∈ pieces j ∧ b.2 ∈ pieces b.1 ∧
        Before pieces a.1 x a.2 ∧ Before paths (parent b.1) b.2 x))

theorem OppositeWidthConflict.left_mem {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : OppositeWidthConflict paths pieces parent a b) :
    a.2 ∈ pieces a.1 := by
  rcases edge with ⟨_,_,_,⟨_,_,_,_,on,_,_⟩ | ⟨_,_,_,_,_,on,_⟩⟩
  · exact on
  · exact on.2.1

theorem OppositeWidthConflict.right_mem {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : OppositeWidthConflict paths pieces parent a b) :
    b.2 ∈ pieces b.1 := by
  rcases edge with ⟨_,_,_,⟨_,_,_,_,_,_,on⟩ | ⟨_,_,_,_,on,_,_⟩⟩
  · exact on.1
  · exact on

theorem OppositeWidthConflict.partner {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : OppositeWidthConflict paths pieces parent a b)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y) :
    LaterReversePartner paths a.2 (parent a.1) (parent b.1) := by
  rcases edge with ⟨same,arrival,x,⟨_,_,_,_,_,forward,reverse⟩ | ⟨_,_,_,_,_,forward,reverse⟩⟩
  · exact ⟨arrival,x,forward,same.symm ▸ steps reverse⟩
  · exact ⟨arrival,x,steps forward,same.symm ▸ reverse⟩

theorem OppositeWidthConflict.out_unique {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b c : J × V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ab : OppositeWidthConflict paths pieces parent a b) (ac : OppositeWidthConflict paths pieces parent a c) :
    b = c := by
  have label := laterReversePartner_unique free three (ab.partner (fun {_ _ _} => steps))
    (ac.partner (fun {_ _ _} => steps))
  have vertex : b.2 = c.2 := ab.1.symm.trans ac.1
  have piece : b.1 = c.1 := by
    by_contra different
    exact apart different label ab.right_mem (vertex.symm ▸ ac.right_mem)
  exact Prod.ext piece vertex

/-- Covering the opposite comparisons that cross a cut preserves half
exclusion through size five after splitting the paths. -/
theorem eraseOppositeWidthConflicts_halfFree [LinearOrder J] {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} (free : HalfBridgeFree (Before paths) 5) (simple : ∀ i, (pieces i).Nodup)
    (monotone : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (deleted : Finset (J × V))
    (covered : ∀ {a b}, OppositeWidthConflict paths pieces parent a b → a ∈ deleted ∨ b ∈ deleted) :
    HalfBridgeFree (Before (erasePieceIncidences pieces deleted)) 5 := by
  let clean := erasePieceIncidences pieces deleted
  have raw {i x y} (step : Before clean i x y) : Before pieces i x y :=
    listBefore_of_sublist (simple i) (erasePieceIncidences_sublist pieces deleted i) step
  have contained {i : J} {x : V} (on : x ∈ clean i) : x ∈ pieces i :=
    (mem_erasePieceIncidences.mp on).1
  have lift {i x y} (step : Before clean i x y) : Before paths (parent i) x y := steps (raw step)
  have together {i j q x y} (same : parent i = parent j) (other : parent i ≠ parent q)
      (xy : Before paths (parent i) x y) (yx : Before clean q y x)
      (left : x ∈ clean i) (right : y ∈ clean j) : i = j := by
    by_contra different
    rcases lt_or_gt_of_ne other with earlier | later
    · have conflict : OppositeWidthConflict paths pieces parent (j,y) (q,y) :=
        ⟨rfl,same ▸ earlier,x,Or.inl ⟨i,different,same,contained left,contained right,same ▸ xy,raw yx⟩⟩
      exact (covered conflict).elim (mem_erasePieceIncidences.mp right).2 (mem_erasePieceIncidences.mp yx.1).2
    · have conflict : OppositeWidthConflict paths pieces parent (q,x) (i,x) :=
        ⟨rfl,later,y,Or.inr ⟨j,fun eq => different eq.symm,same.symm,contained right,contained left,raw yx,xy⟩⟩
      exact (covered conflict).elim (mem_erasePieceIncidences.mp yx.2.1).2 (mem_erasePieceIncidences.mp left).2
  intro d cutoff bridge earlier
  let old := listBridge_after_opposite_safe_split_through_five parent (fun {_ _ _} => lift)
    (fun {_ _ _} diff same one two => apart diff same (contained one) (contained two))
    (fun _ {_ _ _ _} diff one two => no_parallel_list_steps free (by decide) diff one two)
    (fun _ {_ _ _ _ _} => together) (by omega) bridge
  exact free cutoff old (lt_of_le_of_ne (monotone earlier.le) (old.river_ne_arc _).symm)

variable [Fintype J] [Fintype V]

/-- Incidences that participate in a crossed opposite comparison. -/
noncomputable def oppositeWidthConflictIncidences (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) : Finset (J × V) := by
  classical
  exact univ.filter fun a => (∃ b, OppositeWidthConflict paths pieces parent a b) ∨
    (∃ b, OppositeWidthConflict paths pieces parent b a)

/-- Remove one color on the incidences that can make a crossed comparison. -/
noncomputable def oppositeWidthDeletion (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) (color : Bool) : Finset (J × V) :=
  (oppositeWidthConflictIncidences paths pieces parent).filter fun a =>
    reversePartnerColor paths a.2 (parent a.1) = color

theorem oppositeWidthDeletion_covers {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (edge : OppositeWidthConflict paths pieces parent a b) (color : Bool) :
    a ∈ oppositeWidthDeletion paths pieces parent color ∨ b ∈ oppositeWidthDeletion paths pieces parent color := by
  classical
  have aIn : a ∈ oppositeWidthConflictIncidences paths pieces parent := by
    unfold oppositeWidthConflictIncidences
    exact mem_filter.mpr ⟨mem_univ _,Or.inl ⟨b,edge⟩⟩
  have bIn : b ∈ oppositeWidthConflictIncidences paths pieces parent := by
    unfold oppositeWidthConflictIncidences
    exact mem_filter.mpr ⟨mem_univ _,Or.inr ⟨a,edge⟩⟩
  have opposite := reversePartnerColor_ne free three (edge.partner (fun {_ _ _} => steps))
  let colA := reversePartnerColor paths a.2 (parent a.1)
  let colB := reversePartnerColor paths b.2 (parent b.1)
  have ne : colA ≠ colB := by simpa only [colA,colB,← edge.1] using opposite
  have choose {x y c : Bool} (ne : x ≠ y) : x = c ∨ y = c := by
    cases x <;> cases y <;> cases c <;> simp_all
  rcases choose (c := color) ne with selectA | selectB
  · exact Or.inl (mem_filter.mpr ⟨aIn,selectA⟩)
  · exact Or.inr (mem_filter.mpr ⟨bIn,selectB⟩)

/-- One deletion color contains at most half of the implicated incidences. -/
theorem oppositeWidthDeletion_small (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) :
    ∃ c : Bool, 2*(oppositeWidthDeletion paths pieces parent c).card ≤
      (oppositeWidthConflictIncidences paths pieces parent).card := by
  let conflicts := oppositeWidthConflictIncidences paths pieces parent
  let remove := oppositeWidthDeletion paths pieces parent
  have count : (remove false).card+(remove true).card = conflicts.card := by
    let col (a : J × V) := reversePartnerColor paths a.2 (parent a.1)
    have complement (a : J × V) : col a = true ↔ ¬col a = false := by cases col a <;> decide
    change (conflicts.filter fun a => col a = false).card+
      (conflicts.filter fun a => col a = true).card = conflicts.card
    simpa only [complement] using
      (card_filter_add_card_filter_not (s := conflicts) (fun a => col a = false))
  by_cases le : (remove false).card ≤ (remove true).card
  · refine ⟨false,?_⟩
    change 2*(remove false).card ≤ conflicts.card
    omega
  · refine ⟨true,?_⟩
    change 2*(remove true).card ≤ conflicts.card
    omega

end OnlineReachabilityPreservers
