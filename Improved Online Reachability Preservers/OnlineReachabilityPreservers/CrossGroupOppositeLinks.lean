import OnlineReachabilityPreservers.FirstOccurrenceTrimming
import OnlineReachabilityPreservers.OppositeLinkForest

/-! A surviving opposite link can be charged to an original link between groups. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn
open Finset

variable {I V C : Type*} [LinearOrder I] [DecidableEq V]

omit [LinearOrder I] in
private theorem opposite_chain_idx_lt {rows : I → List V} {a b : I} {x y : V}
    (chain : Relation.TransGen (OppositeNeighbors rows a b) x y) : (rows a).idxOf x < (rows a).idxOf y := by
  induction chain with
  | single step => exact step.2.1.2.2
  | tail _ step previous => exact previous.trans step.2.1.2.2

omit [LinearOrder I] in
/-- A chain joining vertices in different groups contains an opposite link
between groups, inside the interval of the chain in its forward row. -/
theorem oppositeNeighbors_crossing_in_interval {rows : I → List V} {a b : I} {x y : V}
    (group : V → C) (chain : Relation.TransGen (OppositeNeighbors rows a b) x y) (across : group x ≠ group y) :
    ∃ u v, OppositeNeighbors rows a b u v ∧ group u ≠ group v ∧
      (rows a).idxOf x ≤ (rows a).idxOf u ∧ (rows a).idxOf v ≤ (rows a).idxOf y := by
  induction chain with
  | single step => exact ⟨x,_,step,across,le_rfl,le_rfl⟩
  | @tail middle last front step previous =>
    by_cases different : group middle ≠ group last
    · exact ⟨middle,last,step,different,(opposite_chain_idx_lt front).le,le_rfl⟩
    · have equal : group middle = group last := not_not.mp different
      obtain ⟨u,v,link,transition,left,right⟩ := previous (fun same => across (same.trans equal))
      exact ⟨u,v,link,transition,left,right.trans step.2.1.2.2.le⟩

omit [LinearOrder I] in
private theorem retainedBefore_of_original_order {rows kept : I → List V} {i : I} {x y : V}
    (simple : (rows i).Nodup) (sub : (kept i).Sublist (rows i)) (onX : x ∈ kept i) (onY : y ∈ kept i)
    (order : (rows i).idxOf x < (rows i).idxOf y) : Before kept i x y := by
  have different : x ≠ y := fun same => (lt_irrefl _) (same ▸ order)
  exact (listBefore_total onX onY different).resolve_right (fun wrong =>
    lt_asymm order (listBefore_of_sublist simple sub wrong).2.2)

omit [LinearOrder I] in
private theorem opposite_intervals_eq_of_shared_link {rows kept : I → List V} {a b : I} {x y c d u v : V}
    (simple : (rows a).Nodup) (sub : (kept a).Sublist (rows a))
    (left : OppositeNeighbors kept a b x y) (right : OppositeNeighbors kept a b c d)
    (between : OppositeNeighbors rows a b u v)
    (leftStart : (rows a).idxOf x ≤ (rows a).idxOf u) (leftEnd : (rows a).idxOf v ≤ (rows a).idxOf y)
    (rightStart : (rows a).idxOf c ≤ (rows a).idxOf u) (rightEnd : (rows a).idxOf v ≤ (rows a).idxOf d) :
    x = c ∧ y = d := by
  have link := between.2.1.2.2
  have start : x = c := by
    by_contra different
    have rankApart : (rows a).idxOf x ≠ (rows a).idxOf c := fun equal =>
      different ((List.idxOf_inj (sub.subset left.2.1.1)).mp equal)
    rcases lt_or_gt_of_ne rankApart with earlier | later
    · exact left.2.2.2 ⟨c,
        retainedBefore_of_original_order simple sub left.2.1.1 right.2.1.1 earlier,
        retainedBefore_of_original_order simple sub right.2.1.1 left.2.1.2.1
          (rightStart.trans_lt (link.trans_le leftEnd)),
        right.2.2.1.2.1⟩
    · exact right.2.2.2 ⟨x,
        retainedBefore_of_original_order simple sub right.2.1.1 left.2.1.1 later,
        retainedBefore_of_original_order simple sub left.2.1.1 right.2.1.2.1
          (leftStart.trans_lt (link.trans_le rightEnd)),
        left.2.2.1.2.1⟩
  subst c
  refine ⟨rfl,?_⟩
  by_contra different
  rcases listBefore_total left.2.1.2.1 right.2.1.2.1 different with earlier | later
  · exact right.2.2.2 ⟨y,left.2.1,earlier,left.2.2.1.1⟩
  · exact left.2.2.2 ⟨d,right.2.1,later,right.2.2.1.1⟩

/-- The opposite links whose vertices belong to different groups. -/
def crossGroupOppositeLinkGraph (rows : I → List V) (free : HalfBridgeFree (Before rows) 2)
    (group : V → C) : SimpleGraph V where
  Adj x y := (oppositeLinkGraphOfHalfTwo rows free).Adj x y ∧ group x ≠ group y
  symm := ⟨fun _ _ edge => ⟨edge.1.symm, edge.2.symm⟩⟩
  loopless := ⟨fun _ edge => edge.2 rfl⟩

private theorem opposite_neighbor_labels {rows : I → List V} (free : HalfBridgeFree (Before rows) 2)
    {a b c d : I} {x y : V} (first : OppositeNeighbors rows a b x y) (second : OppositeNeighbors rows c d x y) :
    a = c ∧ b = d := by
  constructor <;> by_contra different
  · exact no_parallel_list_steps free le_rfl different first.2.1 second.2.1
  · exact no_parallel_list_steps free le_rfl different first.2.2.1 second.2.2.1

variable [Fintype V]

/-- If each surviving opposite link crosses groups, their total number is
bounded by the original cross-group opposite links. In a fixed forward
row, two different surviving intervals cannot share the charged link. -/
theorem oppositeLinkGraph_card_le_crossGroup_of_sublists {rows kept : I → List V}
    (free : HalfBridgeFree (Before rows) 2) (keptFree : HalfBridgeFree (Before kept) 2)
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) (group : V → C)
    (crossing : ∀ {a b x y}, OppositeNeighbors kept a b x y → group x ≠ group y) :
    Nat.card (oppositeLinkGraphOfHalfTwo kept keptFree).edgeSet ≤
      Nat.card (crossGroupOppositeLinkGraph rows free group).edgeSet := by
  classical
  let current := oppositeLinkGraphOfHalfTwo kept keptFree
  let original := crossGroupOppositeLinkGraph rows free group
  have thusOriented (e : current.edgeSet) : ∃ a b x y, e.val = s(x,y) ∧ a < b ∧ OppositeNeighbors kept a b x y := by
    obtain ⟨edge,on⟩ := e
    induction edge using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨a,b,link⟩ := current.mem_edgeSet.mp on
      rcases lt_or_gt_of_ne link.1 with early | late
      · exact ⟨a,b,x,y,rfl,early,link⟩
      · exact ⟨b,a,y,x,Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩),late,oppositeNeighbors_swap_of_halfTwo keptFree link⟩
  choose a b x y oriented using thusOriented
  have crosses (e : current.edgeSet) : ∃ u v, OppositeNeighbors rows (a e) (b e) u v ∧ group u ≠ group v ∧
      (rows (a e)).idxOf (x e) ≤ (rows (a e)).idxOf u ∧ (rows (a e)).idxOf v ≤ (rows (a e)).idxOf (y e) := by
    have link := (oriented e).2.2
    have forward := listBefore_of_sublist (simple (a e)) (sub (a e)) link.2.1
    have reverse := listBefore_of_sublist (simple (b e)) (sub (b e)) link.2.2.1
    exact oppositeNeighbors_crossing_in_interval group
      (oppositeNeighbors_connect_of_halfTwo free link.1 forward reverse) (crossing link)
  choose u v selected using crosses
  let charge (e : current.edgeSet) : original.edgeSet :=
    ⟨s(u e,v e),original.mem_edgeSet.mpr ⟨⟨a e,b e,(selected e).1⟩,(selected e).2.1⟩⟩
  have oneToOne : Function.Injective charge := by
    intro e f same
    have exactPair : s(u e,v e) = s(u f,v f) := congrArg Subtype.val same
    rcases Sym2.eq_iff.mp exactPair with ⟨left,right⟩ | ⟨left,right⟩
    · have aligned : OppositeNeighbors rows (a f) (b f) (u e) (v e) := by
        simpa only [left,right] using (selected f).1
      obtain ⟨sameA,sameB⟩ := opposite_neighbor_labels free (selected e).1 aligned
      have retained : OppositeNeighbors kept (a e) (b e) (x f) (y f) := by
        simpa only [sameA,sameB] using (oriented f).2.2
      have start : (rows (a e)).idxOf (x f) ≤ (rows (a e)).idxOf (u e) := by
        simpa only [sameA,left] using (selected f).2.2.1
      have finish : (rows (a e)).idxOf (v e) ≤ (rows (a e)).idxOf (y f) := by
        simpa only [sameA,right] using (selected f).2.2.2
      obtain ⟨matchesX,matchesY⟩ := opposite_intervals_eq_of_shared_link (simple (a e)) (sub (a e))
        (oriented e).2.2 retained (selected e).1 (selected e).2.2.1 (selected e).2.2.2 start finish
      exact Subtype.ext ((oriented e).1.trans ((Sym2.eq_iff.mpr (Or.inl ⟨matchesX,matchesY⟩)).trans (oriented f).1.symm))
    · have reversed : OppositeNeighbors rows (b f) (a f) (u e) (v e) := by
        simpa only [left,right] using oppositeNeighbors_swap_of_halfTwo free (selected f).1
      obtain ⟨sameA,sameB⟩ := opposite_neighbor_labels free (selected e).1 reversed
      have after : b f < a f := by simpa only [sameA,sameB] using (oriented e).2.1
      exact (lt_asymm after (oriented f).2.1).elim
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective charge oneToOne

/-- Count original neighboring cross-group links to pay for the extra
pruning after first-occurrence trimming. The input cutoff is preserved. -/
theorem HalfBridgeFree.exists_unique_intersections_with_cross_group_link_bound {n p cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : HalfBridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (hp : 0 < p) (first : Fin n → Fin p)
    (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i) :
    let two : HalfBridgeFree (Before rows) 2 := fun _ size => free (size.trans (by omega))
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (rows i)) ∧ (∀ i, (kept i).Nodup) ∧ HalfBridgeFree (Before kept) cutoff ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      (∑ i, (rows i).length) ≤ (∑ i, (kept i).length)+n+Nat.card (crossGroupOppositeLinkGraph rows two first).edgeSet := by
  let two : HalfBridgeFree (Before rows) 2 := fun _ size => free (size.trans (by omega))
  obtain ⟨owner,trimmed,sub,trimmedSimple,trimmedFree,keepsFirst,one,mass⟩ :=
    free.exists_first_occurrence_trim enough simple hp
  let trimmedTwo : HalfBridgeFree (Before trimmed) 2 := fun _ size => trimmedFree (size.trans (by omega))
  have sameOwner {i : Fin p} {v : Fin n} (used : v ∈ rows i) : first v = owner v := by
    have originally := (sub (owner v)).subset (keepsFirst i v used).1
    exact le_antisymm (firstSpec (owner v) v originally).2
      (keepsFirst (first v) v (firstSpec i v used).1).2
  have crossing {a b : Fin p} {x y : Fin n} (link : OppositeNeighbors trimmed a b x y) : first x ≠ first y := by
    intro same
    have owners : owner x = owner y := (sameOwner ((sub a).subset link.2.1.1)).symm.trans
      (same.trans (sameOwner ((sub a).subset link.2.1.2.1)))
    have impossible {i : Fin p} (other : owner x ≠ i) (onX : x ∈ trimmed i) (onY : y ∈ trimmed i) : False :=
      listBefore_ne link.2.1 (card_le_one_iff.mp (one i (owner x) other)
        (mem_filter.mpr ⟨List.mem_toFinset.mpr onX,rfl⟩)
        (mem_filter.mpr ⟨List.mem_toFinset.mpr onY,owners.symm⟩))
    by_cases initial : owner x = a
    · exact impossible (fun equal => link.1 (initial.symm.trans equal)) link.2.2.1.2.1 link.2.2.1.1
    · exact impossible initial link.2.1.1 link.2.1.2.1
  have links := oppositeLinkGraph_card_le_crossGroup_of_sublists two trimmedTwo simple sub first
    (fun {_ _ _ _} => crossing)
  let kept := removeOppositeIntersections trimmed
  have keptSub (i : Fin p) : (kept i).Sublist (rows i) :=
    (removeOppositeIntersections_sublist trimmed i).trans (sub i)
  have keptSimple (i : Fin p) : (kept i).Nodup := (keptSub i).nodup (simple i)
  have keptFree : HalfBridgeFree (Before kept) cutoff := by
    intro size bound b earlier
    exact free bound (b.mapPaths id Function.injective_id (fun i _ _ step =>
      listBefore_of_sublist (simple i) (keptSub i) step)) earlier
  have pruning := removeOppositeIntersections_mass_with_half_two_link_count trimmedTwo trimmedSimple
  change (∑ i, (trimmed i).length) ≤ (∑ i, (kept i).length) +
    Nat.card (oppositeLinkGraphOfHalfTwo trimmed trimmedTwo).edgeSet at pruning
  refine ⟨kept,keptSub,keptSimple,keptFree,?_,by omega⟩
  intro i j x y apart onXA onXB onYA onYB
  exact removeOppositeIntersections_unique trimmedSimple trimmedFree
    (by omega) apart onXA onXB onYA onYB

end OnlineReachabilityPreservers
