import OnlineReachabilityPreservers.ContiguousHalfCleaning

/-! Count active repairs using positions in the later width blocks. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem laterOppositePath_unique {V I : Type*} [DecidableEq V] [LinearOrder I]
    {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 3)
    {central a b : I} {w u v : V} (earlierA : central < a) (earlierB : central < b)
    (au : ListBefore paths a w u) (bv : ListBefore paths b w v)
    (centralU : ListBefore paths central u w) (centralV : ListBefore paths central v w) : a = b := by
  by_contra different
  by_cases equal : u = v
  · subst v
    exact no_parallel_list_steps free (by decide) different au bv
  rcases listBefore_total centralU.1 centralV.1 equal with step | step
  · exact free (by decide) (threeListBridge earlierA.ne' (fun equal => different equal.symm) earlierB.ne' au step bv) earlierB
  · exact free (by decide) (threeListBridge earlierB.ne' different earlierA.ne' bv step au) earlierA

variable {n p : ℕ}

/-- The width-cut incidences after the first block of a path, excluding
the last vertex in every block. -/
noncomputable def laterCutNonterminalIncidences (paths : Fin p → List (Fin n)) (D L : ℕ) :
    Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) := by
  classical
  exact univ.filter fun a => 0 < a.1.snd.val ∧ a.2 ∈ (listRegularizedPaths paths D L a.1).dropLast

/-- The count is obtained directly from the block lengths. -/
theorem laterCutNonterminalIncidences_card (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (D L : ℕ) :
    (laterCutNonterminalIncidences paths D L).card =
      ∑ i : ListBlockIndex (splitListVertices paths D) L,
        if 0 < i.snd.val then (listRegularizedPaths paths D L i).length-1 else 0 := by
  classical
  unfold laterCutNonterminalIncidences
  rw [card_filter,← univ_product_univ,Finset.sum_product]
  apply sum_congr rfl
  intro i _
  rw [← card_filter]
  by_cases afterFirst : 0 < i.snd.val
  · rw [ite_eq_left afterFirst]
    let piece := listRegularizedPaths paths D L i
    have members : (univ.filter fun w => 0 < i.snd.val ∧ w ∈ piece.dropLast) = piece.dropLast.toFinset := by
      ext w
      simp [afterFirst]
    rw [members,List.toFinset_card_of_nodup ((List.dropLast_sublist piece).nodup
      (listRegularizedPaths_simple paths simple D L i)),List.length_dropLast]
  · simp [afterFirst]

/-- Each active inner start charges a different nonterminal incidence in
a later block of a central path. Half-three exclusion gives injectivity. -/
theorem widthCutActiveNestedStarts_card_le_later_nonterminal (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4) (D L : ℕ) :
    Nat.card (widthCutActiveNestedStarts paths D L) ≤ (laterCutNonterminalIncidences paths D L).card := by
  classical
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  let active := widthCutActiveNestedStarts paths D L
  let target := laterCutNonterminalIncidences paths D L
  let J := ListBlockIndex copies L
  let W := ListVertexBlockIndex paths D
  have originalThree : HalfBridgeFree (ListBefore paths) 3 := fun _ h => free (h.trans (by decide))
  have copyThree : HalfBridgeFree (ListBefore copies) 3 :=
    originalThree.split_list_vertices_short (by decide) (fun v => v.fst)
      (fun {i _ _} step => splitListVertices_step (simple i) step)
  have copySimple (i : Fin p) : (copies i).Nodup := by
    apply List.Nodup.of_map (fun v => v.fst)
    rw [splitListVertices_project]
    exact simple i
  have lift {i : J} {a b : W} (step : ListBefore pieces i a b) : ListBefore copies i.fst a b :=
    listBefore_of_sublist (paths := fun j : J => copies j.fst) (cut := pieces) (copySimple i.fst)
      List.filter_sublist step
  have sameIndex {a b : J} (same : a.fst = b.fst) (index : a.snd.val = b.snd.val) : a = b := by
    rcases a with ⟨i,ix⟩
    rcases b with ⟨j,jx⟩
    change i = j at same
    subst j
    obtain rfl : ix = jx := Fin.ext index
    rfl
  have inInner (a : active) : a.val.2 ∈ pieces a.val.1 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,inner⟩ := a.property
    exact inner.1
  have canCharge (a : active) : ∃ j : J, (j,a.val.2) ∈ target ∧
      j.fst < a.val.1.fst ∧ ∃ v : W, ListBefore copies j.fst v a.val.2 ∧
        ListBefore copies a.val.1.fst a.val.2 v := by
    obtain ⟨early,late,_,_,v,z,different,same,_,_,arrival,center,left,right,_,inner⟩ := a.property
    change early.fst = late.fst at same
    have beforeCut : (copies early.fst).idxOf v/L = early.snd.val := (mem_localPathBlock.mp left.2.1).2
    have afterCut : (copies late.fst).idxOf a.val.2/L = late.snd.val := (mem_localPathBlock.mp right.1).2
    have atLeast : (copies early.fst).idxOf v/L ≤ (copies late.fst).idxOf a.val.2/L := by
      rw [← same]
      exact Nat.div_le_div_right center.2.2.le
    rw [beforeCut,afterCut] at atLeast
    have afterFirst : 0 < late.snd.val :=
      (atLeast.lt_of_ne (fun equal => different (sameIndex same equal))).pos
    have notLast : a.val.2 ∈ (pieces late).dropLast := by
      have beforeZ : (pieces late).idxOf a.val.2 < (pieces late).idxOf z := right.2.2
      have zInside : (pieces late).idxOf z < (pieces late).length := List.idxOf_lt_length_of_mem right.2.1
      exact (List.mem_dropLast_iff_idxOf_lt (l := pieces late) right.1).2
        (beforeZ.trans_le (by omega))
    refine ⟨late,?_,same ▸ arrival,v,same ▸ center,lift inner⟩
    change (late,a.val.2) ∈ laterCutNonterminalIncidences paths D L
    exact mem_filter.mpr ⟨mem_univ _,afterFirst,notLast⟩
  let assigned (a : active) := Classical.choose (canCharge a)
  have certificate (a : active) := Classical.choose_spec (canCharge a)
  let charge (a : active) : target := ⟨(assigned a,a.val.2),(certificate a).1⟩
  have injective : Function.Injective charge := by
    intro a b eq
    have image := congrArg Subtype.val eq
    change (assigned a,a.val.2) = (assigned b,b.val.2) at image
    have sameBlock : assigned a = assigned b := congrArg Prod.fst image
    have sameStart := congrArg (fun x : J × W => x.2) image
    obtain ⟨_,earlyA,u,alongA,reverseA⟩ := certificate a
    obtain ⟨_,earlyB,v,alongB,reverseB⟩ := certificate b
    have earlyB' : (assigned a).fst < b.val.1.fst := by rw [sameBlock]; exact earlyB
    have alongB' : ListBefore copies (assigned a).fst v a.val.2 := by rw [sameBlock,sameStart]; exact alongB
    have reverseB' : ListBefore copies b.val.1.fst a.val.2 v := by rw [sameStart]; exact reverseB
    have sameParent : a.val.1.fst = b.val.1.fst :=
      laterOppositePath_unique copyThree earlyA earlyB' reverseA reverseB' alongA alongB'
    have samePiece : a.val.1 = b.val.1 := by
      by_contra different
      exact splitListPaths_disjoint different sameParent (inInner a) (sameStart.symm ▸ inInner b)
    exact Subtype.ext (Prod.ext samePiece sameStart)
  exact (Nat.card_le_card_of_injective charge injective).trans_eq
    (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])

/-- A sufficient cleaning criterion using only the lengths of the
non-first width blocks. -/
theorem regularization_list_frozen_half_four_of_few_later_nonterminal (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : let M := ∑ i, (paths i).length
      12*(laterCutNonterminalIncidences paths (4*M/n) (4*M/p)).card ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 64*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_half_four_of_few_active_nested_starts paths simple free hn hp dense long
    ((Nat.mul_le_mul_left 12 (widthCutActiveNestedStarts_card_le_later_nonterminal paths simple free _ _)).trans few)

end OnlineReachabilityPreservers
