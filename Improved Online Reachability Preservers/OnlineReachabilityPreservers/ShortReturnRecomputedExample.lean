import OnlineReachabilityPreservers.ShortReturnClippingAfterDeletion
import OnlineReachabilityPreservers.ShortReturnRankedExcess

/-! One deletion changes component costs enough to pass the frozen test. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- A length-seven spine, its six adjacent backward darts, and a
bidirected ten-leaf star at vertex zero. Unused row labels are empty. -/
def recomputedExampleRows (i : Fin 59) : List (Fin 48) :=
  if i.val = 0 then [0,1,2,3,4,5,6]
  else if h : i.val < 7 then [⟨i.val,by omega⟩,⟨i.val-1,by omega⟩]
  else if h : i.val < 17 then [0,⟨i.val,by omega⟩]
  else if h : i.val < 27 then [⟨i.val-10,by omega⟩,0]
  else []

private theorem recomputedExample_mass_simple :
    (∑ i, (recomputedExampleRows i).length) = 59 ∧
      ∀ i, (recomputedExampleRows i).Nodup := by decide +kernel

/-- Both frozen widths equal four at the original mass and budgets. -/
theorem recomputedExample_widths :
    let M := ∑ i, (recomputedExampleRows i).length
    M = 59 ∧ 4*M/48 = 4 ∧ 4*M/59 = 4 := by
  dsimp only
  rw [recomputedExample_mass_simple.1]
  decide

private theorem pair_step {I V : Type*} [DecidableEq V] {rows : I → List V} {i : I} {a b x y : V}
    (row : rows i = [a,b]) (different : a ≠ b) (step : BeforeIn rows i x y) : x = a ∧ y = b := by
  have onX : x ∈ [a,b] := row ▸ step.1
  have onY : y ∈ [a,b] := row ▸ step.2.1
  rcases List.mem_cons.mp onX with rfl | tail
  · rcases List.mem_cons.mp onY with rfl | last
    · exact (listBefore_ne step rfl).elim
    · exact ⟨rfl, List.mem_singleton.mp last⟩
  · obtain rfl := List.mem_singleton.mp tail
    rcases List.mem_cons.mp onY with rfl | last
    · have wrong := step.2.2
      rw [row] at wrong
      simp [different] at wrong
    · obtain rfl := List.mem_singleton.mp last
      exact (listBefore_ne step rfl).elim

private theorem recomputed_step_shape {i : Fin 59} {x y : Fin 48}
    (step : BeforeIn recomputedExampleRows i x y) :
    (i.val = 0 ∧ x.val < y.val ∧ y.val < 7) ∨
    (0 < i.val ∧ i.val < 7 ∧ x.val = i.val ∧ y.val+1 = i.val) ∨
    (7 ≤ i.val ∧ i.val < 17 ∧ x = 0 ∧ y.val = i.val) ∨
    (17 ≤ i.val ∧ i.val < 27 ∧ x.val+10 = i.val ∧ y = 0) := by
  by_cases first : i.val = 0
  · have checked : ∀ a b : Fin 48, BeforeIn recomputedExampleRows 0 a b → a.val < b.val ∧ b.val < 7 := by
      unfold BeforeIn
      decide +kernel
    have same : i = 0 := Fin.ext first
    exact Or.inl ⟨first, checked x y (same ▸ step)⟩
  by_cases reverse : i.val < 7
  · let a : Fin 48 := ⟨i.val,by omega⟩
    let b : Fin 48 := ⟨i.val-1,by omega⟩
    have row : recomputedExampleRows i = [a,b] := by simp [recomputedExampleRows, first, reverse, a, b]
    have apart : a ≠ b := by
      intro same
      have values : i.val = i.val-1 := congrArg Fin.val same
      omega
    obtain ⟨rfl,rfl⟩ := pair_step row apart step
    exact Or.inr (Or.inl ⟨by omega, reverse, rfl, by change i.val-1+1 = i.val; omega⟩)
  by_cases outward : i.val < 17
  · let b : Fin 48 := ⟨i.val,by omega⟩
    have row : recomputedExampleRows i = [0,b] := by
      simp [recomputedExampleRows, first, reverse, outward, b]
    have apart : (0 : Fin 48) ≠ b := by
      intro same
      have values : 0 = i.val := congrArg Fin.val same
      omega
    obtain ⟨rfl,rfl⟩ := pair_step row apart step
    exact Or.inr (Or.inr (Or.inl ⟨by omega, outward, rfl, rfl⟩))
  by_cases inward : i.val < 27
  · let a : Fin 48 := ⟨i.val-10,by omega⟩
    have row : recomputedExampleRows i = [a,0] := by
      simp [recomputedExampleRows, first, reverse, outward, inward, a]
    have apart : a ≠ 0 := by
      intro same
      have values : i.val-10 = 0 := congrArg Fin.val same
      omega
    obtain ⟨rfl,rfl⟩ := pair_step row apart step
    exact Or.inr (Or.inr (Or.inr ⟨by omega, inward, by change i.val-10+10 = i.val; omega, rfl⟩))
  · have impossible := step.1
    simp [recomputedExampleRows, first, reverse, outward, inward] at impossible

private theorem bridgeFree_of_river_barriers {I V : Type*} [DecidableEq V] (rows : I → List V)
    (separate : ∀ ⦃i x y⦄, BeforeIn rows i x y → ∃ side : V → Prop,
      side x ∧ ¬side y ∧ ∀ ⦃j a b⦄, j ≠ i → BeforeIn rows j a b → side a → side b)
    (cutoff : ℕ) : BridgeFree (BeforeIn rows) cutoff := by
  intro d _
  refine ⟨fun bridge => ?_⟩
  obtain ⟨side, starts, finishes, closed⟩ := separate bridge.riverStep
  have along (j : Fin (d+2)) : side (bridge.vertex j) := by
    induction j using Fin.induction with
    | zero => exact starts
    | succ i earlier => exact closed (bridge.river_ne_arc i).symm (bridge.arcStep i) earlier
  exact finishes (along _)

private def spineRank (v : Fin 48) : ℕ :=
  if v.val < 7 then v.val else 0

private theorem spineRank_chain {v : Fin 48} (on : v.val < 7) : spineRank v = v.val := by
  simp [spineRank,on]

private theorem spineRank_leaf {v : Fin 48} (on : 7 ≤ v.val) : spineRank v = 0 := by
  simp [spineRank,not_lt_of_ge on]

private theorem spineRank_zero : spineRank 0 = 0 := by decide +kernel

private theorem recomputedExample_barriers {i : Fin 59} {x y : Fin 48} (step : BeforeIn recomputedExampleRows i x y) :
    ∃ side : Fin 48 → Prop,
      side x ∧ ¬side y ∧ ∀ ⦃j a b⦄, j ≠ i → BeforeIn recomputedExampleRows j a b → side a → side b := by
  rcases recomputed_step_shape step with start | reverse | outbound | inbound
  · refine ⟨fun v => spineRank v ≤ x.val, ?_, ?_, ?_⟩
    · change spineRank x ≤ x.val
      rw [spineRank_chain (v := x) (by omega)]
    · change ¬spineRank y ≤ x.val
      rw [spineRank_chain start.2.2]
      exact (Nat.not_le_of_lt start.2.1)
    · intro j a b apart path on
      rcases recomputed_step_shape path with main | backward | out | into
      · exact (apart (Fin.ext (main.1.trans start.1.symm))).elim
      · rw [spineRank_chain (by omega : a.val < 7)] at on
        rw [spineRank_chain (by omega : b.val < 7)]
        omega
      · rw [spineRank_leaf (by omega)]
        exact Nat.zero_le _
      · rw [into.2.2.2, spineRank_zero]
        exact Nat.zero_le _
  · refine ⟨fun v => i.val ≤ spineRank v, ?_, ?_, ?_⟩
    · change i.val ≤ spineRank x
      rw [spineRank_chain (by omega : x.val < 7)]
      omega
    · change ¬i.val ≤ spineRank y
      rw [spineRank_chain (by omega : y.val < 7)]
      omega
    · intro j a b apart path on
      rcases recomputed_step_shape path with main | backward | out | into
      · rw [spineRank_chain (by omega : a.val < 7)] at on
        rw [spineRank_chain main.2.2]
        omega
      · rw [spineRank_chain (by omega : a.val < 7)] at on
        rw [spineRank_chain (by omega : b.val < 7)]
        have rowApart : j.val ≠ i.val := fun eq => apart (Fin.ext eq)
        omega
      · rw [out.2.2.1, spineRank_zero] at on
        omega
      · rw [spineRank_leaf (by omega)] at on
        omega
  · refine ⟨fun v => v ≠ y, listBefore_ne step, fun impossible => impossible rfl, ?_⟩
    intro j a b apart path _ same
    subst b
    rcases recomputed_step_shape path with main | backward | out | into
    · omega
    · omega
    · exact apart (Fin.ext (out.2.2.2.symm.trans outbound.2.2.2))
    · have value := congrArg Fin.val into.2.2.2
      change y.val = 0 at value
      omega
  · refine ⟨fun v => v = x, rfl, (listBefore_ne step).symm, ?_⟩
    intro j a b apart path on
    subst a
    rcases recomputed_step_shape path with main | backward | out | into
    · omega
    · omega
    · have value := congrArg Fin.val out.2.2.1
      change x.val = 0 at value
      omega
    · exact (apart (Fin.ext (into.2.2.1.symm.trans inbound.2.2.1))).elim

/-- Each river comparison has a cut that only its own row can cross. -/
theorem recomputedExample_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn recomputedExampleRows) cutoff :=
  bridgeFree_of_river_barriers recomputedExampleRows (fun {_ _ _} => recomputedExample_barriers) cutoff

/-- A single removal breaks the backward comparison from four to three. -/
def recomputedExampleKept (i : Fin 59) : List (Fin 48) :=
  (recomputedExampleRows i).filter fun v => decide (i ≠ 4 ∨ v ≠ 3)

private theorem recomputedExampleKept_sublist (i : Fin 59) :
    (recomputedExampleKept i).Sublist (recomputedExampleRows i) := List.filter_sublist

private theorem recomputedExampleKept_mass :
    (∑ i, (recomputedExampleKept i).length) = 58 := by decide +kernel

private def recomputedExampleRank (v : Fin 48) : ℕ :=
  if 4 ≤ v.val ∧ v.val < 7 then 1 else 0

private theorem recomputedExampleRank_ordered (i : Fin 59) :
    (recomputedExampleKept i).Pairwise (fun x y => recomputedExampleRank x ≤ recomputedExampleRank y) := by
  revert i
  decide +kernel

private theorem recomputedExampleRank_width (i : Fin 59) (r : ℕ) :
    ((recomputedExampleKept i).toFinset.filter fun v => recomputedExampleRank v = r).card ≤ 4 := by
  have fits : ∀ (j : Fin 59) (a : Fin 2),
      ((recomputedExampleKept j).toFinset.filter fun v => recomputedExampleRank v = a.val).card ≤ 4 := by
    decide +kernel
  by_cases small : r < 2
  · exact fits i ⟨r, small⟩
  have bound (v : Fin 48) : recomputedExampleRank v < 2 := by unfold recomputedExampleRank; split <;> decide
  have empty : ((recomputedExampleKept i).toFinset.filter fun v => recomputedExampleRank v = r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v on
    exact small ((mem_filter.mp on).2 ▸ bound v)
  simp [empty]

/-- The two rank groups on the long row have at most four vertices each.
After the one deletion, the recomputed path excess is zero at every cutoff. -/
theorem recomputedExampleKept_path_excess (k : ℕ) :
    shortReturnPathExcessMass recomputedExampleKept 4 k = 0 := by
  have simple (i : Fin 59) : (recomputedExampleKept i).Nodup :=
    (recomputedExampleKept_sublist i).nodup (recomputedExample_mass_simple.2 i)
  have ordered {i : Fin 59} {x y : Fin 48} (step : BeforeIn recomputedExampleKept i x y) :
      recomputedExampleRank x ≤ recomputedExampleRank y := by
    have xAt := List.idxOf_lt_length_of_mem step.1
    have yAt := List.idxOf_lt_length_of_mem step.2.1
    have monotone := List.pairwise_iff_getElem.mp (recomputedExampleRank_ordered i) _ _ xAt yAt step.2.2
    simpa only [List.getElem_idxOf] using monotone
  have upper := shortReturnPathExcessMass_add_ranked_subsets_le recomputedExampleKept simple 4 k
    recomputedExampleRank (fun {_ _ _} => ordered) (fun i => (recomputedExampleKept i).toFinset)
    (fun _ => Subset.rfl) recomputedExampleRank_width
  have mass : (∑ i, (recomputedExampleKept i).toFinset.card) = ∑ i, (recomputedExampleKept i).length :=
    sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
  rw [mass] at upper
  omega

private theorem linkedGroupExcess_le_total_overage {V : Type*} [LinearOrder V] [Fintype V]
    (members : Finset V) (G : Arcs V) (width : ℕ) :
    (∑ part ∈ linkedGroupComponents members G, (part.card-width)) ≤ members.card-width := by
  obtain ⟨retained, sub, count⟩ := exists_subset_card_eq
    (show min width members.card ≤ members.card from min_le_right _ _)
  have paid := linkedGroupExcess_add_retained_le (G := G) (width := width) sub
    (fun _ _ => (card_le_card inter_subset_right).trans (count.trans_le (min_le_left _ _)))
  omega

private theorem recomputedExample_degree_overage :
    (∑ v, ((occurrences (fun i => (recomputedExampleRows i).toFinset) v).card - 4)) = 18 := by
  decide +kernel

private theorem recomputedExample_degree_excess (k : ℕ) :
    shortReturnDegreeExcessMass recomputedExampleRows 4 k ≤ 18 := by
  rw [← recomputedExample_degree_overage]
  unfold shortReturnDegreeExcessMass
  exact sum_le_sum (fun v _ => linkedGroupExcess_le_total_overage
    (occurrences (fun i => (recomputedExampleRows i).toFinset) v)
    (shortReturnCopyRowGraph recomputedExampleRows k v) 4)

/-- Initial loss one and recomputed excess at most eighteen fit the
original budget; both frozen widths and the full cutoff are preserved. -/
theorem recomputedExample_frozen (cutoff : ℕ) :
    ∃ n' ≤ 48, ∃ p' ≤ 59, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) cutoff ∧
      59 ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 59 ∧
      frozenListCaps 48 59 59 clean := by
  have mass := recomputedExample_mass_simple.1
  have dense : 48 ≤ ∑ i, (recomputedExampleRows i).length := by rw [mass]; decide
  have long : 59 ≤ ∑ i, (recomputedExampleRows i).length := mass.ge
  have boundV : shortReturnDegreeExcessMass recomputedExampleKept 4 cutoff ≤ 18 :=
    (shortReturnExcess_le_of_sublist recomputedExample_mass_simple.2 recomputedExampleKept_sublist 4 4 cutoff).1.trans
      (recomputedExample_degree_excess cutoff)
  have result := regularization_list_frozen_of_small_recomputed_excess_after_sublist (half := false)
    recomputedExampleRows recomputedExampleKept recomputedExample_mass_simple.2
    (recomputedExample_fullFree cutoff) recomputedExampleKept_sublist (by decide) (by decide) dense long (by
      dsimp only
      rw [mass, recomputedExampleKept_mass, show 4*59/48 = 4 by decide,
        recomputedExampleKept_path_excess cutoff]
      omega)
  simpa only [mass, localOrderAdmissible, Bool.false_eq_true, ite_false] using result

private def recomputedCenterTip (i : Fin 59) : Fin 48 :=
  if i.val < 2 then 1
  else if i.val < 17 then ⟨i.val % 48, Nat.mod_lt _ (by decide)⟩
  else ⟨(i.val-10) % 48,Nat.mod_lt _ (by decide)⟩

private def recomputedCenterMate (i : Fin 59) : Fin 59 :=
  if i = 0 then 1 else if i = 1 then 0
  else if i.val < 17 then (i+10) else (i-10)

private theorem recomputed_center_steps :
    ∀ i : Fin 59, (0 : Fin 48) ∈ recomputedExampleRows i →
      let x := recomputedCenterTip i
      let mate := recomputedCenterMate i
      (i ≠ 1 ∧ BeforeIn recomputedExampleRows i 0 x ∧ BeforeIn recomputedExampleRows mate x 0) ∨
        (i ≠ 0 ∧ BeforeIn recomputedExampleRows i x 0 ∧ BeforeIn recomputedExampleRows mate 0 x) := by
  unfold BeforeIn
  decide +kernel

private theorem recomputed_center_initial :
    BeforeIn recomputedExampleRows 0 0 1 ∧ BeforeIn recomputedExampleRows 1 1 0 := by
  unfold BeforeIn
  decide +kernel

private theorem degree_component_from_two_step_return {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [LinearOrder V]
    {rows : I → List V} {i j inward outward : I} {v x y : V}
    (different : i ≠ j) (start : BeforeIn rows i v x) (finish : BeforeIn rows j y v)
    (back : BeforeIn rows inward x v) (forth : BeforeIn rows outward v y) :
    SameComponent (shortReturnCopyRowGraph rows 7 v) i j := by
  let G := listPiecePrecedenceGraph rows
  have edgeBack : Edge G x v := listPiecePrecedenceGraph_edge.mpr ⟨inward,back⟩
  have edgeForward : Edge G v y := listPiecePrecedenceGraph_edge.mpr ⟨outward,forth⟩
  have tail : v ∈ reachIn G y 2 :=
    (reachIn_succ (G := G) (k := 1)).mpr (Or.inr ⟨y,edgeForward,target_mem_reachIn G y 1⟩)
  have route : x ∈ reachIn G y 3 :=
    (reachIn_succ (G := G) (k := 2)).mpr (Or.inr ⟨v,edgeBack,tail⟩)
  have link : ShortReturnCopyRowPair rows 7 v i j := ⟨different,x,y,start,finish,route⟩
  exact ⟨.single (shortReturnCopyRowGraph_edge.mpr (Or.inl link)),
    .single (shortReturnCopyRowGraph_edge.mpr (Or.inr link))⟩

private theorem recomputed_center_connected (i : Fin 59) (on : (0 : Fin 48) ∈ recomputedExampleRows i) :
    SameComponent (shortReturnCopyRowGraph recomputedExampleRows 7 0) i 0 := by
  obtain ⟨first,last⟩ := recomputed_center_initial
  have middle := degree_component_from_two_step_return (by decide : (0 : Fin 59) ≠ 1) first last last first
  rcases recomputed_center_steps i on with ⟨different,start,back⟩ | ⟨different,finish,forth⟩
  · exact (degree_component_from_two_step_return different start last back first).trans middle.symm
  · exact (degree_component_from_two_step_return different.symm first finish last forth).symm

private def recomputedCenterClass : Fin 48 × Fin 59 :=
  (0, componentLabel (shortReturnCopyRowGraph recomputedExampleRows 7 0) 0)

private theorem recomputed_center_class_count :
    ((pieceIncidences recomputedExampleRows univ).filter
      fun a => shortReturnDegreeClass recomputedExampleRows 7 a = recomputedCenterClass).card = 22 := by
  rw [recomputedCenterClass,shortReturnDegreeClass_card]
  let atCenter := occurrences (fun i => (recomputedExampleRows i).toFinset) (0 : Fin 48)
  have all : (atCenter.filter fun i => componentLabel (shortReturnCopyRowGraph recomputedExampleRows 7 0) i =
      componentLabel (shortReturnCopyRowGraph recomputedExampleRows 7 0) 0) = atCenter := by
    ext i
    refine ⟨fun h => (mem_filter.mp h).1, fun on => ?_⟩
    exact mem_filter.mpr ⟨on,componentLabel_eq.mpr (recomputed_center_connected i
      (List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (recomputedExampleRows i).toFinset)).mp on)))⟩
  change (atCenter.filter _).card = 22
  rw [all]
  decide +kernel

private def recomputedSpineVertex (i : Fin 7) : Fin 48 := i.castLE (by decide)

private theorem recomputed_spine_steps (i : Fin 6) :
    BeforeIn recomputedExampleRows 0 (recomputedSpineVertex i.castSucc) (recomputedSpineVertex i.succ) ∧
      BeforeIn recomputedExampleRows (i.succ.castLE (by decide))
        (recomputedSpineVertex i.succ) (recomputedSpineVertex i.castSucc) := by
  revert i
  unfold BeforeIn
  decide +kernel

private theorem row_component_from_reverse_step {I V : Type*} [Fintype I] [Fintype V] [LinearOrder V]
    {rows : I → List V} {i j : I} {x y : V}
    (start : BeforeIn rows i x y) (back : BeforeIn rows j y x) :
    SameComponent (shortReturnRowGraph rows 7 i) x y := by
  let G := listPiecePrecedenceGraph rows
  have edge : Edge G y x := listPiecePrecedenceGraph_edge.mpr ⟨j,back⟩
  have route : y ∈ reachIn G x 4 :=
    (reachIn_succ (G := G) (k := 3)).mpr (Or.inr ⟨x,edge,target_mem_reachIn G x 3⟩)
  exact ⟨.single (shortReturnRowGraph_edge.mpr (Or.inl ⟨start,route⟩)),
    .single (shortReturnRowGraph_edge.mpr (Or.inr ⟨start,route⟩))⟩

private theorem recomputed_spine_connected (i : Fin 7) :
    SameComponent (shortReturnRowGraph recomputedExampleRows 7 0) (recomputedSpineVertex i) 0 := by
  induction i using Fin.induction with
  | zero => exact SameComponent.refl _ _
  | succ j earlier =>
    obtain ⟨forth,back⟩ := recomputed_spine_steps j
    exact (row_component_from_reverse_step forth back).symm.trans earlier

private def recomputedSpineClass : Fin 59 × Fin 48 :=
  (0,componentLabel (shortReturnRowGraph recomputedExampleRows 7 0) 0)

private theorem recomputed_spine_class_count :
    ((pieceIncidences recomputedExampleRows univ).filter
      fun a => shortReturnPathClass recomputedExampleRows 7 a = recomputedSpineClass).card = 7 := by
  rw [recomputedSpineClass,shortReturnPathClass_card]
  have same : ((recomputedExampleRows 0).toFinset.filter
      fun v => componentLabel (shortReturnRowGraph recomputedExampleRows 7 0) v =
        componentLabel (shortReturnRowGraph recomputedExampleRows 7 0) 0) =
      (recomputedExampleRows 0).toFinset := by
    ext v
    refine ⟨fun on => (mem_filter.mp on).1, fun on => ?_⟩
    have inside : ∀ x ∈ recomputedExampleRows 0, x.val < 7 := by decide +kernel
    let index : Fin 7 := ⟨v.val,inside v (List.mem_toFinset.mp on)⟩
    have val : recomputedSpineVertex index = v := Fin.ext rfl
    exact mem_filter.mpr ⟨on, componentLabel_eq.mpr (val ▸ recomputed_spine_connected index)⟩
  rw [same]
  decide +kernel

private theorem original_two_class_loss {A : Type*} [DecidableEq A]
    (degree path removed : Finset A) (degreeCap pathCap : ℕ)
    (fitsV : (degree \ removed).card ≤ degreeCap) (fitsI : (path \ removed).card ≤ pathCap) :
    degree.card + path.card ≤ degreeCap + pathCap + (degree ∩ path).card + removed.card := by
  have splitV := card_sdiff_add_card_inter degree removed
  have splitI := card_sdiff_add_card_inter path removed
  have packed := card_union_add_card_inter (degree ∩ removed) (path ∩ removed)
  have combined : ((degree ∩ removed) ∪ (path ∩ removed)).card ≤ removed.card :=
    card_le_card (union_subset inter_subset_right inter_subset_right)
  have overlap : ((degree ∩ removed) ∩ (path ∩ removed)).card ≤ (degree ∩ path).card :=
    card_le_card (subset_inter (inter_subset_left.trans inter_subset_left)
      (inter_subset_right.trans inter_subset_left))
  omega

private theorem original_filtered_classes_loss {A : Type*} [DecidableEq A]
    (items removed : Finset A) (degree path : A → Prop) [DecidablePred degree] [DecidablePred path]
    (degreeCap pathCap : ℕ)
    (fitsV : ((items \ removed).filter degree).card ≤ degreeCap)
    (fitsI : ((items \ removed).filter path).card ≤ pathCap) :
    (items.filter degree).card + (items.filter path).card ≤
      degreeCap + pathCap + ((items.filter degree) ∩ (items.filter path)).card + removed.card := by
  have filter_sdiff_original (p : A → Prop) [DecidablePred p] :
      (items.filter p) \ removed = (items \ removed).filter p := by
    ext a
    simp only [mem_filter, mem_sdiff]
    tauto
  exact original_two_class_loss (items.filter degree) (items.filter path) removed degreeCap pathCap
    (by rw [filter_sdiff_original]; exact fitsV) (by rw [filter_sdiff_original]; exact fitsI)

private theorem degree_path_classes_overlap_at_most_once {I V : Type*}
    [Fintype I] [Fintype V] [LinearOrder I] [LinearOrder V]
    (rows : I → List V) (k : ℕ) (items : Finset (I × V)) (degree : V × I) (path : I × V) :
    ((items.filter (fun a => shortReturnDegreeClass rows k a = degree)) ∩
      (items.filter (fun a => shortReturnPathClass rows k a = path))).card ≤ 1 := by
  refine (card_le_card (t := {(path.1, degree.1)}) ?_).trans_eq (card_singleton _)
  intro a on
  obtain ⟨left, right⟩ := mem_inter.mp on
  have col : a.2 = degree.1 := congrArg Prod.fst (mem_filter.mp left).2
  have pathEq : shortReturnPathClass rows k a = path := (mem_filter.mp right).2
  have row := congrArg (fun p : I × V => p.1) pathEq
  change a.1 = path.1 at row
  exact mem_singleton.mpr (Prod.ext row col)

/-- Keeping both original class widths through cutoff seven requires at
least twenty deletions. The original one-third budget is nineteen. -/
theorem recomputedExample_original_caps_need_twenty (removed : Finset (Fin 59 × Fin 48))
    (degree : ∀ c, (((pieceIncidences recomputedExampleRows univ) \ removed).filter
      fun a => shortReturnDegreeClass recomputedExampleRows 7 a = c).card ≤ 4)
    (path : ∀ c, (((pieceIncidences recomputedExampleRows univ) \ removed).filter
      fun a => shortReturnPathClass recomputedExampleRows 7 a = c).card ≤ 4) :
    20 ≤ removed.card := by
  let items := pieceIncidences recomputedExampleRows univ
  let degreeLabel (a : Fin 59 × Fin 48) := shortReturnDegreeClass recomputedExampleRows 7 a = recomputedCenterClass
  let pathLabel (a : Fin 59 × Fin 48) := shortReturnPathClass recomputedExampleRows 7 a = recomputedSpineClass
  let atCenter := items.filter degreeLabel
  let onSpine := items.filter pathLabel
  have paid : atCenter.card + onSpine.card ≤ 4+4+(atCenter ∩ onSpine).card + removed.card :=
    original_filtered_classes_loss items removed degreeLabel pathLabel 4 4
      (degree recomputedCenterClass) (path recomputedSpineClass)
  have both : (atCenter ∩ onSpine).card ≤ 1 :=
    degree_path_classes_overlap_at_most_once recomputedExampleRows 7 items recomputedCenterClass recomputedSpineClass
  have countV : atCenter.card = 22 := recomputed_center_class_count
  have countI : onSpine.card = 7 := recomputed_spine_class_count
  omega

end OnlineReachabilityPreservers.SourceAudit
