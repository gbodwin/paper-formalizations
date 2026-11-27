import OnlineReachabilityPreservers.ShortReturnFullCleaning

/-! Bidirected star paths separate the full-mode path and degree tests. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private def starOutLabel (leaf : Fin 23) : Fin 46 := leaf.castAdd 23
private def starInLabel (leaf : Fin 23) : Fin 46 := Fin.natAdd 23 leaf

/-- Use one row for each directed edge of a bidirected 23-leaf star. -/
def shortReturnStarRows (i : Fin 46) : List (Fin 24) :=
  Fin.addCases (m := 23) (n := 23) (fun j => [0, j.succ]) (fun j => [j.succ, 0]) i

private theorem starOut_row (leaf : Fin 23) : shortReturnStarRows (starOutLabel leaf) = [0, leaf.succ] := by
  simp [shortReturnStarRows, starOutLabel]

private theorem starIn_row (leaf : Fin 23) : shortReturnStarRows (starInLabel leaf) = [leaf.succ, 0] := by
  unfold shortReturnStarRows starInLabel
  rw [Fin.addCases_right]

private theorem before_pair_iff {V : Type*} [DecidableEq V] {a b x y : V} (different : a ≠ b) :
    BeforeIn (fun _ : Unit => [a,b]) () x y ↔ x = a ∧ y = b := by
  constructor
  · intro on
    rcases List.mem_cons.mp on.1 with rfl | hx
    · rcases List.mem_cons.mp on.2.1 with rfl | hy
      · exact (lt_irrefl _ on.2.2).elim
      · exact ⟨rfl, List.mem_singleton.mp hy⟩
    · obtain rfl := List.mem_singleton.mp hx
      rcases List.mem_cons.mp on.2.1 with rfl | hy
      · have impossible := on.2.2
        simp [different] at impossible
      · obtain rfl := List.mem_singleton.mp hy
        exact (lt_irrefl _ on.2.2).elim
  · rintro ⟨rfl, rfl⟩
    simp [BeforeIn, different, different.symm]

private theorem starOut_step (leaf : Fin 23) : BeforeIn shortReturnStarRows (starOutLabel leaf) 0 leaf.succ := by
  have step := (before_pair_iff (show (0 : Fin 24) ≠ leaf.succ from (Fin.succ_ne_zero leaf).symm)).mpr ⟨rfl, rfl⟩
  unfold BeforeIn at step ⊢
  rwa [starOut_row]

private theorem starIn_step (leaf : Fin 23) : BeforeIn shortReturnStarRows (starInLabel leaf) leaf.succ 0 := by
  have step := (before_pair_iff (show leaf.succ ≠ (0 : Fin 24) from Fin.succ_ne_zero leaf)).mpr ⟨rfl, rfl⟩
  unfold BeforeIn at step ⊢
  rwa [starIn_row]

private theorem star_step_cases {i : Fin 46} {x y : Fin 24} (step : BeforeIn shortReturnStarRows i x y) :
    (∃ leaf, i = starOutLabel leaf ∧ x = 0 ∧ y = leaf.succ) ∨
      (∃ leaf, i = starInLabel leaf ∧ x = leaf.succ ∧ y = 0) := by
  revert step
  refine Fin.addCases (m := 23) (n := 23) ?_ ?_ i
  · intro leaf on
    have endpoints := (before_pair_iff (show (0 : Fin 24) ≠ leaf.succ from (Fin.succ_ne_zero leaf).symm)).mp (by
      unfold BeforeIn at *
      rwa [← starOut_row])
    exact Or.inl ⟨leaf, rfl, endpoints⟩
  · intro leaf on
    have endpoints := (before_pair_iff (show leaf.succ ≠ (0 : Fin 24) from Fin.succ_ne_zero leaf)).mp (by
      unfold BeforeIn at *
      rwa [← starIn_row])
    exact Or.inr ⟨leaf, rfl, endpoints⟩

/-- Every directed star dart has either a unique row entering its
endpoint or a unique row leaving its start. -/
theorem shortReturnStarRows_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn shortReturnStarRows) cutoff := by
  intro d _
  refine ⟨fun b => ?_⟩
  rcases star_step_cases b.riverStep with ⟨leaf, river, _, finish⟩ | ⟨leaf, river, start, _⟩
  · let last := Fin.last d
    have terminal : BeforeIn shortReturnStarRows (b.arc last) (b.vertex last.castSucc) leaf.succ := by
      rw [← finish]
      exact b.arcStep last
    rcases star_step_cases terminal with ⟨other, arc, _, equal⟩ | ⟨_, _, _, equal⟩
    · have same : leaf = other := Fin.succ_injective _ equal
      exact b.river_ne_arc last (river.trans (same ▸ arc.symm))
    · exact Fin.succ_ne_zero _ equal
  · have first : BeforeIn shortReturnStarRows (b.arc 0) leaf.succ (b.vertex (0 : Fin (d+1)).succ) := by
      rw [← start]
      exact b.arcStep 0
    rcases star_step_cases first with ⟨_, _, equal, _⟩ | ⟨other, arc, equal, _⟩
    · exact Fin.succ_ne_zero _ equal
    · have same : leaf = other := Fin.succ_injective _ equal
      exact b.river_ne_arc 0 (river.trans (same ▸ arc.symm))

private theorem starRows_parameters :
    (∀ i, (shortReturnStarRows i).Nodup ∧ (shortReturnStarRows i).length = 2 ∧ (0 : Fin 24) ∈ shortReturnStarRows i) ∧
      (∑ i, (shortReturnStarRows i).length) = 92 := by
  have every (i : Fin 46) : (shortReturnStarRows i).Nodup ∧ (shortReturnStarRows i).length = 2 ∧
      (0 : Fin 24) ∈ shortReturnStarRows i := by
    refine Fin.addCases (m := 23) (n := 23) ?_ ?_ i
    · intro leaf
      rw [show shortReturnStarRows (Fin.castAdd 23 leaf) = [0,leaf.succ] from starOut_row leaf]
      simp [(Fin.succ_ne_zero leaf).symm]
    · intro leaf
      rw [show shortReturnStarRows (Fin.natAdd 23 leaf) = [leaf.succ,0] from starIn_row leaf]
      simp
  refine ⟨every, ?_⟩
  rw [show (fun i => (shortReturnStarRows i).length) = fun _ => 2 from funext (fun i => (every i).2.1)]
  decide

private theorem star_link (out incoming : Fin 23) :
    ShortReturnCopyRowPair shortReturnStarRows 7 0 (starOutLabel out) (starInLabel incoming) := by
  have apart : starOutLabel out ≠ starInLabel incoming := by
    intro equal
    have h : out.val = 23 + incoming.val := congrArg Fin.val equal
    omega
  let G := listPiecePrecedenceGraph shortReturnStarRows
  have toCenter : Edge G out.succ 0 := listPiecePrecedenceGraph_edge.mpr ⟨_, starIn_step out⟩
  have toLeaf : Edge G 0 incoming.succ := listPiecePrecedenceGraph_edge.mpr ⟨_, starOut_step incoming⟩
  have reached : (0 : Fin 24) ∈ reachIn G incoming.succ 1 :=
    reachIn_succ.mpr (Or.inr ⟨incoming.succ, toLeaf, target_mem_reachIn G _ 0⟩)
  have fromOut : out.succ ∈ reachIn G incoming.succ 2 := reachIn_succ.mpr (Or.inr ⟨0, toCenter, reached⟩)
  exact ⟨apart, out.succ, incoming.succ, starOut_step out, starIn_step incoming,
    reachIn_subset_succ G _ 2 fromOut⟩

private theorem star_same_component (out incoming : Fin 23) :
    SameComponent (shortReturnCopyRowGraph shortReturnStarRows 7 0) (starOutLabel out) (starInLabel incoming) :=
  ⟨.single (shortReturnCopyRowGraph_edge.mpr (Or.inl (star_link out incoming))),
    .single (shortReturnCopyRowGraph_edge.mpr (Or.inr (star_link out incoming)))⟩

private theorem star_center_component_univ :
    shortReturnCopyRowComponent shortReturnStarRows 7 0 (starOutLabel 0) = univ := by
  ext i
  refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
  have on : i ∈ occurrences (fun j => (shortReturnStarRows j).toFinset) 0 :=
    mem_occurrences.mpr (List.mem_toFinset.mpr ((starRows_parameters.1 i).2.2))
  have joins : SameComponent (shortReturnCopyRowGraph shortReturnStarRows 7 0) i (starOutLabel 0) := by
    refine Fin.addCases (m := 23) (n := 23) ?_ ?_ i
    · intro leaf
      exact (star_same_component leaf 0).trans (star_same_component 0 0).symm
    · intro leaf
      exact (star_same_component 0 leaf).symm
  exact mem_filter.mpr ⟨on, componentLabel_eq.mpr joins⟩

/-- At cutoff seven the center's component contains all 46 rows, though
the original factor-four degree width is only 15. -/
theorem shortReturnStar_degree_component :
    (shortReturnCopyRowComponent shortReturnStarRows 7 0 (starOutLabel 0)).card = 46 := by
  rw [star_center_component_univ, card_univ, Fintype.card_fin]

theorem shortReturnStar_widths :
    4*(∑ i, (shortReturnStarRows i).length)/24 = 15 ∧ 4*(∑ i, (shortReturnStarRows i).length)/46 = 8 := by
  rw [starRows_parameters.2]
  decide

/-- The center alone consumes more than one third of the mass in the
two-sided clipping test at the original widths. -/
theorem shortReturnStar_excess_test_fails :
    92 < 3*(shortReturnDegreeExcessMass shortReturnStarRows 15 7 +
      shortReturnPathExcessMass (clipShortReturnDegreeComponents shortReturnStarRows 15 7) 8 7) := by
  let members := occurrences (fun i => (shortReturnStarRows i).toFinset) (0 : Fin 24)
  let graph := shortReturnCopyRowGraph shortReturnStarRows 7 0
  have allRows : (univ : Finset (Fin 46)) ∈ linkedGroupComponents members graph := by
    rw [← star_center_component_univ]
    exact mem_image_of_mem _ (mem_occurrences.mpr
      (List.mem_toFinset.mpr ((starRows_parameters.1 (starOutLabel 0)).2.2)))
  let loss (v : Fin 24) := ∑ group ∈ linkedGroupComponents (occurrences (fun i => (shortReturnStarRows i).toFinset) v)
    (shortReturnCopyRowGraph shortReturnStarRows 7 v), (group.card - 15)
  have center : 31 ≤ loss 0 := calc
    _ = (univ : Finset (Fin 46)).card - 15 := by decide
    _ ≤ _ := single_le_sum (f := fun g => g.card - 15) (fun _ _ => Nat.zero_le _) allRows
  have bound : 31 ≤ shortReturnDegreeExcessMass shortReturnStarRows 15 7 :=
    center.trans (single_le_sum (f := loss) (fun _ _ => Nat.zero_le _) (mem_univ 0))
  omega

/-- The original path components fit at cutoff seven. This gives a
quarter-mass witness even though the original degree groups fail. -/
theorem shortReturnStar_full_frozen :
    ∃ n' ≤ 24, ∃ p' ≤ 46, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) 7 ∧
      92 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 92 ∧ frozenListCaps 24 46 92 clean := by
  have mass := starRows_parameters.2
  have dense : 24 ≤ ∑ i, (shortReturnStarRows i).length := by rw [mass]; decide
  have long : 46 ≤ ∑ i, (shortReturnStarRows i).length := by rw [mass]; decide
  have result := regularization_list_frozen_full_of_original_path_component_room shortReturnStarRows
    (fun i => (starRows_parameters.1 i).1) (shortReturnStarRows_fullFree 7)
    (by decide) (by decide) dense long (by
      dsimp only
      rw [mass]
      intro i x _
      have bound : (shortReturnRowComponent shortReturnStarRows 7 i x).card ≤ (shortReturnStarRows i).length :=
        (card_le_card (filter_subset _ _)).trans_eq (List.toFinset_card_of_nodup (starRows_parameters.1 i).1)
      exact bound.trans ((starRows_parameters.1 i).2.1.symm ▸ (by decide : 2 ≤ (4*92:ℕ)/46)))
  simpa only [mass] using result

end OnlineReachabilityPreservers.SourceAudit
