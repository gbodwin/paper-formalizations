import OnlineReachabilityPreservers.BridgeRiverRanks

/-! A component test for the existence of ranks on actual path pieces. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Add the reverse of each possible river comparison whose endpoints
already have a short detour outside that river piece. The reverse edge
records that the two endpoints must have equal rank. -/
def riverDetourConstraintGraph {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V]
    (pieces : J → List V) (k : ℕ) : Arcs V := by
  letI (x y : V) : DecidablePred (fun j => Before pieces j y x ∧
      y ∈ reachIn (listPiecePrecedenceGraph (fun i => if i = j then [] else pieces i)) x (k-1)) :=
    fun j => by unfold SourceAudit.BeforeIn; infer_instance
  exact listPiecePrecedenceGraph pieces ∪
    univ.filter fun e => ∃ j, Before pieces j e.2 e.1 ∧
      e.2 ∈ reachIn (listPiecePrecedenceGraph (fun i => if i = j then [] else pieces i)) e.1 (k-1)

theorem riverDetourConstraintGraph_edge {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V]
    {pieces : J → List V} {k : ℕ} {x y : V} :
    Edge (riverDetourConstraintGraph pieces k) x y ↔
      (∃ i, Before pieces i x y) ∨ ∃ i, Before pieces i y x ∧
        y ∈ reachIn (listPiecePrecedenceGraph (fun j => if j = i then [] else pieces j)) x (k-1) := by
  unfold Edge riverDetourConstraintGraph
  simp only [mem_union,mem_filter,mem_univ,true_and]
  exact or_congr listPiecePrecedenceGraph_edge Iff.rfl

private theorem rank_conditions_iff_constraint_monotone {J V : Type*}
    [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V] (pieces : J → List V) (k : ℕ) (rank : V → ℕ) :
    (∀ ⦃x y⦄, Edge (riverDetourConstraintGraph pieces k) x y → rank x ≤ rank y) ↔
      (∀ {i x y}, Before pieces i x y → rank x ≤ rank y) ∧ NoCrossRankRiverDetour pieces rank k := by
  constructor
  · intro monotone
    refine ⟨fun {i x y} h => monotone (riverDetourConstraintGraph_edge.mpr (Or.inl ⟨i,h⟩)),?_⟩
    intro i x y river increasing found
    exact increasing.not_ge (monotone (riverDetourConstraintGraph_edge.mpr (Or.inr ⟨i,river,found⟩)))
  · rintro ⟨ordered,noDetour⟩ x y edge
    rcases riverDetourConstraintGraph_edge.mp edge with ⟨_,before⟩ | ⟨_,river,found⟩
    · exact ordered before
    · exact le_of_not_gt (fun increasing => noDetour river increasing found)

private noncomputable def componentPredecessorRank {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (x : V) : ℕ :=
  (reaches G x).card * Fintype.card V + (Fintype.equivFin V (componentLabel G x)).val

private theorem componentPredecessorRank_eq {V : Type*} [LinearOrder V] [Fintype V]
    {G : Arcs V} {x y : V} : componentPredecessorRank G x = componentPredecessorRank G y ↔ SameComponent G x y := by
  constructor
  · intro equal
    have remainder (v : V) : componentPredecessorRank G v % Fintype.card V =
        (Fintype.equivFin V (componentLabel G v)).val := by
      let label := Fintype.equivFin V (componentLabel G v)
      change ((reaches G v).card * Fintype.card V + label.val) % Fintype.card V = label.val
      rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt label.isLt]
    have same := congrArg (fun n : ℕ => n % Fintype.card V) equal
    rw [remainder,remainder] at same
    exact componentLabel_eq.mp ((Fintype.equivFin V).injective (Fin.ext same))
  · intro same
    have predecessors : reaches G x = reaches G y := by
      ext v
      simp only [mem_reaches]
      exact ⟨fun h => h.trans same.1,fun h => h.trans same.2⟩
    unfold componentPredecessorRank
    rw [predecessors,componentLabel_eq.mpr same]

private theorem componentPredecessorRank_mono {V : Type*} [LinearOrder V] [Fintype V]
    {G : Arcs V} {x y : V} (edge : Edge G x y) : componentPredecessorRank G x ≤ componentPredecessorRank G y := by
  by_cases same : SameComponent G x y
  · exact (componentPredecessorRank_eq.mpr same).le
  · have count : (reaches G x).card < (reaches G y).card := by
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun v on => mem_reaches.mpr ((mem_reaches.mp on).tail edge),?_⟩
      intro equal
      have on : y ∈ reaches G y := mem_reaches.mpr .refl
      exact same ⟨.single edge,mem_reaches.mp (equal.symm ▸ on)⟩
    apply Nat.le_of_lt
    calc
      _ < ((reaches G x).card+1)*Fintype.card V := by
        rw [Nat.succ_mul]
        exact Nat.add_lt_add_left (Fintype.equivFin V (componentLabel G x)).isLt _
      _ ≤ (reaches G y).card*Fintype.card V := Nat.mul_le_mul_right _ count
      _ ≤ _ := Nat.le_add_right _ _

private theorem equal_ranks_of_same_component {V : Type*} {G : Arcs V} {rank : V → ℕ}
    (mono : ∀ ⦃x y⦄, Edge G x y → rank x ≤ rank y) {x y : V} (same : SameComponent G x y) :
    rank x = rank y := by
  have along {a b : V} (route : Reach G a b) : rank a ≤ rank b := by
    induction route with
    | refl => exact le_rfl
    | tail _ step earlier => exact earlier.trans (mono step)
  exact le_antisymm (along same.1) (along same.2)

/-- A suitable rank exists exactly when distinct pieces of one parent
meet no common strongly connected component of the constraint graph. -/
theorem exists_river_detour_rank_iff {I J V : Type*} [DecidableEq J] [LinearOrder V] [Fintype J] [Fintype V]
    (parent : J → I) (pieces : J → List V) (k : ℕ) :
    (∃ rank : V → ℕ, (∀ {i x y}, Before pieces i x y → rank x ≤ rank y) ∧
      (∀ {i j x y}, i ≠ j → parent i = parent j → x ∈ pieces i → y ∈ pieces j → rank x ≠ rank y) ∧
      NoCrossRankRiverDetour pieces rank k) ↔
    (∀ {i j x y}, i ≠ j → parent i = parent j → x ∈ pieces i → y ∈ pieces j →
      ¬ SameComponent (riverDetourConstraintGraph pieces k) x y) := by
  constructor
  · rintro ⟨rank,ordered,apart,noDetour⟩ i j x y distinct same hx hy components
    have edges := (rank_conditions_iff_constraint_monotone pieces k rank).mpr ⟨ordered,noDetour⟩
    exact apart distinct same hx hy (equal_ranks_of_same_component edges components)
  · intro apart
    let rank := componentPredecessorRank (riverDetourConstraintGraph pieces k)
    obtain ⟨ordered,noDetour⟩ := (rank_conditions_iff_constraint_monotone pieces k rank).mp
      (fun {_ _} => componentPredecessorRank_mono)
    exact ⟨rank,ordered,fun {_ _ _ _} distinct same hx hy equal =>
      apart distinct same hx hy (componentPredecessorRank_eq.mp equal),noDetour⟩

/-- The component test preserves the chosen bridge cutoff on the pieces. -/
theorem localOrderAdmissible_of_river_detour_component_separation {I J V : Type*}
    [LinearOrder I] [LinearOrder J] [LinearOrder V] [Fintype J] [Fintype V]
    {rows : I → List V} {pieces : J → List V} {k : ℕ} {half : Bool}
    (parent : J → I) (arrival : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (apart : ∀ {i j x y}, i ≠ j → parent i = parent j → x ∈ pieces i → y ∈ pieces j →
      ¬ SameComponent (riverDetourConstraintGraph pieces k) x y)
    (legal : localOrderAdmissible half k rows) : localOrderAdmissible half k pieces := by
  obtain ⟨rank,ordered,separate,noDetour⟩ := (exists_river_detour_rank_iff parent pieces k).mpr apart
  exact localOrderAdmissible_of_noCrossRankRiverDetour parent arrival rank steps ordered separate noDetour legal

/-- Test the actual consecutive width blocks using their detour constraint
components. Only pieces of the same parent must avoid common components. -/
theorem splitListPaths_admissible_of_river_detour_components {p k width : ℕ} {V : Type*}
    [LinearOrder V] [Fintype V] {half : Bool} (rows : Fin p → List V)
    (simple : ∀ i, (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (apart : let pieces := splitListPaths rows width
      ∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
        ¬ SameComponent (riverDetourConstraintGraph pieces k) x y) :
    localOrderAdmissible half k (splitListPaths rows width) := by
  let J := ListBlockIndex rows width
  let pieces := splitListPaths rows width
  have step {i : J} {x y : V} (before : Before pieces i x y) : Before rows i.fst x y :=
    listBefore_of_sublist (paths := fun j : J => rows j.fst) (simple i.fst) List.filter_sublist before
  exact localOrderAdmissible_of_river_detour_component_separation (fun j : J => j.fst)
    (block_parent_mono (fun i => (rows i).toFinset) width) (fun {_ _ _} => step)
    (fun {i j x y} => @apart i j x y) legal

/-- The component test on the original-width pieces gives a frozen
cleaning witness when degree copying already preserves the exclusion. -/
theorem regularization_list_frozen_of_river_detour_components {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (apart : let M := ∑ i, (paths i).length
      let pieces := listRegularizedPaths paths (4*M/n) (4*M/p)
      ∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
        ¬ SameComponent (riverDetourConstraintGraph pieces k) x y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let copies := splitListVertices paths (4*M/n)
  have allowed : localOrderAdmissible half k (listRegularizedPaths paths (4*M/n) (4*M/p)) :=
    splitListPaths_admissible_of_river_detour_components copies
      (fun i => splitListVertices_simple paths _ i (simple i)) legal apart
  exact regularization_list_frozen_after_width_blocks_of_mass (half := half) (retention := 16)
    paths simple allowed hn hp dense long le_rfl (by norm_num)

end OnlineReachabilityPreservers
