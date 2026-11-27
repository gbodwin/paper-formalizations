import OnlineReachabilityPreservers.ShortReturnFixedCopyCleaning

/-! Bound the cost of clipping short-return components by a monotone rank. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Any subset keeping at most the width in each original component loses
at least the total excess. Component clipping attains this lower bound. -/
theorem linkedGroupExcess_add_retained_le {V : Type*} [LinearOrder V] [Fintype V]
    {members retained : Finset V} {G : Arcs V} {width : ℕ}
    (sub : retained ⊆ members)
    (fits : ∀ x ∈ members, (linkedGroupComponent members G x ∩ retained).card ≤ width) :
    (∑ group ∈ linkedGroupComponents members G, (group.card - width)) + retained.card ≤
      members.card := by
  let groups := linkedGroupComponents members G
  have retainedUnion : groups.biUnion (· ∩ retained) = retained := by
    ext v
    constructor
    · intro on
      obtain ⟨_, _, inGroup⟩ := mem_biUnion.mp on
      exact (mem_inter.mp inGroup).2
    · intro on
      have onMembers := sub on
      rw [← linkedGroupComponents_cover members G] at onMembers
      obtain ⟨group, among, present⟩ := mem_biUnion.mp onMembers
      exact mem_biUnion.mpr ⟨group, among, mem_inter.mpr ⟨present, on⟩⟩
  have apart : (↑groups : Set (Finset V)).PairwiseDisjoint (· ∩ retained) := by
    intro a onA b onB different
    exact (linkedGroupComponents_apart members G onA onB different).mono inter_subset_left inter_subset_left
  have retainedCount : retained.card = ∑ g ∈ groups, (g ∩ retained).card :=
    (congrArg card retainedUnion).symm.trans (card_biUnion apart)
  have memberCount : members.card = ∑ g ∈ groups, g.card :=
    (congrArg card (linkedGroupComponents_cover members G)).symm.trans
      (card_biUnion (linkedGroupComponents_apart members G))
  change (∑ group ∈ groups, (group.card - width)) + retained.card ≤ members.card
  rw [retainedCount, memberCount, ← sum_add_distrib]
  apply sum_le_sum
  intro group among
  obtain ⟨x, on, rfl⟩ := mem_image.mp among
  have inside : (linkedGroupComponent members G x ∩ retained).card ≤
      (linkedGroupComponent members G x).card := card_le_card inter_subset_left
  have capped := fits x on
  omega

/-- If every strict comparison respects a vertex rank, endpoints joined
by a short backward return have equal rank. A retained subset whose rank
classes fit the width bounds the cost of clipping all path components. -/
theorem shortReturnPathExcessMass_add_ranked_subsets_le
    {I V : Type*} [Fintype I] [Fintype V] [LinearOrder V]
    (rows : I → List V) (simple : ∀ i, (rows i).Nodup) (width k : ℕ)
    (rank : V → ℕ) (ordered : ∀ ⦃i x y⦄, Before rows i x y → rank x ≤ rank y)
    (retained : I → Finset V) (sub : ∀ i, retained i ⊆ (rows i).toFinset)
    (fits : ∀ i a, ((retained i).filter fun v => rank v = a).card ≤ width) :
    shortReturnPathExcessMass rows width k + (∑ i, (retained i).card) ≤
      ∑ i, (rows i).length := by
  let G := listPiecePrecedenceGraph rows
  have along {x y : V} (route : Reach G x y) : rank x ≤ rank y := by
    induction route with
    | refl => exact le_rfl
    | tail _ edge ih =>
      obtain ⟨i, step⟩ := listPiecePrecedenceGraph_edge.mp edge
      exact ih.trans (ordered step)
  have linked {i : I} {x y : V} (step : Before rows i x y)
      (back : y ∈ reachIn G x (k-3)) : rank x = rank y :=
    le_antisymm (ordered step) (along (reachIn_sound back))
  have sameRank {i : I} {x y : V} (route : Reach (shortReturnRowGraph rows k i) x y) :
      rank x = rank y := by
    induction route with
    | refl => rfl
    | tail _ edge ih =>
      rcases shortReturnRowGraph_edge.mp edge with forward | backward
      · exact ih.trans (linked forward.1 forward.2)
      · exact ih.trans (linked backward.1 backward.2).symm
  unfold shortReturnPathExcessMass
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  rw [← List.toFinset_card_of_nodup (simple i)]
  apply linkedGroupExcess_add_retained_le (sub i)
  intro x _
  refine (card_le_card ?_).trans (fits i (rank x))
  intro y on
  obtain ⟨inGroup, retainedY⟩ := mem_inter.mp on
  have connected := componentLabel_eq.mp (mem_filter.mp inGroup).2
  exact mem_filter.mpr ⟨retainedY, sameRank connected.1⟩

/-- A rank test on the original degree copies can certify the full-mode
path-excess criterion without computing the individual return components. -/
theorem regularization_list_frozen_full_of_ranked_copied_subsets {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (rank : ListVertexBlockIndex rows (4*(∑ i, (rows i).length)/n) → ℕ)
    (ordered : let M := ∑ i, (rows i).length
      ∀ ⦃i x y⦄, Before (splitListVertices rows (4*M/n)) i x y → rank x ≤ rank y)
    (retained : Fin p → Finset (ListVertexBlockIndex rows (4*(∑ i, (rows i).length)/n)))
    (sub : let M := ∑ i, (rows i).length
      ∀ i, retained i ⊆ (splitListVertices rows (4*M/n) i).toFinset)
    (fits : let M := ∑ i, (rows i).length
      ∀ i a, ((retained i).filter fun v => rank v = a).card ≤ 4*M/p)
    (mass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (retained i).card)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let copies := splitListVertices rows (4*M/n)
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple rows _ i (simple i)
  have copyMass : (∑ i, (copies i).length) = M := by simp [copies, M]
  have excess := shortReturnPathExcessMass_add_ranked_subsets_le copies copySimple (4*M/p) k
    rank (fun {_ _ _} step => ordered step) retained sub fits
  rw [copyMass] at excess
  apply regularization_list_frozen_full_of_small_copied_path_excess rows simple free hn hp dense long
  change 3*shortReturnPathExcessMass copies (4*M/p) k ≤ M
  change 2*M ≤ 3*(∑ i, (retained i).card) at mass
  omega

end OnlineReachabilityPreservers
