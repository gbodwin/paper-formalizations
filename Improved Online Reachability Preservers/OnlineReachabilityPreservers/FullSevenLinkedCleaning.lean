import OnlineReachabilityPreservers.FullSevenPathLinks
import OnlineReachabilityPreservers.FrozenDistinctCleaning

/-! Frozen cleaning using the row labels of the two return steps. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Pack the protected groups at the stated width while preserving
full exclusion through any cutoff at most seven. -/
theorem split_of_cappedFullSevenPathPartition {V : Type*} [LinearOrder V] [Fintype V]
    {p w cutoff : ℕ} {rows : Fin p → List V} (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (bound : cutoff ≤ 7)
    (canGroup : HasCappedFullSevenPathPartition rows w) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ BridgeFree (Before pieces) cutoff ∧
      (∀ i, (pieces i).length ≤ w) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ w/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  refine split_of_capped_path_partitions (half := false) (cutoff := cutoff)
    simple (fullSevenPathLink rows) canGroup ?_
  intro sizes pieces step disjoint together
  exact fullBridgeFree_of_full_seven_path_links Sigma.fst free bound
    (fun {_ _ _} => step) (fun {_ _ _} => disjoint) (fun {_ _ _ _} => together)

/-- Width-bounded protected components on the standard degree copies
give a frozen quarter-mass witness at full cutoff seven. -/
theorem regularization_list_frozen_full_seven_of_copied_path_link_components {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) 7)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length; let copies := splitListVertices rows (4*M/n)
      ∀ i, ∀ x ∈ copies i, (fullSevenPathLinkComponent copies i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 7 ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices rows D
  have copied : BridgeFree (Before copies) 7 :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have packed := split_of_cappedFullSevenPathPartition (fun i => splitListVertices_simple rows D i (simple i))
    copied (le_rfl : 7 ≤ 7) ((hasCappedFullSevenPathPartition_iff_component_room copies L).mpr room)
  exact regularization_list_frozen_after_packing_standard_degree_copies (half := false) (k := 7)
    rows hn hp dense long packed


/-- A vertex projection preserving row comparisons also preserves the
labels of each direct or two-step return. -/
theorem fullSevenPathLink_map_vertices {I V W : Type*} [DecidableEq V] [DecidableEq W]
    {rows : I → List V} {copies : I → List W} (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before rows i (project x) (project y))
    {i : I} {x y : W} (link : fullSevenPathLink copies i x y) :
    fullSevenPathLink rows i (project x) (project y) := by
  refine ⟨steps link.1, ?_⟩
  rcases link.2 with ⟨q, reverse⟩ | ⟨a, c, z, route⟩
  · exact Or.inl ⟨q, steps reverse⟩
  · have first := steps route.into_return
    have old := steps route.parent_step
    exact Or.inr ⟨a, c, project z,
      ⟨⟨route.cross.left_ne_middle, route.cross.left_ne_right, route.cross.right_ne_middle,
          first.2.1, old.1, steps route.cross.step⟩, first, old⟩⟩

/-- The protected components cannot grow under copying when the
projection recovers each simple parent row exactly. -/
theorem fullSevenPathLinkComponent_card_le_project {I V W : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder W] [Fintype W]
    {rows : I → List V} {copies : I → List W} (project : W → V)
    (simple : ∀ i, (rows i).Nodup) (projects : ∀ i, (copies i).map project = rows i) (i : I) (x : W) :
    (fullSevenPathLinkComponent copies i x).card ≤
      (fullSevenPathLinkComponent rows i (project x)).card := by
  have step {j : I} {a b : W} (before : Before copies j a b) :
      Before rows j (project a) (project b) := by
    have mapped := listBefore_map project ((projects j).symm ▸ simple j) before
    have identifies : (fun r => (copies r).map project) = rows := funext projects
    rwa [identifies] at mapped
  refine linkedGroupComponent_card_le_project project ?_ ?_ ?_ x
  · intro v on
    have mapped := List.mem_map_of_mem (f := project) (List.mem_toFinset.mp on)
    rw [projects i] at mapped
    exact List.mem_toFinset.mpr mapped
  · intro a onA b onB equal
    by_contra! apart
    rcases listBefore_total (List.mem_toFinset.mp onA) (List.mem_toFinset.mp onB) apart with first | last
    · exact listBefore_ne (step first) equal
    · exact listBefore_ne (step last) equal.symm
  · intro a b edge
    rcases fullSevenPathLinkGraph_edge.mp edge with first | last
    · exact fullSevenPathLinkGraph_edge.mpr (Or.inl (fullSevenPathLink_map_vertices project (fun {_ _ _} => step) first))
    · exact fullSevenPathLinkGraph_edge.mpr (Or.inr (fullSevenPathLink_map_vertices project (fun {_ _ _} => step) last))

/-- It suffices to test the protected groups before choosing the
standard degree copies. -/
theorem regularization_list_frozen_full_seven_of_path_link_components {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) 7)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (fullSevenPathLinkComponent rows i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 7 ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let project (x : ListVertexBlockIndex rows D) := x.fst
  refine regularization_list_frozen_full_seven_of_copied_path_link_components rows simple free hn hp dense long ?_
  dsimp only
  intro i x on
  have projected (j : Fin p) : (splitListVertices rows D j).map project = rows j :=
    splitListVertices_project rows D j
  have appears := List.mem_map_of_mem (f := project) on
  rw [projected i] at appears
  exact (fullSevenPathLinkComponent_card_le_project project simple projected i x).trans (room i _ appears)

/-- The original protected groups also give a distinct nonempty
full-seven witness for feasible literal input. -/
theorem regularization_list_frozen_full_seven_distinct_of_path_link_components {n p : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) 7)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (fullSevenPathLinkComponent rows i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) 7 ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (half := false) (k := 7) (retention := 8)
    rows distinct nonempty simple free (by decide) hn hp dense (by decide) ?_
  dsimp only
  intro long
  obtain ⟨n', vertices, p', paths, clean, cleanSimple, allowed, lower, upper, caps⟩ :=
    regularization_list_frozen_full_seven_of_path_link_components rows simple free hn hp dense long room
  exact ⟨n', vertices, p', paths, clean, cleanSimple, allowed, by omega, upper, caps⟩

end OnlineReachabilityPreservers
