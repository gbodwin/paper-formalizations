import OnlineReachabilityPreservers.FullSevenPathLinks

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

end OnlineReachabilityPreservers
