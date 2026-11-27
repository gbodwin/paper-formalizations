import OnlineReachabilityPreservers.ComponentSplitCleaning

/-! Two-step return certificates for full cutoff seven. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

/-- A return radius of two suffices for full exclusion through seven
when disjoint pieces preserve comparisons and may interleave. -/
theorem bridgeFree_of_disjoint_split_of_no_two_step_backward_returns {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [LinearOrder I] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W}
    (G : Arcs V) (project : W → V) (parent : J → I)
    (steps : ∀ ⦃i x y⦄, Before pieces i x y → Before paths (parent i) x y)
    (edges : ∀ ⦃i x y⦄, Before pieces i x y → Edge G (project x) (project y))
    (disjoint : ∀ ⦃i j x⦄, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (safe : NoShortBackwardReturnAcrossPieces G project paths pieces parent 2)
    (free : BridgeFree (Before paths) cutoff) (short : cutoff ≤ 7) :
    BridgeFree (Before pieces) cutoff := by
  refine fullBridgeFree_of_opposite_and_two_step_safe_split (paths := paths) (pieces := pieces) parent
    (fun {_ _ _} step => steps step) (fun {_ _ _} apart eq onX onY => disjoint apart eq onX onY)
    ?_ ?_ free short
  · intro i j q x y same _ forward reverse onX onY
    by_contra different
    apply safe different same onX onY forward
    have one : project y ∈ reachIn G (project x) 1 :=
      reachIn_succ.mpr (Or.inr ⟨project x, edges reverse, target_mem_reachIn G (project x) 0⟩)
    exact reachIn_subset_succ G (project x) 1 one
  · intro i j a c x y z different same _ _ _ onX onY reverse first second
    apply safe different.symm same.symm onY onX (same ▸ reverse)
    have last : project z ∈ reachIn G (project y) 1 :=
      reachIn_succ.mpr (Or.inr ⟨project y, edges second, target_mem_reachIn G (project y) 0⟩)
    exact reachIn_succ.mpr (Or.inr ⟨project z, edges first, last⟩)

/-- For full cutoff seven, test just one and two edges of the actual
piece graph across each original width cut. The argument 5 gives
radius 5 minus 3 in the existing width-cut test. -/
theorem splitListPaths_full_seven_of_two_step_width_test {p L : ℕ}
    {V : Type*} [LinearOrder V] [Fintype V] (rows : Fin p → List V)
    (simple : ∀ i, (rows i).Nodup) (free : BridgeFree (Before rows) 7)
    (test : NoShortReturnAcrossWidthCutsInPieces rows L 5) :
    BridgeFree (Before (splitListPaths rows L)) 7 := by
  let J := ListBlockIndex rows L
  let pieces := splitListPaths rows L
  let parent (j : J) := j.fst
  let G := listPiecePrecedenceGraph pieces
  refine bridgeFree_of_disjoint_split_of_no_two_step_backward_returns G id parent
    (fun {i _ _} step => listBefore_of_sublist (paths := fun j : J => rows j.fst)
      (simple i.fst) List.filter_sublist step)
    (fun {i _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨i, step⟩)
    (fun {_ _ _} => splitListPaths_disjoint) ?_ free (by decide)
  intro i j x y different same onX onY before
  apply test before
  rcases i with ⟨a,u⟩
  rcases j with ⟨b,v⟩
  change a = b at same
  subst b
  have xBlock := (mem_localPathBlock.mp onX).2
  have yBlock := (mem_localPathBlock.mp onY).2
  intro equal
  exact different (congrArg (Sigma.mk a) (Fin.ext (xBlock.symm.trans (equal.trans yBlock))))

/-- At full cutoff seven, the two-step return check after both standard
width splits gives the frozen witness at the original budgets. -/
theorem regularization_list_frozen_full_seven_of_two_step_width_test {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) 7)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (test : let M := ∑ i, (rows i).length; NoShortReturnAcrossCopiedWidthCuts rows (4*M/n) (4*M/p) 5) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 7 ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let copies := splitListVertices rows (4*M/n)
  have copied : BridgeFree (Before copies) 7 :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have pieces : localOrderAdmissible false 7 (listRegularizedPaths rows (4*M/n) (4*M/p)) :=
    splitListPaths_full_seven_of_two_step_width_test copies
      (fun i => splitListVertices_simple rows _ i (simple i)) copied test
  exact regularization_list_frozen_after_width_blocks_of_mass rows simple pieces
    hn hp dense long le_rfl (by omega)

end OnlineReachabilityPreservers
