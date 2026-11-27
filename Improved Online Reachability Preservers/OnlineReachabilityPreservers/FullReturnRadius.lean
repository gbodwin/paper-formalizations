import OnlineReachabilityPreservers.BackwardCopyReturns
import OnlineReachabilityPreservers.FrozenDistinctCleaning

/-! The shortest repeated-parent gap gives a smaller return radius for full bridges. -/

namespace OnlineReachabilityPreservers

open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Every relevant crossed return is a backward walk in a graph
containing the projected comparisons of the pieces. -/
theorem NoShortBackwardReturnAcrossPieces.noCrossedParentReturnUpTo
    {V W I J : Type*} [DecidableEq V] [DecidableEq W] {radius : ℕ}
    {paths : I → List W} {pieces : J → List W} {G : Arcs V} {project : W → V} {parent : J → I}
    (safe : NoShortBackwardReturnAcrossPieces G project paths pieces parent radius)
    (edges : ∀ {i x y}, Before pieces i x y → Edge G (project x) (project y)) :
    NoCrossedParentReturnUpTo paths pieces parent radius := by
  intro i j d apart same short v a _ _ first last backward along
  have reachable : project (v 0) ∈ reachIn G (project (v (Fin.last d))) d :=
    reachIn_of_fin_steps (project ∘ v) (fun t => edges (along t))
  have mono : Monotone (reachIn G (project (v (Fin.last d)))) :=
    monotone_nat_of_le_succ (reachIn_subset_succ G _)
  exact safe apart.symm same.symm last first (same ▸ backward) (mono short reachable)

/-- At a full cutoff of at least seven, depth cutoff minus five in the
actual comparison graph suffices for a disjoint order-preserving split. -/
theorem bridgeFree_of_disjoint_split_of_short_parent_returns
    {V W I J : Type*} [DecidableEq V] [DecidableEq W] [LinearOrder I] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V) (parent : J → I)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (edges : ∀ {i x y}, Before pieces i x y → Edge G (project x) (project y))
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (safe : NoShortBackwardReturnAcrossPieces G project paths pieces parent (cutoff-5))
    (free : BridgeFree (Before paths) cutoff) (large : 7 ≤ cutoff) : BridgeFree (Before pieces) cutoff :=
  fullBridgeFree_of_short_parent_returns parent (fun {_ _ _} => steps) (fun {_ _ _} => disjoint)
    (safe.noCrossedParentReturnUpTo (fun {_ _ _} => edges)) free large

/-- Test the shortened radius in the graph of the actual width blocks. -/
theorem splitListPaths_fullFree_of_short_parent_return_width_test {p width cutoff : ℕ}
    {V : Type*} [LinearOrder V] [Fintype V] (rows : Fin p → List V)
    (simple : ∀ i, (rows i).Nodup) (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (test : NoShortReturnAcrossWidthCutsInPieces rows width (cutoff-2)) :
    BridgeFree (Before (splitListPaths rows width)) cutoff := by
  let pieces := splitListPaths rows width
  let J := ListBlockIndex rows width
  let G := listPiecePrecedenceGraph pieces
  refine bridgeFree_of_disjoint_split_of_short_parent_returns G id Sigma.fst
    (fun {i _ _} step => listBefore_of_sublist (paths := fun j : J => rows j.fst)
      (simple i.fst) List.filter_sublist step)
    (fun {i _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨i, step⟩)
    (fun {_ _ _} => splitListPaths_disjoint) ?_ free large
  intro i j x y apart same first last forward reachable
  rcases i with ⟨a,i⟩
  rcases j with ⟨b,j⟩
  change a = b at same
  subst b
  have xBlock := (mem_localPathBlock.mp first).2
  have yBlock := (mem_localPathBlock.mp last).2
  have different : (rows a).idxOf x/width ≠ (rows a).idxOf y/width :=
    fun equal => apart (congrArg (Sigma.mk a) (Fin.ext (xBlock.symm.trans (equal.trans yBlock))))
  have radius : (cutoff-2-2)-1 = cutoff-5 := by omega
  exact test forward different (by simpa only [radius, G, pieces, id_eq] using reachable)

/-- The shortened test on the standard degree and path blocks gives
one sixteenth of the original mass with both budgets and frozen caps. -/
theorem regularization_list_frozen_full_of_short_parent_return_width_test {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (test : let M := ∑ i, (rows i).length
      NoShortReturnAcrossCopiedWidthCuts rows (4*M/n) (4*M/p) (cutoff-2)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let copies := splitListVertices rows (4*M/n)
  have copied : BridgeFree (Before copies) cutoff :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have allowed : localOrderAdmissible false cutoff (listRegularizedPaths rows (4*M/n) (4*M/p)) :=
    splitListPaths_fullFree_of_short_parent_return_width_test copies
      (fun i => splitListVertices_simple rows _ i (simple i)) copied large test
  exact regularization_list_frozen_after_width_blocks_of_mass rows simple allowed
    hn hp dense long le_rfl (by omega)

/-- The same width test certifies a distinct nonempty frozen witness
for feasible literal input at every full cutoff of at least seven. -/
theorem regularization_list_frozen_full_distinct_of_short_parent_return_width_test {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (test : let M := ∑ i, (rows i).length
      NoShortReturnAcrossCopiedWidthCuts rows (4*M/n) (4*M/p) (cutoff-2)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 16*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 16)
    rows distinct nonempty simple free (by omega) hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_short_parent_return_width_test
      rows simple free large hn hp dense long test)

end OnlineReachabilityPreservers
