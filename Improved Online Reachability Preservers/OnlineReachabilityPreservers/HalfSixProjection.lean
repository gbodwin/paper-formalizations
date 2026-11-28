import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Unique intersections and full-three exclusion suffice for both half-six width splits. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

section VertexProjection

variable {I V W : Type*} [LinearOrder I] [DecidableEq V] [DecidableEq W]

/-- Projection at half cutoff six keeps the last arc if a two-step
return cannot switch copies and the original paths exclude full-three
bridges. A terminal three-step return would leave a two-step detour
with the same river. -/
theorem HalfBridgeFree.split_list_vertices_six_of_full_three_of_no_split_return
    {paths : I → List V} {copies : I → List W}
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y))
    (noReturn : ∀ {i j x y z}, Before copies i x y → Before copies j y z →
      project x = project z → x = z) : HalfBridgeFree (Before copies) 6 := by
  intro d small bridge earlier
  by_cases short : d ≤ 3
  · have five : HalfBridgeFree (Before paths) 5 := fun _ h => free (h.trans (by decide))
    exact (five.split_list_vertices_five_of_no_split_return project (fun {_ _ _} => steps)
      (fun {_ _ _ _ _} => noReturn)) (by omega) bridge earlier
  have size : d = 4 := by omega
  subst d
  let v := project ∘ bridge.vertex
  have first : Before paths (bridge.arc 0) (v 0) (v 1) := steps (bridge.arcStep 0)
  have second : Before paths (bridge.arc 1) (v 1) (v 2) := steps (bridge.arcStep 1)
  have last : Before paths (bridge.arc 4) (v 4) (v 5) := steps (bridge.arcStep 4)
  have river : Before paths bridge.river (v 0) (v 5) := steps bridge.riverStep
  have terminal (i : Fin 5) : v i.castSucc ≠ v (Fin.last 5) := by
    fin_cases i
    · exact listBefore_ne river
    · intro same
      exact no_parallel_list_steps three.halfFree (by decide) (bridge.river_ne_arc 0) river (same ▸ first)
    · intro same
      have shorten : Before paths (bridge.arc 1) (v 1) (v 5) := same ▸ second
      have apart : bridge.arc 0 ≠ bridge.arc 1 := fun h =>
        (by decide : (0:Fin 5) ≠ 1) (bridge.distinctArcs h)
      exact (three (by decide)).false
        (threeListBridge apart (bridge.river_ne_arc 0) (bridge.river_ne_arc 1) first shorten river)
    · intro same
      have sameCopy := noReturn (bridge.arcStep 3) (bridge.arcStep 4) same
      exact (by decide : (3:Fin 6) ≠ 5) (bridge.distinctVertices sameCopy)
    · exact listBefore_ne last
  obtain ⟨j,fit,old,sameRiver,sameArc⟩ :=
    bridge.project_vertices_preserving_last project (fun {_ _ _} => steps) listBefore_ne terminal
  exact free (by omega) old (by rw [sameArc,sameRiver]; exact earlier)

end VertexProjection

/-- At half cutoff six, simple rows with unique intersections and full
exclusion through size three admit both consecutive width splits. -/
theorem listRegularizedPaths_halfFree_six_of_full_three_unique {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 6)
    (three : BridgeFree (Before paths) 3)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (D L : ℕ) : HalfBridgeFree (Before (listRegularizedPaths paths D L)) 6 := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let parent : ListBlockIndex copies L → I := Sigma.fst
  have before {i x y} (step : Before copies i x y) : Before paths i x.fst y.fst :=
    splitListVertices_step (simple i) step
  have noReturn {i j x y z} (first : Before copies i x y) (last : Before copies j y z)
      (returns : x.fst = z.fst) : x = z := by
    have forward := before first
    have backward : Before paths j y.fst x.fst := returns.symm ▸ before last
    by_cases same : i = j
    · subst j
      exact (lt_asymm forward.2.2 backward.2.2).elim
    · exact (listBefore_ne forward (unique same forward.1 backward.2.1 forward.2.1 backward.1)).elim
  have copiedFree : HalfBridgeFree (Before copies) 6 :=
    free.split_list_vertices_six_of_full_three_of_no_split_return three (·.fst)
      (fun {_ _ _} => before) (fun {_ _ _ _ _} => noReturn)
  have copiedThree : BridgeFree (Before copies) 3 :=
    three.split_list_vertices_any (·.fst) (fun {_ _ _} => before)
  have copiedSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copiedUnique {a b x y} (different : a ≠ b) (xa : x ∈ copies a) (xb : x ∈ copies b)
      (ya : y ∈ copies a) (yb : y ∈ copies b) : x = y :=
    splitListVertices_unique simple (fun {_ _ _ _} => unique) different xa xb ya yb
  have parentStep {i x y} (step : Before pieces i x y) : Before copies (parent i) x y :=
    listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (copiedSimple i.fst) List.filter_sublist step
  have together {i j q x y} (_same : parent i = parent j) (diff : parent i ≠ parent q)
      (forward : Before copies (parent i) x y) (backward : Before pieces q y x)
      (_left : x ∈ pieces i) (_right : y ∈ pieces j) : i = j := by
    have reverse := parentStep backward
    exact (listBefore_ne forward (copiedUnique diff forward.1 reverse.2.1 forward.2.1 reverse.1)).elim
  have ordered : Monotone parent := block_parent_mono (fun i => (copies i).toFinset) L
  intro d small bridge earlier
  by_cases short : d ≤ 3
  · have five : HalfBridgeFree (Before copies) 5 := fun _ h => copiedFree (h.trans (by decide))
    exact (five.split_list_paths_five_of_unique parent ordered (fun {_ _ _} => parentStep)
      (fun {_ _ _} => splitListPaths_disjoint) (fun {_ _ _ _} => copiedUnique)) (by omega) bridge earlier
  have size : d = 4 := by omega
  subst d
  let old := listBridge_after_contiguous_opposite_safe_split_six parent
    (fun {_ _ _} => parentStep) (fun {_ _ _} => splitListPaths_disjoint)
    (fun {_ _ _ _ _} => together) (fun {_ _} => contiguousBlocks_separated) copiedThree bridge
  exact copiedFree small old (lt_of_le_of_ne (ordered earlier.le) (old.river_ne_arc _).symm)

/-- The same assumptions give the starting-average half-six witness
with both original budgets and all four exact caps. -/
theorem regularization_list_frozen_half_six_of_full_three_unique {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass (half := true) (k := 6) (retention := 16)
    paths simple (listRegularizedPaths_halfFree_six_of_full_three_unique simple free three
      (fun {_ _ _ _} => unique) (4*M/n) (4*M/p)) hn hp dense long le_rfl (by ring_nf; omega)

/-- Full-three exclusion also gives the half-six output-average witness
for arbitrary pairwise intersections. Prune opposite intersections before
choosing the rectangle and splitting its rows and vertices. -/
theorem regularization_list_output_average_half_six_of_full_three {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 392*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  refine regularization_list_output_average_of_pruned_rectangle_splits (k := 6)
    paths simple true free (by decide) ?_ hn hp dense long
  intro A B D L
  dsimp only
  intro quarterSimple quarterUnique quarterAllowed
  let kept := removeOppositeIntersections paths
  let quarter := restrictListPaths kept A B
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have quarterThree : BridgeFree (Before quarter) 3 :=
    restrictListPaths_fullFree keptSimple (removeOppositeIntersections_fullFree simple three) A B
  change HalfBridgeFree (Before (listRegularizedPaths quarter D L)) 6
  exact listRegularizedPaths_halfFree_six_of_full_three_unique quarterSimple quarterAllowed quarterThree
    (fun {_ _ _ _} => quarterUnique) D L

/-- The output-average conclusion also holds in the literal convention. -/
theorem regularization_literal_output_average_half_six_of_full_three {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 6 ∧
      M ≤ 7056*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,rowsFree,retain,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed (half := true)
      paths distinct (fun i => (valid i).1) (fun i => (valid i).2) free (by decide) hn hp dense
      (regularization_list_output_average_half_six_of_full_three paths (fun i => (valid i).2)
        free three hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,rowsFree,retain,upper,caps⟩

/-- With unique intersections, the full-three premise also gives a
starting-average witness in the literal convention. -/
theorem regularization_literal_frozen_half_six_of_full_three_unique {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 6 ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,full,retention,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(full 6).halfFree,by omega,upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum fun i _ => List.length_pos_of_ne_nil (valid i).1
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retention,upper,caps⟩ :=
    regularization_list_frozen_half_six_of_full_three_unique paths (fun i => (valid i).2) free three
      (fun {_ _ _ _} => unique) hn hp dense long
  have mean : 4*p < M := by have bound := le_max_right n p; omega
  obtain ⟨oneToOne,nonempty⟩ :=
    frozen_length_distinct_of_large_mean rowsSimple rowsFree (by decide) hp mean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,retention,upper,caps⟩

end OnlineReachabilityPreservers
