import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Projection of half bridges through cutoff five under vertex and path splits. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

section

variable {I V W : Type*} [LinearOrder I] [DecidableEq V] [DecidableEq W]

/-- A projected half-five bridge can only identify the two endpoints of
its last two-step return. The shortened bridge has its last arc after
the river in the original arrival order. -/
theorem HalfBridgeFree.project_half_five_terminal_collision {paths : I → List V} {copies : I → List W}
    (free : HalfBridgeFree (Before paths) 5) (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y))
    (b : Bridge (Before copies) 3) (earlier : b.arc (Fin.last 3) < b.river) :
    project (b.vertex 2) = project (b.vertex 4) ∧ b.river < b.arc 1 := by
  let v := project ∘ b.vertex
  have first : Before paths (b.arc 0) (v 0) (v 1) := steps (b.arcStep 0)
  have second : Before paths (b.arc 1) (v 1) (v 2) := steps (b.arcStep 1)
  have third : Before paths (b.arc 2) (v 2) (v 3) := steps (b.arcStep 2)
  have last : Before paths (b.arc 3) (v 3) (v 4) := steps (b.arcStep 3)
  have river : Before paths b.river (v 0) (v 4) := steps b.riverStep
  have ne01 := listBefore_ne first
  have ne12 := listBefore_ne second
  have ne23 := listBefore_ne third
  have ne34 := listBefore_ne last
  have ne04 := listBefore_ne river
  have distinctArcs {i j : Fin 4} (different : i ≠ j) : b.arc i ≠ b.arc j :=
    fun eq => different (b.distinctArcs eq)
  have noParallel {i : Fin 4} (step : Before paths (b.arc i) (v 0) (v 4)) : False :=
    no_parallel_list_steps free (by decide) (b.river_ne_arc i) river step
  have ne02 : v 0 ≠ v 2 := by
    intro eq
    have step : Before paths (b.arc 2) (v 0) (v 3) := eq.symm ▸ third
    exact free (by decide)
      (threeListBridge (distinctArcs (by decide : (2:Fin 4) ≠ 3))
        (b.river_ne_arc 2) (b.river_ne_arc 3) step last river) earlier
  have ne03 : v 0 ≠ v 3 := fun eq => noParallel (i := 3) (eq.symm ▸ last)
  have ne13 : v 1 ≠ v 3 := by
    intro eq
    have step : Before paths (b.arc 3) (v 1) (v 4) := eq.symm ▸ last
    exact free (by decide)
      (threeListBridge (distinctArcs (by decide : (0:Fin 4) ≠ 3))
        (b.river_ne_arc 0) (b.river_ne_arc 3) first step river) earlier
  have ne14 : v 1 ≠ v 4 := fun eq => noParallel (i := 0) (eq ▸ first)
  have returns : v 2 = v 4 := by
    by_contra ne24
    have injective : Function.Injective v := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> simp_all
    let old : Bridge (Before paths) 3 :=
      ⟨v,b.arc,b.river,injective,b.distinctArcs,b.river_ne_arc,
        steps b.riverStep,fun i => steps (b.arcStep i)⟩
    exact free (by decide) old earlier
  let small := threeListBridge (distinctArcs (by decide : (0:Fin 4) ≠ 1))
    (b.river_ne_arc 0) (b.river_ne_arc 1) first (returns ▸ second) river
  have notEarlier : ¬b.arc 1 < b.river := by
    intro h
    apply free (by decide) small
    simpa [small,threeListBridge] using h
  exact ⟨returns,lt_of_le_of_ne (le_of_not_gt notEarlier) (b.river_ne_arc 1)⟩

/-- Preserving the endpoint label of each projected two-step return
is enough to preserve half exclusion through size five. -/
theorem HalfBridgeFree.split_list_vertices_five_of_no_split_return {paths : I → List V} {copies : I → List W}
    (free : HalfBridgeFree (Before paths) 5) (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y))
    (noReturn : ∀ {i j x y z}, Before copies i x y → Before copies j y z →
      project x = project z → x = z) :
    HalfBridgeFree (Before copies) 5 := by
  intro d small b earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
    have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => steps)
    exact safe (by omega) b earlier
  · have size : d = 3 := by omega
    subst d
    have returns := (free.project_half_five_terminal_collision project (fun {_ _ _} => steps) b earlier).1
    have collapsed := noReturn (b.arcStep 2) (b.arcStep 3) returns
    exact (by decide : (2:Fin 5) ≠ 4) (b.distinctVertices collapsed)

end

section UniqueFive

variable {I J V W : Type*} [LinearOrder I] [LinearOrder J]
  [DecidableEq V] [DecidableEq W]

/-- Unique intersections rule out a projected terminal return, so no
full-bridge assumption is needed for the half-five vertex projection. -/
theorem HalfBridgeFree.split_list_vertices_five_of_unique {paths : I → List V} {copies : I → List W}
    (free : HalfBridgeFree (Before paths) 5) (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y))
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    HalfBridgeFree (Before copies) 5 := by
  apply free.split_list_vertices_five_of_no_split_return project (fun {_ _ _} => steps)
  intro i j x y z first second returns
  have before := steps first
  have after : Before paths j (project y) (project x) := returns.symm ▸ steps second
  by_cases same : i = j
  · subst j
    exact (lt_asymm before.2.2 after.2.2).elim
  · exact (listBefore_ne before (unique same before.1 after.2.1 before.2.1 after.1)).elim

/-- With unique intersections, disjoint path pieces project all five
bridge slots to distinct parent rows and keep the arrival comparison. -/
theorem HalfBridgeFree.split_list_paths_five_of_unique {paths : I → List V} {pieces : J → List V}
    (free : HalfBridgeFree (Before paths) 5)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    HalfBridgeFree (Before pieces) 5 := by
  intro d small b earlier
  let old := listBridge_after_opposite_safe_split_through_five parent (fun {_ _ _} => steps)
    (fun {_ _ _} => apart)
    (fun _ {_ _ _ _} different one two => no_parallel_list_steps free (by decide) different one two)
    (fun _ {_ _ _ _ _} _ different forward reverse _ _ => False.elim
      (listBefore_ne forward (unique different forward.1 (steps reverse).2.1 forward.2.1 (steps reverse).1)))
    (by omega) b
  apply free small old
  exact lt_of_le_of_ne (monotone earlier.le) (old.river_ne_arc _).symm

end UniqueFive

open scoped Sigma.Lex

/-- Both consecutive width splits preserve half exclusion through five on
a simple family with unique pairwise intersections. -/
theorem listRegularizedPaths_halfFree_five_of_unique {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (D L : ℕ) : HalfBridgeFree (Before (listRegularizedPaths paths D L)) 5 := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  have freeCopies : HalfBridgeFree (Before copies) 5 :=
    free.split_list_vertices_five_of_unique (·.fst)
      (fun {i _ _} => splitListVertices_step (simple i)) (fun {_ _ _ _} => unique)
  have nodup (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  exact freeCopies.split_list_paths_five_of_unique Sigma.fst
    (block_parent_mono (fun i => (copies i).toFinset) L)
    (fun {i _ _} step => listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := pieces) (nodup i.fst) List.filter_sublist step)
    (fun {_ _ _} => splitListPaths_disjoint)
    (fun {_ _ _ _} => splitListVertices_unique simple (fun {_ _ _ _} => unique))

/-- Five-half-bridge exclusion and unique intersections suffice for frozen
cleaning through the original vertex and path budgets. -/
theorem regularization_list_frozen_half_five_of_unique {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass (half := true) (k := 5) (retention := 16)
    paths simple (listRegularizedPaths_halfFree_five_of_unique simple free (fun {_ _ _ _} => unique) (4*M/n) (4*M/p))
    hn hp dense long le_rfl (by ring_nf; omega)

end OnlineReachabilityPreservers
