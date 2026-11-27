import OnlineReachabilityPreservers.ComponentSplitCleaning
import OnlineReachabilityPreservers.HalfFiveDegreeRepair

/-! Only returns to earlier degree blocks can break half-bridge projection. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- Forbid bounded walks that return to a strictly earlier copy of the
same projected vertex. -/
def NoShortBackwardProjection {I V W : Type*} (steps : I → W → W → Prop)
    (project : W → V) (rank : W → ℕ) (cutoff : ℕ) : Prop :=
  ∀ {d : ℕ} (vertex : Fin (d+1) → W) (row : Fin d → I),
    d ≤ cutoff →
    (∀ j, steps (row j) (vertex j.castSucc) (vertex j.succ)) →
    project (vertex 0) = project (vertex (Fin.last d)) →
    rank (vertex (Fin.last d)) < rank (vertex 0) → False

set_option maxHeartbeats 1200000 in
/-- Copy ranks monotone at arriving terminal incidences allow the
last arc of a projected half-bridge to be recovered. -/
theorem HalfBridgeFree.of_noShortBackwardProjection {I V W : Type*}
    [LinearOrder I] [DecidableEq V] {before : I → V → V → Prop}
    {copied : I → W → W → Prop} {k : ℕ}
    (free : HalfBridgeFree before k) (project : W → V) (rank : W → ℕ)
    (labels : ∀ {x y}, project x = project y → rank x = rank y → x = y)
    (step : ∀ {i x y}, copied i x y → before i (project x) (project y))
    (stepNe : ∀ {i x y}, before i x y → x ≠ y)
    (ordered : ∀ {i j s t x y}, i ≤ j → copied i s x → copied j t y →
      project x = project y → rank x ≤ rank y)
    (safe : NoShortBackwardProjection copied project rank (k-3)) :
    HalfBridgeFree copied k := by
  classical
  intro d small b earlier
  let last := Fin.last (d+1)
  let hits := (univ : Finset (Fin (d+1))).filter
    fun j => project (b.vertex j.castSucc) = project (b.vertex last)
  by_cases nonempty : hits.Nonempty
  · obtain ⟨i,iOn,first⟩ := exists_min_image hits Fin.val nonempty
    have same := (mem_filter.mp iOn).2
    have pastFirst : 2 ≤ i.val := by
      by_contra! earlyCorner
      have zeroOrOne : i.val = 0 ∨ i.val = 1 := by omega
      rcases zeroOrOne with atStart | atNext
      · have eq : i.castSucc = 0 := Fin.ext atStart
        rw [eq] at same
        exact stepNe (step b.riverStep) same
      · have eq : i.castSucc = (0 : Fin (d+1)).succ := Fin.ext atNext
        have parallel := step (b.arcStep 0)
        rw [← eq,same] at parallel
        exact free.no_parallel_steps (by omega) (b.river_ne_arc 0)
          (stepNe (step b.riverStep)) (step b.riverStep) parallel
    let m := i.val-1
    let pos (j : Fin (m+2)) : Fin (d+2) := Fin.castLE (by dsimp [m]; omega) j
    let arcPos (j : Fin (m+1)) : Fin (d+1) := Fin.castLE (by dsimp [m]; omega) j
    have plainLeft (j : Fin (m+1)) : pos j.castSucc = (arcPos j).castSucc := Fin.ext rfl
    have plainRight (j : Fin (m+1)) : pos j.succ = (arcPos j).succ := Fin.ext rfl
    have prefixEnd : pos (Fin.last (m+1)) = i.castSucc := Fin.ext (by dsimp [pos,m]; omega)
    let pulled (j : I) (u v : W) := before j (project u) (project v)
    let prefixBridge : Bridge pulled m := by
      refine ⟨b.vertex ∘ pos,b.arc ∘ arcPos,b.river,
        b.distinctVertices.comp (Fin.castLE_injective _), b.distinctArcs.comp (Fin.castLE_injective _),
        fun j => b.river_ne_arc (arcPos j),?_,?_⟩
      · change before b.river (project (b.vertex 0)) (project (b.vertex (pos (Fin.last (m+1)))))
        rw [prefixEnd,same]
        exact step b.riverStep
      · intro j
        change before (b.arc (arcPos j)) (project (b.vertex (pos j.castSucc))) (project (b.vertex (pos j.succ)))
        rw [plainLeft,plainRight]
        exact step (b.arcStep (arcPos j))
    have terminal (j : Fin (m+1)) :
        project (prefixBridge.vertex j.castSucc) ≠ project (prefixBridge.vertex (Fin.last (m+1))) := by
      intro equal
      change project (b.vertex (pos j.castSucc)) = project (b.vertex (pos (Fin.last (m+1)))) at equal
      rw [plainLeft,prefixEnd,same] at equal
      have earlierHit : arcPos j ∈ hits := mem_filter.mpr ⟨mem_univ _,equal⟩
      have noEarlier := first (arcPos j) earlierHit
      change i.val ≤ j.val at noEarlier
      have fits := j.isLt
      dsimp [m] at fits
      omega
    obtain ⟨j,bound,old,river,lastArc⟩ := prefixBridge.project_vertices_preserving_last project
      (after := before) (fun {_ _ _} found => found) (fun {_ _ _} found => stepNe found) terminal
    have lastLabel : old.arc (Fin.last j) = b.arc (arcPos (Fin.last m)) := lastArc
    have riverLabel : old.river = b.river := river
    have noEarlier : ¬ b.arc (arcPos (Fin.last m)) < b.river := by
      intro order
      exact free (show j+2 ≤ k by dsimp [m] at bound; omega) old (by simpa only [lastLabel,riverLabel] using order)
    have riverFirst : b.river < b.arc (arcPos (Fin.last m)) :=
      lt_of_le_of_ne (le_of_not_gt noEarlier) (b.river_ne_arc _)
    have target : (arcPos (Fin.last m)).succ = i.castSucc := Fin.ext (by dsimp [arcPos,m]; omega)
    have onPrefix : copied (b.arc (arcPos (Fin.last m)))
        (b.vertex (arcPos (Fin.last m)).castSucc) (b.vertex i.castSucc) := by
      rw [← target]
      exact b.arcStep (arcPos (Fin.last m))
    have earlierBlock := ordered riverFirst.le b.riverStep onPrefix same.symm
    have distinctBlocks : rank (b.vertex last) ≠ rank (b.vertex i.castSucc) := by
      intro sameBlock
      have equal := b.distinctVertices (labels same.symm sameBlock)
      have values := congrArg Fin.val equal
      change d+1 = i.val at values
      omega
    have backwards : rank (b.vertex last) < rank (b.vertex i.castSucc) :=
      earlierBlock.lt_of_ne distinctBlocks
    let t := d+1-i.val
    have tFit : t ≤ k-3 := by unfold t; omega
    let position (j : Fin (t+1)) : Fin (d+2) := ⟨i.val+j.val,by unfold t at j; omega⟩
    let v (j : Fin (t+1)) := b.vertex (position j)
    let rowIdx (j : Fin t) : Fin (d+1) := ⟨i.val+j.val,by unfold t at j; omega⟩
    let row (j : Fin t) := b.arc (rowIdx j)
    have start : position 0 = i.castSucc := Fin.ext (by simp [position])
    have finish : position (Fin.last t) = last := Fin.ext (by simp [position,t,last])
    have tailSteps (j : Fin t) : copied (row j) (v j.castSucc) (v j.succ) := by
      have left : position j.castSucc = (rowIdx j).castSucc := Fin.ext rfl
      have right : position j.succ = (rowIdx j).succ := Fin.ext (by simp [position,rowIdx,Nat.add_assoc])
      simpa only [v,row,left,right] using b.arcStep (rowIdx j)
    apply safe v row tFit tailSteps
    · simpa only [v,start,finish] using same
    · simpa only [v,start,finish] using backwards
  · have noHits {i : Fin (d+1)} (equal : project (b.vertex i.castSucc) = project (b.vertex last)) : False :=
      nonempty ⟨i,mem_filter.mpr ⟨mem_univ _,equal⟩⟩
    obtain ⟨j,size,old,river,lastArc⟩ := b.project_vertices_preserving_last project
      (fun {_ _ _} => step) (fun {_ _ _} found => stepNe found) (fun _ => noHits)
    exact free (show j+2 ≤ k by omega) old (by simpa only [river,lastArc] using earlier)

/-- A bounded walk in the supplied copied rows cannot return to an
earlier copy of its starting vertex. -/
def NoShortBackwardCopyReturnIn {n p D : ℕ} {paths : Fin p → List (Fin n)}
    (rows : Fin p → List (ListVertexBlockIndex paths D)) (cutoff : ℕ) : Prop :=
  NoShortBackwardProjection (Before rows) (·.fst) (fun x => x.snd.val) cutoff

/-- A short copied walk cannot return to an earlier block of its
original starting vertex. -/
def NoShortBackwardCopyReturn {n p : ℕ} (paths : Fin p → List (Fin n)) (D cutoff : ℕ) : Prop :=
  NoShortBackwardCopyReturnIn (splitListVertices paths D) cutoff

theorem NoShortSplitReturn.noShortBackwardCopyReturn {n p D cutoff : ℕ}
    {paths : Fin p → List (Fin n)}
    (safe : NoShortSplitReturn (splitListVertices paths D) (·.fst) cutoff) :
    NoShortBackwardCopyReturn paths D cutoff := by
  dsimp only [NoShortBackwardCopyReturn]
  intro d vertex row short steps same backwards
  have equal := safe vertex row short steps same
  change (vertex (Fin.last d)).snd.val < (vertex 0).snd.val at backwards
  exact (lt_irrefl _) (congrArg (fun w : ListVertexBlockIndex paths D => w.snd.val) equal ▸ backwards)

set_option maxHeartbeats 1200000 in
/-- If the projected terminal corner occurs earlier in a copied bridge,
its first occurrence is reached by an arc later than the river. Its
degree block is therefore later than the terminal block on any
rowwise restriction of the original copied rows. -/
theorem copied_subrows_halfFree_of_noShortBackwardCopyReturn {n p k D : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (kept : Fin p → List (ListVertexBlockIndex paths D))
    (sub : ∀ i, (kept i).Sublist (splitListVertices paths D i))
    (free : HalfBridgeFree (Before paths) k) (safe : NoShortBackwardCopyReturnIn kept (k-3)) :
    HalfBridgeFree (Before kept) k := by
  let project (x : ListVertexBlockIndex paths D) := x.fst
  let rank (x : ListVertexBlockIndex paths D) := x.snd.val
  have steps {i x y} (found : Before kept i x y) : Before paths i (project x) (project y) :=
    splitListVertices_step (simple i)
      (listBefore_of_sublist (splitListVertices_simple paths D i (simple i)) (sub i) found)
  exact free.of_noShortBackwardProjection project rank
    (fun {_ _} => vertexBlock_eq_of_same_label) (fun {_ _ _} => steps)
    (fun {_ _ _} => listBefore_ne)
    (fun {_ _ _ _ _ _} arrival left right same =>
      splitListVertices_block_mono same arrival ((sub _).subset left.2.1) ((sub _).subset right.2.1))
    safe

/-- The earlier-block return test applies to the full copied rows. -/
theorem splitListVertices_halfFree_of_noShortBackwardCopyReturn {n p k D : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (safe : NoShortBackwardCopyReturn paths D (k-3)) :
    HalfBridgeFree (Before (splitListVertices paths D)) k :=
  copied_subrows_halfFree_of_noShortBackwardCopyReturn paths simple (splitListVertices paths D)
    (fun _ => List.Sublist.refl _) free safe


private theorem reachIn_of_fin_steps {V : Type*} [DecidableEq V] {G : Arcs V} {d : ℕ}
    (vertex : Fin (d+1) → V)
    (steps : ∀ i : Fin d, Edge G (vertex i.castSucc) (vertex i.succ)) :
    vertex 0 ∈ reachIn G (vertex (Fin.last d)) d := by
  induction d with
  | zero =>
    change vertex 0 ∈ reachIn G (vertex 0) 0
    exact target_mem_reachIn G _ 0
  | succ d shorter =>
    apply reachIn_succ.mpr
    exact Or.inr ⟨vertex (Fin.succ 0),steps 0,
      shorter (vertex ∘ Fin.succ) (fun i => steps i.succ)⟩

/-- An edge superset can be used to check short backward returns. -/
theorem NoShortBackwardProjection.of_bounded_reach {I V W : Type*} [DecidableEq W]
    {steps : I → W → W → Prop} {project : W → V} {rank : W → ℕ} {G : Arcs W}
    {cutoff : ℕ} (edge : ∀ {i x y}, steps i x y → Edge G x y)
    (noBack : ∀ {x y}, project x = project y → rank y < rank x → x ∉ reachIn G y cutoff) :
    NoShortBackwardProjection steps project rank cutoff := by
  intro d vertex row short route same backwards
  have found : vertex 0 ∈ reachIn G (vertex (Fin.last d)) d :=
    reachIn_of_fin_steps vertex (fun i => edge (route i))
  have monotone : Monotone (reachIn G (vertex (Fin.last d))) :=
    monotone_nat_of_le_succ (reachIn_subset_succ G (vertex (Fin.last d)))
  exact noBack same backwards (monotone short found)

/-- Bounded reachability in the supplied rows certifies the
earlier-block return test. -/
theorem NoShortBackwardCopyReturnIn.of_reachIn {n p D cutoff : ℕ} {paths : Fin p → List (Fin n)}
    (rows : Fin p → List (ListVertexBlockIndex paths D))
    (noBack : ∀ {x y : ListVertexBlockIndex paths D}, x.fst = y.fst → y.snd.val < x.snd.val →
      x ∉ reachIn (listPiecePrecedenceGraph rows) y cutoff) :
    NoShortBackwardCopyReturnIn rows cutoff :=
  NoShortBackwardProjection.of_bounded_reach (G := listPiecePrecedenceGraph rows)
    (fun {i _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨i,step⟩) noBack

/-- The bounded search in the copied rows certifies the absence of a
return to an earlier block. -/
theorem NoShortBackwardCopyReturn.of_reachIn {n p D cutoff : ℕ} {paths : Fin p → List (Fin n)}
    (noBack : ∀ {x y : ListVertexBlockIndex paths D}, x.fst = y.fst → y.snd.val < x.snd.val →
      x ∉ reachIn (listPiecePrecedenceGraph (splitListVertices paths D)) y cutoff) :
    NoShortBackwardCopyReturn paths D cutoff :=
  NoShortBackwardCopyReturnIn.of_reachIn (splitListVertices paths D) noBack

/-- Test only returns to earlier degree blocks and returns across width
cuts in the actual pieces. The frozen averages and budgets stay fixed. -/
theorem regularization_list_frozen_half_of_noShortBackwardCopyReturn {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (degreeSafe : let M := ∑ i, (paths i).length
      NoShortBackwardCopyReturn paths (4*M/n) (k-3))
    (returns : let M := ∑ i, (paths i).length
      NoShortReturnAcrossCopiedWidthCuts paths (4*M/n) (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have safe := splitListVertices_halfFree_of_noShortBackwardCopyReturn paths simple free degreeSafe
  have admissible := listRegularizedPaths_admissible_of_noShortReturnAcrossCopiedWidthCuts
    (half := true) paths simple safe returns
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple admissible hn hp dense long le_rfl (by omega)

/-- Repair the degree-copy projection by deleting incidences before
testing the two kinds of short return. Keep the original copy labels and
both original widths. -/
theorem regularization_list_frozen_half_after_copied_return_deletions {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (kept : let M := ∑ i, (paths i).length; Fin p → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length; ∀ i, (kept i).Sublist (splitListVertices paths (4*M/n) i))
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length))
    (degreeSafe : NoShortBackwardCopyReturnIn kept (k-3))
    (returns : let M := ∑ i, (paths i).length; NoShortReturnAcrossWidthCutsInPieces kept (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have keptFree := copied_subrows_halfFree_of_noShortBackwardCopyReturn paths simple kept sub free degreeSafe
  exact regularization_list_frozen_of_admissible_copied_row_deletions (half := true)
    paths simple hn hp dense long kept sub keptFree retained returns


/-- Any ordered choice of degree copies can be used at the original
widths. The copied alphabet has its own upper support bound. -/
theorem regularization_list_frozen_half_of_ranked_degree_rows {n p k : ℕ} {W : Type*}
    [LinearOrder W] [Fintype W] (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (rows : Fin p → List W) (project : W → Fin n) (rank : W → ℕ)
    (sameRows : ∀ i, (rows i).map project = paths i)
    (labels : ∀ {x y}, project x = project y → rank x = rank y → x = y)
    (ordered : ∀ {i j s t x y}, i ≤ j → Before rows i s x → Before rows j t y →
      project x = project y → rank x ≤ rank y)
    (degreeSafe : NoShortBackwardProjection (Before rows) project rank (k-3))
    (widthSafe : let M := ∑ i, (paths i).length; NoShortReturnAcrossWidthCutsInPieces rows (4*M/p) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (count : 3*Fintype.card W ≤ 4*n)
    (degree : ∀ w, (occurrences (fun i => (rows i).toFinset) w).card ≤ 4*(∑ i, (paths i).length)/n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have mapSimple (i : Fin p) : ((rows i).map project).Nodup := (sameRows i).symm ▸ simple i
  have rowSimple (i : Fin p) : (rows i).Nodup := List.Nodup.of_map project (mapSimple i)
  have step {i x y} (h : Before rows i x y) : Before paths i (project x) (project y) := by
    simpa only [sameRows] using listBefore_map project (mapSimple i) h
  have copiedFree : HalfBridgeFree (Before rows) k :=
    free.of_noShortBackwardProjection project rank (fun {_ _} => labels)
      (fun {_ _ _} => step) (fun {_ _ _} => listBefore_ne) (fun {_ _ _ _ _ _} => ordered) degreeSafe
  have sameMass : (∑ i, (rows i).length) = ∑ i, (paths i).length := sum_congr rfl (fun i _ => by
    rw [← sameRows i, List.length_map])
  exact regularization_list_frozen_of_safe_width_pieces (half := true) rows rowSimple copiedFree widthSafe
    hn hp dense long count degree sameMass


/-- A gap in arrival order is safe at a vertex if a short return cannot
start on a later row and end on an earlier row across that gap. -/
def IsSafeDegreeReturnGap {n p : ℕ} (paths : Fin p → List (Fin n))
    (v : Fin n) (gap radius : ℕ) : Prop :=
  radius < 2 ∨ ∀ ⦃a b : Fin p⦄ ⦃x y : Fin n⦄, b.val < gap → gap ≤ a.val →
    Before paths a v x → Before paths b y v →
    x ∉ reachIn (listPiecePrecedenceGraph paths) y (radius-2)

set_option maxHeartbeats 1200000 in
/-- A copy assignment can use any safe gap separating its different
ranks. The test uses the original comparisons and the rows supplying
the first and last steps of a possible return. -/
theorem NoShortBackwardProjection.of_safe_degree_return_gaps {n p radius : ℕ} {W : Type*} [DecidableEq W]
    (paths : Fin p → List (Fin n)) (rows : Fin p → List W) (project : W → Fin n) (rank : W → ℕ)
    (projectStep : ∀ {i x y}, Before rows i x y → Before paths i (project x) (project y))
    (separates : ∀ {a b x y s t}, Before rows a x s → Before rows b t y →
      project x = project y → rank y < rank x →
      ∃ gap, b.val < gap ∧ gap ≤ a.val ∧ IsSafeDegreeReturnGap paths (project x) gap radius) :
    NoShortBackwardProjection (Before rows) project rank radius := by
  intro d vertex row short steps same backwards
  have two : 2 ≤ d := by
    by_contra! one
    have choices : d = 0 ∨ d = 1 := by omega
    rcases choices with rfl | rfl
    · have eq : Fin.last 0 = (0 : Fin 1) := rfl
      rw [eq] at backwards
      exact (lt_irrefl _) backwards
    · have edge := projectStep (steps 0)
      have firstEq : (0 : Fin 1).castSucc = 0 := rfl
      have lastEq : (0 : Fin 1).succ = Fin.last 1 := rfl
      exact listBefore_ne edge (by simpa only [firstEq,lastEq] using same)
  obtain ⟨q,rfl⟩ : ∃ q, d = q+2 := ⟨d-2,by omega⟩
  let first : Fin (q+2) := 0
  let last := Fin.last (q+1)
  have firstStep : Before rows (row first) (vertex 0) (vertex first.succ) := steps first
  have lastStep : Before rows (row last) (vertex last.castSucc) (vertex (Fin.last (q+2))) := by
    simpa only [last,Fin.succ_last] using steps last
  obtain ⟨gap,early,late,safe⟩ := separates firstStep lastStep same backwards
  let place (i : Fin (q+1)) : Fin (q+3) := i.succ.castSucc
  let middle (i : Fin (q+1)) := project (vertex (place i))
  have middleSteps (i : Fin q) : Edge (listPiecePrecedenceGraph paths) (middle i.castSucc) (middle i.succ) := by
    let index : Fin (q+2) := i.succ.castSucc
    have sourceIndex : place i.castSucc = index.castSucc := Fin.ext rfl
    have toward : place i.succ = index.succ := Fin.ext rfl
    exact listPiecePrecedenceGraph_edge.mpr ⟨row index,by
      simpa only [middle,sourceIndex,toward] using projectStep (steps index)⟩
  have reached := reachIn_of_fin_steps middle middleSteps
  have sourceIndex : place 0 = first.succ := Fin.ext rfl
  have toward : place (Fin.last q) = last.castSucc := Fin.ext rfl
  change project (vertex (place 0)) ∈ reachIn (listPiecePrecedenceGraph paths)
    (project (vertex (place (Fin.last q)))) q at reached
  rw [sourceIndex,toward] at reached
  have endStep := projectStep lastStep
  rw [← same] at endStep
  apply safe.resolve_left (by omega) early late (projectStep firstStep) endStep
  exact (monotone_nat_of_le_succ (reachIn_subset_succ _ _) (show q ≤ radius-2 by omega)) reached

open scoped Classical in
/-- The latest chosen cut of one vertex at or before the row arrives. -/
noncomputable def degreeReturnGapRank {n p : ℕ} (cuts : Fin n → Finset ℕ)
    (v : Fin n) (i : Fin p) : ℕ :=
  ((cuts v).filter fun gap => gap ≤ i.val).sup id

/-- Ranks increase only across a chosen gap. -/
theorem degreeReturnGapRank_lt_iff {n p : ℕ} {cuts : Fin n → Finset ℕ}
    {v : Fin n} {i j : Fin p} :
    degreeReturnGapRank cuts v i < degreeReturnGapRank cuts v j ↔
      ∃ gap ∈ cuts v, i.val < gap ∧ gap ≤ j.val := by
  constructor
  · intro increasing
    by_contra! none
    have atMost : degreeReturnGapRank cuts v j ≤ degreeReturnGapRank cuts v i := by
      unfold degreeReturnGapRank
      apply Finset.sup_le
      intro gap atJ
      have chosen := (mem_filter.mp atJ).1
      have byJ := (mem_filter.mp atJ).2
      have byI : gap ≤ i.val := by
        by_contra! afterI
        exact (none gap chosen afterI).not_ge byJ
      exact Finset.le_sup (f := id) (mem_filter.mpr ⟨chosen,byI⟩)
    exact increasing.not_ge atMost
  · rintro ⟨gap,chosen,byI,byJ⟩
    have before : degreeReturnGapRank cuts v i ≤ i.val := by
      unfold degreeReturnGapRank
      exact Finset.sup_le (fun _ atI => (mem_filter.mp atI).2)
    have after : gap ≤ degreeReturnGapRank cuts v j :=
      Finset.le_sup (f := id) (mem_filter.mpr ⟨chosen,byJ⟩)
    exact (before.trans_lt byI).trans_le after

/-- The degree copy labels are the occupied pairs of vertex and rank. -/
noncomputable def degreeReturnGapAlphabet {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) : Finset (Fin n ×ₗ ℕ) :=
  univ.biUnion fun i : Fin p =>
    (paths i).toFinset.image (fun v => toLex (v,degreeReturnGapRank cuts v i))

abbrev DegreeReturnGapCopy {n p : ℕ} (paths : Fin p → List (Fin n)) (cuts : Fin n → Finset ℕ) :=
  ↥(degreeReturnGapAlphabet paths cuts)

private def degreeReturnGapProject {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cuts : Fin n → Finset ℕ} (x : DegreeReturnGapCopy paths cuts) : Fin n :=
  (ofLex x.val).1

private def degreeReturnGapBlock {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cuts : Fin n → Finset ℕ} (x : DegreeReturnGapCopy paths cuts) : ℕ :=
  (ofLex x.val).2

private noncomputable def degreeReturnGapCopyAt {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (i : Fin p) (v : {v // v ∈ paths i}) :
    DegreeReturnGapCopy paths cuts :=
  ⟨toLex (v.val,degreeReturnGapRank cuts v.val i),
    mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨v.val,List.mem_toFinset.mpr v.property,rfl⟩⟩⟩

/-- Apply the chosen degree cuts without changing any row positions. -/
noncomputable def splitListVerticesAtReturnGaps {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (i : Fin p) : List (DegreeReturnGapCopy paths cuts) :=
  (paths i).attach.map (degreeReturnGapCopyAt paths cuts i)

theorem splitListVerticesAtReturnGaps_project {n p : ℕ} (paths : Fin p → List (Fin n))
    (cuts : Fin n → Finset ℕ) (i : Fin p) :
    (splitListVerticesAtReturnGaps paths cuts i).map degreeReturnGapProject = paths i := by
  unfold splitListVerticesAtReturnGaps
  rw [List.map_map]
  exact List.attach_map_subtype_val _

private theorem degreeReturnGap_copy_eq {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cuts : Fin n → Finset ℕ} {x y : DegreeReturnGapCopy paths cuts}
    (project : degreeReturnGapProject x = degreeReturnGapProject y)
    (rank : degreeReturnGapBlock x = degreeReturnGapBlock y) : x = y :=
  Subtype.ext (ofLex.injective (Prod.ext project rank))

private theorem mem_splitListVerticesAtReturnGaps {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cuts : Fin n → Finset ℕ} {i : Fin p} {x : DegreeReturnGapCopy paths cuts} :
    x ∈ splitListVerticesAtReturnGaps paths cuts i ↔
      degreeReturnGapProject x ∈ paths i ∧
      degreeReturnGapBlock x = degreeReturnGapRank cuts (degreeReturnGapProject x) i := by
  constructor
  · intro on
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp on
    exact ⟨v.property,rfl⟩
  · rintro ⟨present,rank⟩
    apply List.mem_map.mpr
    refine ⟨⟨degreeReturnGapProject x,present⟩,by simp,?_⟩
    exact degreeReturnGap_copy_eq rfl rank.symm

set_option maxHeartbeats 1200000 in
/-- Use any selected safe degree gaps with the original upper caps. The
copy budget counts only labels that occur in at least one row. -/
theorem regularization_list_frozen_half_of_safe_degree_gaps {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (cuts : Fin n → Finset ℕ)
    (safe : ∀ v gap, gap ∈ cuts v → IsSafeDegreeReturnGap paths v gap (k-3))
    (widthSafe : let M := ∑ i, (paths i).length
      NoShortReturnAcrossWidthCutsInPieces (splitListVerticesAtReturnGaps paths cuts) (4*M/p) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (count : 3*(degreeReturnGapAlphabet paths cuts).card ≤ 4*n)
    (load : let M := ∑ i, (paths i).length
      ∀ v rank, ((univ : Finset (Fin p)).filter
        fun i => v ∈ paths i ∧ degreeReturnGapRank cuts v i = rank).card ≤ 4*M/n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let rows := splitListVerticesAtReturnGaps paths cuts
  let W := DegreeReturnGapCopy paths cuts
  let project (x : W) := degreeReturnGapProject x
  let block (x : W) := degreeReturnGapBlock x
  have rowRank {i x} (on : x ∈ rows i) : block x = degreeReturnGapRank cuts (project x) i :=
    (mem_splitListVerticesAtReturnGaps.mp on).2
  have rowRanks {a b x y} (left : x ∈ rows a) (right : y ∈ rows b) (same : project x = project y)
      (different : block y < block x) :
      ∃ gap ∈ cuts (project x), b.val < gap ∧ gap ≤ a.val := by
    rw [rowRank right, rowRank left, ← same] at different
    exact degreeReturnGapRank_lt_iff.mp different
  have projects {i x y} (edge : Before rows i x y) : Before paths i (project x) (project y) := by
    have sameRows := splitListVerticesAtReturnGaps_project paths cuts i
    have nodup : ((rows i).map project).Nodup := sameRows.symm ▸ simple i
    have step := listBefore_map project nodup edge
    have eqRows : (fun j => (rows j).map project) = paths :=
      funext (splitListVerticesAtReturnGaps_project paths cuts)
    rwa [eqRows] at step
  have admissible : NoShortBackwardProjection (Before rows) project block (k-3) := by
    apply NoShortBackwardProjection.of_safe_degree_return_gaps paths rows project block (fun {_ _ _} => projects)
    intro a b x y s t start finish same different
    obtain ⟨gap,chosen,early,late⟩ := rowRanks start.1 finish.2.1 same different
    exact ⟨gap,early,late,safe (project x) gap chosen⟩
  have capacity (x : W) : (occurrences (fun i => (rows i).toFinset) x).card ≤
      4*(∑ i, (paths i).length)/n := by
    have on : occurrences (fun i => (rows i).toFinset) x = (univ : Finset (Fin p)).filter
        (fun i => project x ∈ paths i ∧ degreeReturnGapRank cuts (project x) i = block x) := by
      ext i
      rw [mem_occurrences,List.mem_toFinset,mem_splitListVerticesAtReturnGaps,mem_filter]
      simp only [mem_univ,true_and,project,block,eq_comm]
    rw [on]
    exact load (project x) (block x)
  refine regularization_list_frozen_half_of_ranked_degree_rows paths simple free rows project block
    (splitListVerticesAtReturnGaps_project paths cuts) (fun {_ _} => degreeReturnGap_copy_eq)
    ?_ admissible widthSafe hn hp dense long (by simpa only [W,Fintype.card_coe] using count) capacity
  intro i j s t x y arrives left right same
  by_contra! backwards
  obtain ⟨_,_,early,late⟩ := rowRanks left.2.1 right.2.1 same backwards
  change i.val ≤ j.val at arrives
  exact early.not_ge (late.trans arrives)
end OnlineReachabilityPreservers
