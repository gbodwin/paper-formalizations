import OnlineReachabilityPreservers.ComponentSplitCleaning
import OnlineReachabilityPreservers.HalfFiveDegreeRepair

/-! Only returns to earlier degree blocks can break half-bridge projection. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- A bounded walk in the supplied copied rows cannot return to an
earlier copy of its starting vertex. -/
def NoShortBackwardCopyReturnIn {n p D : ℕ} {paths : Fin p → List (Fin n)}
    (rows : Fin p → List (ListVertexBlockIndex paths D)) (cutoff : ℕ) : Prop :=
  ∀ {d : ℕ} (vertex : Fin (d+1) → ListVertexBlockIndex paths D) (row : Fin d → Fin p),
    d ≤ cutoff →
    (∀ j, Before rows (row j) (vertex j.castSucc) (vertex j.succ)) →
    (vertex 0).fst = (vertex (Fin.last d)).fst →
    (vertex (Fin.last d)).snd.val < (vertex 0).snd.val → False

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
  classical
  let copies := kept
  let V := ListVertexBlockIndex paths D
  let project (x : V) := x.fst
  have step {i x y} (found : Before copies i x y) : Before paths i (project x) (project y) :=
    splitListVertices_step (simple i)
      (listBefore_of_sublist (splitListVertices_simple paths D i (simple i)) (sub i) found)
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
        exact listBefore_ne (step b.riverStep) same
      · have eq : i.castSucc = (0 : Fin (d+1)).succ := Fin.ext atNext
        have parallel := step (b.arcStep 0)
        rw [← eq,same] at parallel
        exact no_parallel_list_steps free (by omega) (b.river_ne_arc 0) (step b.riverStep) parallel
    let m := i.val-1
    let pos (j : Fin (m+2)) : Fin (d+2) := Fin.castLE (by dsimp [m]; omega) j
    let arcPos (j : Fin (m+1)) : Fin (d+1) := Fin.castLE (by dsimp [m]; omega) j
    have plainLeft (j : Fin (m+1)) : pos j.castSucc = (arcPos j).castSucc := Fin.ext rfl
    have plainRight (j : Fin (m+1)) : pos j.succ = (arcPos j).succ := Fin.ext rfl
    have prefixEnd : pos (Fin.last (m+1)) = i.castSucc := Fin.ext (by dsimp [pos,m]; omega)
    let pulled (j : Fin p) (u v : V) := Before paths j (project u) (project v)
    let prefixBridge : Bridge pulled m := by
      refine ⟨b.vertex ∘ pos,b.arc ∘ arcPos,b.river,
        b.distinctVertices.comp (Fin.castLE_injective _), b.distinctArcs.comp (Fin.castLE_injective _),
        fun j => b.river_ne_arc (arcPos j),?_,?_⟩
      · change Before paths b.river (project (b.vertex 0)) (project (b.vertex (pos (Fin.last (m+1)))))
        rw [prefixEnd,same]
        exact step b.riverStep
      · intro j
        change Before paths (b.arc (arcPos j)) (project (b.vertex (pos j.castSucc))) (project (b.vertex (pos j.succ)))
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
      (after := Before paths) (fun {_ _ _} found => found) (fun {_ _ _} found => listBefore_ne found) terminal
    have lastLabel : old.arc (Fin.last j) = b.arc (arcPos (Fin.last m)) := lastArc
    have riverLabel : old.river = b.river := river
    have noEarlier : ¬ b.arc (arcPos (Fin.last m)) < b.river := by
      intro order
      exact free (show j+2 ≤ k by dsimp [m] at bound; omega) old (by simpa only [lastLabel,riverLabel] using order)
    have riverFirst : b.river < b.arc (arcPos (Fin.last m)) :=
      lt_of_le_of_ne (le_of_not_gt noEarlier) (b.river_ne_arc _)
    have target : (arcPos (Fin.last m)).succ = i.castSucc := Fin.ext (by dsimp [arcPos,m]; omega)
    have onPrefix : b.vertex i.castSucc ∈ copies (b.arc (arcPos (Fin.last m))) := by
      rw [← target]
      exact (b.arcStep (arcPos (Fin.last m))).2.1
    have earlierBlock := splitListVertices_block_mono same.symm riverFirst.le
      ((sub b.river).subset b.riverStep.2.1) ((sub (b.arc (arcPos (Fin.last m)))).subset onPrefix)
    have distinctBlocks : (b.vertex last).snd.val ≠ (b.vertex i.castSucc).snd.val := by
      intro sameBlock
      have equal := b.distinctVertices (vertexBlock_eq_of_same_label same.symm sameBlock)
      have values := congrArg Fin.val equal
      change d+1 = i.val at values
      omega
    have backwards : (b.vertex last).snd.val < (b.vertex i.castSucc).snd.val :=
      earlierBlock.lt_of_ne distinctBlocks
    let t := d+1-i.val
    have tFit : t ≤ k-3 := by unfold t; omega
    let position (j : Fin (t+1)) : Fin (d+2) := ⟨i.val+j.val,by unfold t at j; omega⟩
    let v (j : Fin (t+1)) := b.vertex (position j)
    let rowIdx (j : Fin t) : Fin (d+1) := ⟨i.val+j.val,by unfold t at j; omega⟩
    let row (j : Fin t) := b.arc (rowIdx j)
    have start : position 0 = i.castSucc := Fin.ext (by simp [position])
    have finish : position (Fin.last t) = last := Fin.ext (by simp [position,t,last])
    have tailSteps (j : Fin t) : Before copies (row j) (v j.castSucc) (v j.succ) := by
      have left : position j.castSucc = (rowIdx j).castSucc := Fin.ext rfl
      have right : position j.succ = (rowIdx j).succ := Fin.ext (by simp [position,rowIdx,Nat.add_assoc])
      simpa only [v,row,left,right] using b.arcStep (rowIdx j)
    apply safe v row tFit tailSteps
    · simpa only [v,start,finish] using same
    · let block (x : V) := x.snd.val
      change block (b.vertex (position (Fin.last t))) < block (b.vertex (position 0))
      rw [start,finish]
      exact backwards
  · have noHits {i : Fin (d+1)} (equal : project (b.vertex i.castSucc) = project (b.vertex last)) : False :=
      nonempty ⟨i,mem_filter.mpr ⟨mem_univ _,equal⟩⟩
    obtain ⟨j,size,old,river,lastArc⟩ := b.project_vertices_preserving_last project
      (fun {_ _ _} => step) (fun {_ _ _} found => listBefore_ne found) (fun _ => noHits)
    exact free (show j+2 ≤ k by omega) old (by simpa only [river,lastArc] using earlier)

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

/-- Bounded reachability in the supplied rows certifies the
earlier-block return test. -/
theorem NoShortBackwardCopyReturnIn.of_reachIn {n p D cutoff : ℕ} {paths : Fin p → List (Fin n)}
    (rows : Fin p → List (ListVertexBlockIndex paths D))
    (noBack : ∀ {x y : ListVertexBlockIndex paths D}, x.fst = y.fst → y.snd.val < x.snd.val →
      x ∉ reachIn (listPiecePrecedenceGraph rows) y cutoff) :
    NoShortBackwardCopyReturnIn rows cutoff := by
  dsimp only [NoShortBackwardCopyReturnIn]
  intro d vertex row short steps same backwards
  let graph := listPiecePrecedenceGraph rows
  have found : vertex 0 ∈ reachIn graph (vertex (Fin.last d)) d :=
    reachIn_of_fin_steps vertex (fun j => listPiecePrecedenceGraph_edge.mpr ⟨row j,steps j⟩)
  have monotone : Monotone (reachIn graph (vertex (Fin.last d))) :=
    monotone_nat_of_le_succ (reachIn_subset_succ graph (vertex (Fin.last d)))
  exact noBack same backwards (monotone short found)

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

end OnlineReachabilityPreservers
