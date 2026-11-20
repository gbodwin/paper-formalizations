import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Consecutive local path cuts through half-bridge cutoff four. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I J : Type*} [DecidableEq V] [LinearOrder I] [LinearOrder J]

/-- Two distinct partners cannot reverse strictly nested intervals of a
path when the partner reversing the inner interval arrives later. -/
def NoLaterNestedOpposites (paths : I → List V) : Prop :=
  ∀ ⦃outer first inner : I⦄, outer ≠ first → outer ≠ inner → first < inner →
    ∀ ⦃u v w z : V⦄, ListBefore paths first u v → ListBefore paths first v w →
      ListBefore paths first w z → ListBefore paths outer z u →
      ListBefore paths inner w v → False

/-- Unique intersections rule out the nested reversal obstruction. -/
theorem noLaterNestedOpposites_of_unique {paths : I → List V}
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b →
      y ∈ paths a → y ∈ paths b → x = y) : NoLaterNestedOpposites paths := by
  intro a b c _ _ later u v w z uv vw wz zu wv
  exact listBefore_ne vw (unique later.ne vw.1 wv.2.1 vw.2.1 wv.1)

/-- The only possible repeated parent in a new four-corner half bridge
would give two strictly nested, reversed intervals. Ordered pieces avoid
the other repeat, which would give a parallel pair on distinct parent paths. -/
theorem HalfBridgeFree.split_ordered_list_paths {paths : I → List V} {pieces : J → List V}
    (free : HalfBridgeFree (ListBefore paths) 4) (noNested : NoLaterNestedOpposites paths)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → ListBefore paths (parent i) x y)) :
    HalfBridgeFree (ListBefore pieces) 4 := by
  intro k cutoff b earlier
  by_cases small : k ≤ 1
  · have oldShort : HalfBridgeFree (ListBefore paths) 3 := by
      intro s limit
      exact free (limit.trans (by decide))
    exact oldShort.split_list_paths_short le_rfl parent monotone steps disjoint (by omega) b earlier
  have eq : k = 2 := by omega
  subst k
  have step0 : ListBefore pieces (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
  have step1 : ListBefore pieces (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
  have step2 : ListBefore pieces (b.arc 2) (b.vertex 2) (b.vertex 3) := b.arcStep 2
  have river : ListBefore pieces b.river (b.vertex 0) (b.vertex 3) := b.riverStep
  have apart {i j : Fin 3} (ne : i ≠ j) : b.arc i ≠ b.arc j := fun h => ne (b.distinctArcs h)
  have adj01 : parent (b.arc 0) ≠ parent (b.arc 1) := fun h =>
    disjoint (apart (by decide)) h step0.2.1 step1.1
  have adj12 : parent (b.arc 1) ≠ parent (b.arc 2) := fun h =>
    disjoint (apart (by decide)) h step1.2.1 step2.1
  have adjR0 : parent b.river ≠ parent (b.arc 0) := fun h =>
    disjoint (b.river_ne_arc 0) h river.1 step0.1
  have adjR2 : parent b.river ≠ parent (b.arc 2) := fun h =>
    disjoint (b.river_ne_arc 2) h river.2.1 step2.2.1
  have earlierParent : parent (b.arc 2) < parent b.river :=
    (monotone earlier.le).lt_of_ne adjR2.symm
  have oppositeR1 : parent b.river ≠ parent (b.arc 1) := by
    intro eq
    rcases ordered (b.river_ne_arc 1) eq with before | after
    · exact no_parallel_list_steps free (by decide) adjR0 (before river.1 step1.1) (steps step0)
    · exact no_parallel_list_steps free (by decide) adjR2 (after step1.2.1 river.2.1) (steps step2)
  have opposite02 : parent (b.arc 0) ≠ parent (b.arc 2) := by
    intro eq
    rcases ordered (apart (by decide)) eq with before | after
    · exact no_parallel_list_steps free (by decide) adjR0.symm (before step0.1 step2.2.1) (steps river)
    · exact noNested adj01.symm oppositeR1.symm (eq ▸ earlierParent)
        (eq.symm ▸ steps step2) (after step2.2.1 step0.1) (steps step0) (steps step1) (steps river)
  have different : Function.Injective (parent ∘ b.arc) := by
    intro i j equal
    change parent (b.arc i) = parent (b.arc j) at equal
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact (adj01 equal).elim
      | exact (adj01 equal.symm).elim
      | exact (adj12 equal).elim
      | exact (adj12 equal.symm).elim
      | exact (opposite02 equal).elim
      | exact (opposite02 equal.symm).elim
  have riverApart : ∀ j, parent b.river ≠ (parent ∘ b.arc) j := by
    intro i
    fin_cases i
    · exact adjR0
    · exact oppositeR1
    · exact adjR2
  let old : Bridge (ListBefore paths) 2 :=
    ⟨b.vertex,parent ∘ b.arc,parent b.river,b.distinctVertices,different,riverApart,
      steps b.riverStep,fun i => steps (b.arcStep i)⟩
  exact free cutoff old earlierParent

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

omit [LinearOrder I] [Fintype I] in
private theorem listBlocks_ordered (paths : I → List V) (width : ℕ)
    {i j : ListBlockIndex paths width} (different : i ≠ j) (same : i.fst = j.fst) :
    (∀ ⦃x y⦄, x ∈ splitListPaths paths width i → y ∈ splitListPaths paths width j →
      ListBefore paths i.fst x y) ∨
    (∀ ⦃x y⦄, x ∈ splitListPaths paths width j → y ∈ splitListPaths paths width i →
      ListBefore paths i.fst x y) := by
  rcases i with ⟨a,ia⟩
  rcases j with ⟨b,jb⟩
  change a = b at same
  subst b
  have distinct : ia.val ≠ jb.val := fun eq => different (by cases Fin.ext eq; rfl)
  have before {x y : V} {i j : ℕ}
      (iLt : i < j) (xIn : x ∈ localPathBlock (paths a) width i)
      (yIn : y ∈ localPathBlock (paths a) width j) : ListBefore paths a x y := by
    obtain ⟨inX,atX⟩ := mem_localPathBlock.mp xIn
    obtain ⟨inY,atY⟩ := mem_localPathBlock.mp yIn
    refine ⟨inX,inY,lt_of_not_ge fun ge => ?_⟩
    have quotient := Nat.div_le_div_right (c := width) ge
    rw [atX,atY] at quotient
    exact (not_le_of_gt iLt) quotient
  rcases lt_or_gt_of_ne distinct with order | order
  · exact Or.inl (fun _ _ hx hy => before order hx hy)
  · exact Or.inr (fun _ _ hx hy => before order hx hy)

private theorem splitListVertices_project_step (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (width : ℕ) {i : I} {x y : ListVertexBlockIndex paths width}
    (before : ListBefore (splitListVertices paths width) i x y) : ListBefore paths i x.fst y.fst := by
  have nodup : ((splitListVertices paths width i).map (fun v => v.fst)).Nodup := by
    rw [splitListVertices_project]
    exact simple i
  simpa only [splitListVertices_project] using
    listBefore_map (fun v : ListVertexBlockIndex paths width => v.fst) nodup before

/-- The two standard splits preserve the half exclusion through four for
a family without the later nested reversal pattern. -/
theorem listRegularizedPaths_halfFree_of_no_later_nested {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup) (nonested : NoLaterNestedOpposites paths)
    (free : HalfBridgeFree (ListBefore paths) 4) (D L : ℕ) :
    HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) 4 := by
  let copies := splitListVertices paths D
  have project {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copies i x y) :
      ListBefore paths i x.fst y.fst := splitListVertices_project_step paths simple D step
  have copyFree : HalfBridgeFree (ListBefore copies) 4 :=
    free.split_list_vertices_short le_rfl (fun v => v.fst) (fun {_ _ _} step => project step)
  have copySimple (i : I) : (copies i).Nodup := by
    apply List.Nodup.of_map (fun v => v.fst)
    change ((splitListVertices paths D i).map (fun v => v.fst)).Nodup
    rw [splitListVertices_project]
    exact simple i
  have copyNesting : NoLaterNestedOpposites copies := by
    intro a b c apart distinct later x y z w xy yz zw outer inner
    exact nonested apart distinct later (project xy) (project yz) (project zw) (project outer) (project inner)
  change HalfBridgeFree (ListBefore (splitListPaths copies L)) 4
  apply copyFree.split_ordered_list_paths copyNesting (fun j : ListBlockIndex copies L => j.fst)
    (block_parent_mono (fun i => (copies i).toFinset) L)
  · intro i x y step
    exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := splitListPaths copies L) (copySimple i.fst)
      List.filter_sublist step
  · intro i j x different same left right
    rcases listBlocks_ordered copies L different same with before | after
    · exact listBefore_ne (before left right) rfl
    · exact listBefore_ne (after right left) rfl
  · intro i j different same
    exact listBlocks_ordered copies L different same

/-- The original factor-four caps and one-sixteenth retention hold through
half-bridge cutoff four under the no-later-nested-reversals condition. -/
theorem regularization_list_frozen_half_four_of_no_later_nested {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : HalfBridgeFree (ListBefore paths) 4) (noNested : NoLaterNestedOpposites paths)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  obtain ⟨dPos,dRoom,_⟩ := four_average_width hn dense
  obtain ⟨lPos,lRoom,_⟩ := four_average_width hp long
  obtain ⟨vRaw,iRaw⟩ := regularization_list_counts paths simple (D := D) (L := L) dPos lPos
  have vertices : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    change Fintype.card (ListVertexBlockIndex paths D) ≤ Fintype.card (Fin n) + M/D at vRaw
    simp only [Fintype.card_fin] at vRaw
    change 3*(M/D) ≤ n at dRoom
    calc
      _ ≤ 3*(n+M/D) := Nat.mul_le_mul_left _ vRaw
      _ = 3*n+3*(M/D) := Nat.mul_add _ _ _
      _ ≤ 4*n := by omega
  have families : 3*Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ 4*p := by
    change Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ Fintype.card (Fin p) + M/L at iRaw
    simp only [Fintype.card_fin] at iRaw
    change 3*(M/L) ≤ p at lRoom
    calc
      _ ≤ 3*(p+M/L) := Nat.mul_le_mul_left _ iRaw
      _ = 3*p+3*(M/L) := Nat.mul_add _ _ _
      _ ≤ 4*p := by omega
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  exact regularization_list_frozen_after_caps_with_room pieces
    (listRegularizedPaths_simple paths simple D L)
    (half := true) (k := 4) (listRegularizedPaths_halfFree_of_no_later_nested simple noNested allowed D L)
    hn hp dense long vertices families length degree mass

end OnlineReachabilityPreservers
