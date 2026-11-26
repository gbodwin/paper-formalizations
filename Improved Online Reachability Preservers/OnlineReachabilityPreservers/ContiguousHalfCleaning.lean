import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.LocalFrozenLowMass
import OnlineReachabilityPreservers.OppositeLinkForest

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

/-- A nested reversal survives the cuts if the four required steps each survive
in one piece and the two steps on the central path use different pieces.
The names `early` and `late` refer to their order in the central path. -/
def CutRetainsNestedOppositesAt (paths : I → List V) (pieces : J → List V)
    (parent : J → I) (inner : J) (w : V) : Prop :=
  ∃ (early late outer : J) (u v z : V),
    early ≠ late ∧ parent early = parent late ∧
    parent outer ≠ parent early ∧ parent outer ≠ parent inner ∧ parent early < parent inner ∧
    ListBefore paths (parent early) v w ∧
    ListBefore pieces early u v ∧ ListBefore pieces late w z ∧
    ListBefore pieces outer z u ∧ ListBefore pieces inner w v

/-- Some starting incidence lies on an inner step of a retained nested reversal. -/
def CutRetainsNestedOpposites (paths : I → List V) (pieces : J → List V) (parent : J → I) : Prop :=
  ∃ (inner : J) (w : V), CutRetainsNestedOppositesAt paths pieces parent inner w

/-- Any retained nested reversal produces an actual half-4-bridge. -/
theorem CutRetainsNestedOpposites.not_half_free {paths : I → List V} {pieces : J → List V}
    {parent : J → I} (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (pattern : CutRetainsNestedOpposites paths pieces parent) :
    ¬ HalfBridgeFree (ListBefore pieces) 4 := by
  rintro free
  obtain ⟨inner,w,early,late,outer,u,v,z,earlyLate,parents,outerEarly,outerInner,earlyInner,
    vw,uv,wz,zu,wv⟩ := pattern
  have oldUV := steps uv
  have oldWZ : ListBefore paths (parent early) w z := parents.symm ▸ steps wz
  have uw := lt_trans oldUV.2.2 vw.2.2
  have vz := lt_trans vw.2.2 oldWZ.2.2
  have uz := lt_trans oldUV.2.2 vz
  have uV : u ≠ v := listBefore_ne oldUV
  have vW : v ≠ w := listBefore_ne vw
  have wZ : w ≠ z := listBefore_ne oldWZ
  have uW : u ≠ w := fun eq => (lt_irrefl _ (eq ▸ uw))
  have vZ : v ≠ z := fun eq => (lt_irrefl _ (eq ▸ vz))
  have uZ : u ≠ z := fun eq => (lt_irrefl _ (eq ▸ uz))
  have innerEarly : inner ≠ early := fun eq => earlyInner.ne (congrArg parent eq).symm
  have innerLate : inner ≠ late := fun eq => earlyInner.ne (parents.trans (congrArg parent eq).symm)
  have outerNeEarly : outer ≠ early := fun eq => outerEarly (congrArg parent eq)
  have outerNeLate : outer ≠ late := fun eq => outerEarly ((congrArg parent eq).trans parents.symm)
  have innerNeOuter : inner ≠ outer := fun eq => outerInner (congrArg parent eq).symm
  let corners : Fin 4 → V := ![w,z,u,v]
  let arcs : Fin 3 → J := ![late,outer,early]
  have differentCorners : Function.Injective corners := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp [corners] at eq ⊢ <;> exfalso <;>
      first | exact uV eq | exact vW eq | exact wZ eq | exact uW eq | exact vZ eq | exact uZ eq
            | exact uV eq.symm | exact vW eq.symm | exact wZ eq.symm | exact uW eq.symm
            | exact vZ eq.symm | exact uZ eq.symm
  have differentArcs : Function.Injective arcs := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp [arcs] at eq ⊢ <;> exfalso <;>
      first | exact earlyLate eq | exact outerNeEarly eq | exact outerNeLate eq
            | exact earlyLate eq.symm | exact outerNeEarly eq.symm | exact outerNeLate eq.symm
  have riverApart (i : Fin 3) : inner ≠ arcs i := by
    fin_cases i
    · exact innerLate
    · exact innerNeOuter
    · exact innerEarly
  have chain (i : Fin 3) : ListBefore pieces (arcs i) (corners i.castSucc) (corners i.succ) := by
    fin_cases i
    · exact wz
    · exact zu
    · exact uv
  let bridge : Bridge (ListBefore pieces) 2 := ⟨corners,arcs,inner,differentCorners,differentArcs,
    riverApart,wv,chain⟩
  have order : early < inner := by
    by_contra! wrong
    exact earlyInner.not_ge (monotone wrong)
  exact free (by decide) bridge order

/-- For ordered pieces of a half-4-free family the surviving nested reversal
is the exact obstruction to remaining half-4-free. -/
theorem HalfBridgeFree.split_ordered_iff_no_retained_nested {paths : I → List V} {pieces : J → List V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → ListBefore paths (parent i) x y)) :
    HalfBridgeFree (ListBefore pieces) 4 ↔ ¬ CutRetainsNestedOpposites paths pieces parent := by
  refine ⟨fun child pattern => pattern.not_half_free monotone steps child,?_⟩
  intro noNested k cutoff b earlier
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
    · exact noNested ⟨b.river,_,b.arc 2,b.arc 0,b.arc 1,_,_,_,
        apart (by decide),eq.symm,adj12,oppositeR1.symm,earlierParent,
        eq ▸ after step2.2.1 step0.1,step2,step0,step1,river⟩
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

/-- No nested reversal in the input is sufficient for any collection of
ordered disjoint pieces to preserve half-bridge exclusion through four. -/
theorem HalfBridgeFree.split_ordered_list_paths {paths : I → List V} {pieces : J → List V}
    (free : HalfBridgeFree (ListBefore paths) 4) (noNested : NoLaterNestedOpposites paths)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → ListBefore paths (parent i) x y)) :
    HalfBridgeFree (ListBefore pieces) 4 := by
  apply (free.split_ordered_iff_no_retained_nested parent monotone steps disjoint ordered).mpr
  intro pattern
  obtain ⟨inner,w,early,late,outer,u,v,z,_,parents,outerEarly,outerInner,earlyInner,
    vw,uv,wz,zu,wv⟩ := pattern
  exact noNested outerEarly outerInner earlyInner (steps uv) vw (parents.symm ▸ steps wz)
    (steps zu) (steps wv)

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

/-- A half-four-free simple family with few opposite links can be cleaned
at the original averages, with both original budgets. -/
theorem regularization_list_frozen_half_four_of_few_opposite_links {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 18*Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet ≤
      ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  let K := ∑ i, (kept i).length
  let D := 4*M/n
  let L := 4*M/p
  have two : HalfBridgeFree (ListBefore paths) 2 := fun _ h => free (h.trans (by decide))
  let E := Nat.card (oppositeLinkGraphOfHalfTwo paths two).edgeSet
  have retained : M ≤ K+E := removeOppositeIntersections_mass_with_half_two_link_count two simple
  have enough : 8*(32+2)*M ≤ 9*32*K := by
    change 18*E ≤ M at few
    omega
  have massCap : K ≤ M := sum_le_sum fun i _ => (removeOppositeIntersections_sublist paths i).length_le
  have keptSimple (i : Fin p) : (kept i).Nodup := (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have keptFree : HalfBridgeFree (ListBefore kept) 4 := removeOppositeIntersections_halfFree simple free
  have legal : localOrderAdmissible true 4 (listRegularizedPaths kept D L) := listRegularizedPaths_halfFree keptSimple
    (fun {_ _ _ _} ab xa xb ya yb =>
      removeOppositeIntersections_unique simple free (by decide) ab xa xb ya yb) keptFree D L
  exact regularization_list_frozen_after_width_blocks_of_mass kept keptSimple legal
    hn hp dense long massCap enough

/-- At half cutoff four it suffices that the original mass is at least
eight times the number of opposite links. -/
theorem regularization_list_frozen_half_four_of_eight_links {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 8*Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet ≤
      ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  let K := ∑ i, (kept i).length
  have two : HalfBridgeFree (ListBefore paths) 2 := fun _ h => free (h.trans (by decide))
  let E := Nat.card (oppositeLinkGraphOfHalfTwo paths two).edgeSet
  have loss : M ≤ K+E := removeOppositeIntersections_mass_with_half_two_link_count two simple
  have enough : 7*M ≤ 8*K := by
    change 8*E ≤ M at few
    omega
  have upper : K ≤ M := sum_le_sum fun i _ => (removeOppositeIntersections_sublist paths i).length_le
  have keptSimple (i : Fin p) : (kept i).Nodup := (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have keptFree : HalfBridgeFree (ListBefore kept) 4 := removeOppositeIntersections_halfFree simple free
  have allowed : localOrderAdmissible true 4 (listRegularizedPaths kept (4*M/n) (4*M/p)) :=
    listRegularizedPaths_halfFree keptSimple
      (fun {_ _ _ _} ab xa xb ya yb =>
        removeOppositeIntersections_unique simple free (by decide) ab xa xb ya yb) keptFree _ _
  exact regularization_list_frozen_of_seven_eighths_mass paths kept simple keptSimple free (by decide)
    hn hp dense long upper (fun _ => enough) allowed

/-- A numeric density condition supplies the opposite-link budget for
half-four cleaning with all four original-average caps. -/
theorem regularization_list_frozen_half_four_of_incidence_square {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (square : 16*n^2*(n-1) ≤ (∑ i, (paths i).length)^2) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let E := Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet
  have edges : 4*E^2 ≤ n^2*(n-1) := by
    simpa only [Fintype.card_fin,E] using halfFour_oppositeLinkGraph_card_edgeSet_sq free
  have sufficient : (8*E)^2 ≤ M^2 := calc
    _ = 16*(4*E^2) := by ring
    _ ≤ 16*(n^2*(n-1)) := Nat.mul_le_mul_left 16 edges
    _ = 16*n^2*(n-1) := by ring
    _ ≤ _ := square
  exact regularization_list_frozen_half_four_of_eight_links paths simple free hn hp dense long
    ((Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp sufficient)

/-- The original-average cleaning conclusion holds at the unrestricted
half-four maximum when the path budget supplies the numeric density. -/
theorem localOrderExtremal_frozen_half_four_of_large_path_budget (n p : ℕ)
    (hn : 0 < n) (hp : 0 < p) (square : 16*n^2*(n-1) ≤ p^2) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ HalfBridgeFree (ListBefore paths) 4 ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → HalfBridgeFree (ListBefore other) 4 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
        (∑ i, (paths i).length) ≤ 32*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧
        frozenListCaps n p (∑ i, (paths i).length) clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p 4 true hn hp
  exact ⟨paths,simple,free,maximal,regularization_list_frozen_half_four_of_incidence_square
    paths simple free hn hp dense long (square.trans (Nat.pow_le_pow_left long 2))⟩

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I J : Type*} [LinearOrder V] [LinearOrder I] [LinearOrder J]

/-- The starting incidence on the inner piece of each nested reversal
that survives the given cuts. Several witnesses can share one incidence. -/
def activeNestedOppositeStarts (paths : I → List V) (pieces : J → List V) (parent : J → I) : Set (J × V) :=
  {a | CutRetainsNestedOppositesAt paths pieces parent a.1 a.2}

/-- Remove the marked starts while keeping the original pieces and their order. -/
noncomputable def removeActiveNestedOppositeStarts (paths : I → List V) (pieces : J → List V)
    (parent : J → I) (i : J) : List V := by
  classical
  exact (pieces i).filter fun w => decide ((i,w) ∉ activeNestedOppositeStarts paths pieces parent)

omit [LinearOrder J] in
theorem removeActiveNestedOppositeStarts_sublist (paths : I → List V) (pieces : J → List V)
    (parent : J → I) (i : J) : (removeActiveNestedOppositeStarts paths pieces parent i).Sublist (pieces i) :=
  List.filter_sublist

omit [LinearOrder J] in
theorem removeActiveNestedOppositeStarts_mem {paths : I → List V} {pieces : J → List V}
    {parent : J → I} {i : J} {w : V} :
    w ∈ removeActiveNestedOppositeStarts paths pieces parent i ↔
      w ∈ pieces i ∧ (i,w) ∉ activeNestedOppositeStarts paths pieces parent := by
  simp [removeActiveNestedOppositeStarts]

/-- Deleting exactly those starting incidences repairs the half-four
exclusion for any ordered disjoint split of a half-four-free input. -/
theorem removeActiveNestedOppositeStarts_halfFree {paths : I → List V} {pieces : J → List V}
    (free : HalfBridgeFree (ListBefore paths) 4) (simple : ∀ i, (pieces i).Nodup)
    (parent : J → I) (monotone : Monotone parent)
    (steps : ∀ {i x y}, ListBefore pieces i x y → ListBefore paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → ListBefore paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → ListBefore paths (parent i) x y)) :
    HalfBridgeFree (ListBefore (removeActiveNestedOppositeStarts paths pieces parent)) 4 := by
  let repaired := removeActiveNestedOppositeStarts paths pieces parent
  have contained {i : J} {w : V} (mem : w ∈ repaired i) : w ∈ pieces i :=
    (removeActiveNestedOppositeStarts_mem.mp mem).1
  have lift {i : J} {x y : V} (step : ListBefore repaired i x y) : ListBefore pieces i x y :=
    listBefore_of_sublist (simple i) (removeActiveNestedOppositeStarts_sublist paths pieces parent i) step
  apply (free.split_ordered_iff_no_retained_nested parent monotone
    (fun h => steps (lift h)) (fun ne eq left right => disjoint ne eq (contained left) (contained right)) ?_).mpr
  · rintro ⟨inner,w,early,late,outer,u,v,z,neq,same,outerEarly,outerInner,earlier,vw,uv,wz,zu,wv⟩
    exact (removeActiveNestedOppositeStarts_mem.mp wv.1).2
      ⟨early,late,outer,u,v,z,neq,same,outerEarly,outerInner,earlier,vw,lift uv,lift wz,lift zu,lift wv⟩
  · intro i j different same
    rcases ordered different same with before | after
    · left
      intro x y left right
      exact before (contained left) (contained right)
    · right
      intro x y left right
      exact after (contained left) (contained right)

omit [LinearOrder J] in
/-- The number of removed incidences is exactly the number of marked starts. -/
theorem removeActiveNestedOppositeStarts_mass [Fintype V] [Fintype J]
    (paths : I → List V) (pieces : J → List V) (parent : J → I) (simple : ∀ i, (pieces i).Nodup) :
    (∑ i, (removeActiveNestedOppositeStarts paths pieces parent i).length) +
      Nat.card (activeNestedOppositeStarts paths pieces parent) = ∑ i, (pieces i).length := by
  classical
  let active := activeNestedOppositeStarts paths pieces parent
  let kept := removeActiveNestedOppositeStarts paths pieces parent
  let erased := (univ : Finset (J × V)).filter fun a => a ∈ active
  have asSet : (erased : Set (J × V)) = active := by ext a; simp [erased]
  have inside (i : J) (w : V) (mark : (i,w) ∈ active) : w ∈ pieces i := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wv⟩ := mark
    exact wv.1
  have erasedSize : erased.card = ∑ i, ((pieces i).toFinset \ (kept i).toFinset).card := by
    unfold erased
    rw [card_filter,← univ_product_univ,Finset.sum_product]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    congr 1
    ext w
    simp only [mem_filter,mem_univ,true_and,mem_sdiff,List.mem_toFinset,kept,removeActiveNestedOppositeStarts_mem]
    exact ⟨fun mark => ⟨inside i w mark,fun kept => kept.2 mark⟩,
      fun absent => Classical.byContradiction (fun notMarked => absent.2 ⟨absent.1,notMarked⟩)⟩
  have activeSize : Nat.card active = erased.card := by
    rw [← asSet]
    change Nat.card (↥erased) = erased.card
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  change (∑ i, (kept i).length)+Nat.card active = ∑ i, (pieces i).length
  rw [activeSize,erasedSize,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  let sub := removeActiveNestedOppositeStarts_sublist paths pieces parent i
  have subset : (kept i).toFinset ⊆ (pieces i).toFinset := fun _ mem =>
    List.mem_toFinset.mpr (sub.subset (List.mem_toFinset.mp mem))
  rw [← List.toFinset_card_of_nodup (sub.nodup (simple i)),← List.toFinset_card_of_nodup (simple i),Nat.add_comm]
  exact card_sdiff_add_card_eq_card subset

variable {n p : ℕ}

/-- The loss count for the actual degree and path width blocks. -/
def widthCutActiveNestedStarts (paths : Fin p → List (Fin n)) (D L : ℕ) :
    Set (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) :=
  activeNestedOppositeStarts (splitListVertices paths D) (listRegularizedPaths paths D L) Sigma.fst

/-- Remove the marked river starts for the actual degree and path width blocks. -/
noncomputable def repairWidthCutNestedStarts (paths : Fin p → List (Fin n)) (D L : ℕ) :=
  removeActiveNestedOppositeStarts (splitListVertices paths D) (listRegularizedPaths paths D L) Sigma.fst

/-- Each marked start costs exactly one incidence, and the remaining
subsequences exclude half-bridges through size four. -/
theorem repairWidthCutNestedStarts_spec (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4)
    (D L : ℕ) :
    let pieces := listRegularizedPaths paths D L
    let kept := repairWidthCutNestedStarts paths D L
    (∀ i, List.Sublist (kept i) (pieces i)) ∧ HalfBridgeFree (ListBefore kept) 4 ∧
      (∑ i, (kept i).length)+Nat.card (widthCutActiveNestedStarts paths D L) = ∑ i, (pieces i).length := by
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  let parent : ListBlockIndex copies L → Fin p := Sigma.fst
  let kept := repairWidthCutNestedStarts paths D L
  have copyFree : HalfBridgeFree (ListBefore copies) 4 :=
    free.split_list_vertices_short le_rfl (fun v => v.fst) (fun step => splitListVertices_project_step paths simple D step)
  have copySimple (i : Fin p) : (copies i).Nodup := by
    apply List.Nodup.of_map (fun v => v.fst)
    rw [splitListVertices_project]
    exact simple i
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  have sub (i : ListBlockIndex copies L) := removeActiveNestedOppositeStarts_sublist copies pieces parent i
  have valid : HalfBridgeFree (ListBefore kept) 4 := by
    apply removeActiveNestedOppositeStarts_halfFree copyFree pieceSimple parent
      (block_parent_mono (fun i => (copies i).toFinset) L)
    · intro i x y step
      exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
        (cut := splitListPaths copies L) (copySimple i.fst) List.filter_sublist step
    · intro i j x different same left right
      rcases listBlocks_ordered copies L different same with before | after
      · exact listBefore_ne (before left right) rfl
      · exact listBefore_ne (after right left) rfl
    · intro i j different same
      exact listBlocks_ordered copies L different same
  exact ⟨sub,valid,removeActiveNestedOppositeStarts_mass copies pieces parent pieceSimple⟩

/-- Repairing just the nested reversals that survive the original-width
blocks gives both budgets and all four frozen caps if at most one twelfth
of the original incidences are marked. -/
theorem regularization_list_frozen_half_four_of_few_active_nested_starts (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : let M := ∑ i, (paths i).length
      12*Nat.card (widthCutActiveNestedStarts paths (4*M/n) (4*M/p)) ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 64*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  let kept := repairWidthCutNestedStarts paths D L
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  obtain ⟨sub,valid,total⟩ := repairWidthCutNestedStarts_spec paths simple free D L
  obtain ⟨dPos,dRoom,_⟩ := four_average_width hn dense
  obtain ⟨lPos,lRoom,_⟩ := four_average_width hp long
  obtain ⟨rawV,rawP⟩ := regularization_list_counts paths simple (D := D) (L := L) dPos lPos
  have vertices : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    change 3*(M/D) ≤ n at dRoom
    simp only [Fintype.card_fin] at rawV
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n+M/D at rawV
    omega
  have rows : 3*Fintype.card (ListBlockIndex copies L) ≤ 4*p := by
    change 3*(M/L) ≤ p at lRoom
    simp only [Fintype.card_fin] at rawP
    change Fintype.card (ListBlockIndex copies L) ≤ p+M/L at rawP
    omega
  obtain ⟨pieceMass,length,degree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  change (∑ i, (pieces i).length) = M at pieceMass
  change (∑ i, (kept i).length)+Nat.card (widthCutActiveNestedStarts paths D L) = (∑ i, (pieces i).length) at total
  rw [pieceMass] at total
  change 12*Nat.card (widthCutActiveNestedStarts paths D L) ≤ M at few
  have cap (x : ListVertexBlockIndex paths D) : (occurrences (fun i => (kept i).toFinset) x).card ≤ D := by
    apply le_trans (card_le_card (t := occurrences (fun i => (pieces i).toFinset) x) ?_) (degree x)
    intro i mem
    have inside : x ∈ (kept i).toFinset := (mem_occurrences (marks := fun j => (kept j).toFinset)).mp mem
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp inside)))
  exact regularization_list_frozen_after_caps_with_room_of_mass kept (fun i => (sub i).nodup (pieceSimple i))
    (half := true) (k := 4) (retention := 64) valid hn hp dense long vertices rows
    (fun i => (sub i).length_le.trans (length i)) cap (by omega) (by omega)

end OnlineReachabilityPreservers
