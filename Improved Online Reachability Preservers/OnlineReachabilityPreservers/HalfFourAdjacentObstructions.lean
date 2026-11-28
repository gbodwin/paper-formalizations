import OnlineReachabilityPreservers.HalfThreeLiteralCapacity

/-! Order obstructions among consecutive steps at half cutoff four. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn
local notation "Adjacent" => rowAdjacentComparisons

variable {I V : Type*} [LinearOrder I] [Fintype V] [DecidableEq V]
variable {rows : I → List V} {k : ℕ}

private theorem adjacent_conflicts_with_gap (free : HalfBridgeFree (Before rows) k) (two : 2 ≤ k)
    {i j : I} {u v : V} (edge : (u,v) ∈ Adjacent rows j) (on : Before rows i u v)
    (gap : (rows i).idxOf u+1 < (rows i).idxOf v) : False := by
  obtain ⟨step,adjacent⟩ := mem_rowAdjacentComparisons.mp edge
  by_cases same : i = j
  · subst j
    omega
  · exact no_parallel_list_steps free two same on step

/-- A three-step detour of adjacent comparisons forces the river to
precede its last row when one of the indicated back comparisons exists.
Consecutive repeats may be contracted while preserving the last row. -/
theorem halfFour_adjacent_detour_order (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k)
    {a b c r : I} {x y z t : V} (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V))
    (first : (x,y) ∈ Adjacent rows a) (second : (y,z) ∈ Adjacent rows b)
    (last : (z,t) ∈ Adjacent rows c) (shortcut : (x,t) ∈ Adjacent rows r)
    (back : ∃ i, (z,y) ∈ Adjacent rows i ∨ (t,y) ∈ Adjacent rows i) : r < c := by
  obtain ⟨firstStep,firstAdj⟩ := mem_rowAdjacentComparisons.mp first
  obtain ⟨secondStep,secondAdj⟩ := mem_rowAdjacentComparisons.mp second
  obtain ⟨lastStep,lastAdj⟩ := mem_rowAdjacentComparisons.mp last
  obtain ⟨riverStep,riverAdj⟩ := mem_rowAdjacentComparisons.mp shortcut
  have xz : x ≠ z := distinct.ne (by decide : (0 : Fin 4) ≠ 2)
  have yt : y ≠ t := distinct.ne (by decide : (1 : Fin 4) ≠ 3)
  have ra : r ≠ a := by
    rintro rfl
    exact yt ((List.idxOf_inj firstStep.2.1).mp (firstAdj.trans riverAdj.symm))
  have rc : r ≠ c := by
    rintro rfl
    exact xz ((List.idxOf_inj riverStep.1).mp (Nat.add_right_cancel (riverAdj.symm.trans lastAdj)))
  have rb : r ≠ b := by
    rintro rfl
    have xyIndex : (rows r).idxOf x ≠ (rows r).idxOf y :=
      fun eq => listBefore_ne firstStep ((List.idxOf_inj riverStep.1).mp eq)
    have ytIndex : (rows r).idxOf y ≠ (rows r).idxOf t :=
      fun eq => yt ((List.idxOf_inj secondStep.1).mp eq)
    have xzIndex : (rows r).idxOf x ≠ (rows r).idxOf z :=
      fun eq => xz ((List.idxOf_inj riverStep.1).mp eq)
    rcases lt_or_gt_of_ne xyIndex with forward | backward
    · exact adjacent_conflicts_with_gap free (by omega) first
        ⟨riverStep.1,secondStep.1,forward⟩ (by omega)
    · exact adjacent_conflicts_with_gap free (by omega) last
        ⟨secondStep.2.1,riverStep.2.1,by omega⟩ (by omega)
  have ac : a ≠ c := by
    rintro rfl
    have xzIndex : (rows a).idxOf x ≠ (rows a).idxOf z :=
      fun eq => xz ((List.idxOf_inj firstStep.1).mp eq)
    have xtIndex : (rows a).idxOf x ≠ (rows a).idxOf t :=
      fun eq => listBefore_ne riverStep ((List.idxOf_inj firstStep.1).mp eq)
    rcases lt_or_gt_of_ne xzIndex with forward | backward
    · exact adjacent_conflicts_with_gap free (by omega) shortcut
        ⟨firstStep.1,lastStep.2.1,by omega⟩ (by omega)
    · obtain ⟨i,backwardArc | crossArc⟩ := back
      · exact adjacent_conflicts_with_gap free (by omega) backwardArc
          ⟨lastStep.1,firstStep.2.1,by omega⟩ (by omega)
      · exact adjacent_conflicts_with_gap free (by omega) crossArc
          ⟨lastStep.2.1,firstStep.2.1,by omega⟩ (by omega)
  by_contra! wrong
  have earlier : c < r := lt_of_le_of_ne wrong rc.symm
  by_cases ab : a = b
  · subst b
    have merged : Before rows a x z := ⟨firstStep.1,secondStep.2.1,firstStep.2.2.trans secondStep.2.2⟩
    exact free (by omega : 1+2 ≤ k) (threeListBridge ac ra rc merged lastStep riverStep) earlier
  by_cases bc : b = c
  · subst b
    have merged : Before rows c y t := ⟨secondStep.1,lastStep.2.1,secondStep.2.2.trans lastStep.2.2⟩
    exact free (by omega : 1+2 ≤ k) (threeListBridge ac ra rc firstStep merged riverStep) earlier
  let bridge : Bridge (Before rows) 2 :=
    { vertex := ![x,y,z,t]
      arc := ![a,b,c]
      river := r
      distinctVertices := distinct
      distinctArcs := by
        intro i j equal
        fin_cases i <;> fin_cases j <;> simp_all
      river_ne_arc := by intro i; fin_cases i; exacts [ra,rb,rc]
      riverStep := riverStep
      arcStep := by intro i; fin_cases i; exacts [firstStep,secondStep,lastStep] }
  exact free four bridge earlier

variable [Fintype I]

omit [LinearOrder I] in
private theorem mem_family_adjacent {x y : V} :
    (x,y) ∈ univ.biUnion (Adjacent rows) ↔ ∃ i, (x,y) ∈ Adjacent rows i := by simp

/-- Two opposite three-step detours into one target give contradictory
arrival constraints. In particular a bidirected square cannot occur
among the consecutive comparisons. -/
theorem halfFour_no_adjacent_opposite_detours (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k)
    {x y z t : V} (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V))
    (xy : (x,y) ∈ univ.biUnion (Adjacent rows)) (yx : (y,x) ∈ univ.biUnion (Adjacent rows))
    (yz : (y,z) ∈ univ.biUnion (Adjacent rows)) (zy : (z,y) ∈ univ.biUnion (Adjacent rows))
    (xt : (x,t) ∈ univ.biUnion (Adjacent rows)) (zt : (z,t) ∈ univ.biUnion (Adjacent rows)) : False := by
  obtain ⟨a,xy⟩ := mem_family_adjacent.mp xy
  obtain ⟨b,yx⟩ := mem_family_adjacent.mp yx
  obtain ⟨c,yz⟩ := mem_family_adjacent.mp yz
  obtain ⟨d,zy⟩ := mem_family_adjacent.mp zy
  obtain ⟨r,xt⟩ := mem_family_adjacent.mp xt
  obtain ⟨s,zt⟩ := mem_family_adjacent.mp zt
  have rotated : Function.Injective (![z,y,x,t] : Fin 4 → V) := by
    have swaps : (![z,y,x,t] : Fin 4 → V) = ![x,y,z,t] ∘ Equiv.swap (0 : Fin 4) 2 := by
      funext i
      fin_cases i <;> rfl
    rw [swaps]
    exact distinct.comp (Equiv.swap _ _).injective
  exact (halfFour_adjacent_detour_order free four distinct xy yz zt xt ⟨d,Or.inl zy⟩).asymm
    (halfFour_adjacent_detour_order free four rotated zy yx xt zt ⟨a,Or.inl xy⟩)

/-- A cyclic orientation of four cross edges plus the two specified
diagonals is impossible for the adjacent comparisons. In particular two
disjoint reciprocal pairs cannot be joined by such a directed cycle. -/
theorem halfFour_no_adjacent_cycle_with_chords (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k)
    {x y z t : V} (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V))
    (xy : (x,y) ∈ univ.biUnion (Adjacent rows)) (yz : (y,z) ∈ univ.biUnion (Adjacent rows))
    (zt : (z,t) ∈ univ.biUnion (Adjacent rows)) (xt : (x,t) ∈ univ.biUnion (Adjacent rows))
    (ty : (t,y) ∈ univ.biUnion (Adjacent rows)) (zx : (z,x) ∈ univ.biUnion (Adjacent rows)) : False := by
  obtain ⟨_,xy⟩ := mem_family_adjacent.mp xy
  obtain ⟨_,yz⟩ := mem_family_adjacent.mp yz
  obtain ⟨_,zt⟩ := mem_family_adjacent.mp zt
  obtain ⟨_,ty⟩ := mem_family_adjacent.mp ty
  obtain ⟨_,xt⟩ := mem_family_adjacent.mp xt
  obtain ⟨_,zx⟩ := mem_family_adjacent.mp zx
  exact (halfFour_adjacent_detour_order free four distinct xy yz zt xt ⟨_,Or.inr ty⟩).asymm
    (halfThree_adjacent_triangle_order free (by omega) zx xt zt)

omit [Fintype V] [DecidableEq V] in
private theorem swap_last_vertices {x y z t : V}
    (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V)) :
    Function.Injective (![x,y,t,z] : Fin 4 → V) := by
  have swap : (![x,y,t,z] : Fin 4 → V) = ![x,y,z,t] ∘ Equiv.swap (2 : Fin 4) 3 := by
    funext i
    fin_cases i <;> rfl
  rw [swap]
  exact distinct.comp (Equiv.swap _ _).injective

omit [Fintype V] [DecidableEq V] in
private theorem swap_first_vertices {x y z t : V}
    (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V)) :
    Function.Injective (![y,x,z,t] : Fin 4 → V) := by
  have swap : (![y,x,z,t] : Fin 4 → V) = ![x,y,z,t] ∘ Equiv.swap (0 : Fin 4) 1 := by
    funext i
    fin_cases i <;> rfl
  rw [swap]
  exact distinct.comp (Equiv.swap _ _).injective

local notation "arcs" => (univ.biUnion (Adjacent rows))

private theorem halfThree_adjacent_no_common_out
    (free : HalfBridgeFree (Before rows) k) (three : 3 ≤ k) {x y z : V}
    (xy : (x,y) ∈ arcs) (yx : (y,x) ∈ arcs) (xz : (x,z) ∈ arcs) : (y,z) ∉ arcs := by
  intro yz
  obtain ⟨_,xy⟩ := mem_family_adjacent.mp xy
  obtain ⟨_,yx⟩ := mem_family_adjacent.mp yx
  obtain ⟨_,xz⟩ := mem_family_adjacent.mp xz
  obtain ⟨_,yz⟩ := mem_family_adjacent.mp yz
  exact (halfThree_adjacent_triangle_order free three xy yz xz).asymm
    (halfThree_adjacent_triangle_order free three yx xz yz)

private theorem halfFour_adjacent_no_full_cross_indegree (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k)
    {x y z t : V} (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V))
    (xy : (x,y) ∈ arcs) (yx : (y,x) ∈ arcs) (zt : (z,t) ∈ arcs) (tz : (t,z) ∈ arcs)
    (zx : (z,x) ∈ arcs) (toY : (z,y) ∈ arcs ∨ (t,y) ∈ arcs)
    (toZ : (x,z) ∈ arcs ∨ (y,z) ∈ arcs) (toT : (x,t) ∈ arcs ∨ (y,t) ∈ arcs) : False := by
  have apart {a b c : V} : (a,b) ∈ arcs → (b,a) ∈ arcs → (a,c) ∈ arcs → (b,c) ∉ arcs :=
    halfThree_adjacent_no_common_out free (by omega)
  by_cases xz : (x,z) ∈ arcs
  · have ty := toY.resolve_left (apart xz zx xy)
    have yt := toT.resolve_left (apart zx xz zt)
    exact halfFour_no_adjacent_opposite_detours free four (swap_last_vertices distinct)
      xy yx yt ty xz tz
  · have yz := toZ.resolve_left xz
    have zy : (z,y) ∉ arcs := fun zy => apart yz zy yx zx
    have ty := toY.resolve_left zy
    have yt : (y,t) ∉ arcs := fun yt => apart ty yt tz yz
    have xt := toT.resolve_right yt
    exact halfFour_no_adjacent_cycle_with_chords free four (swap_first_vertices (swap_last_vertices distinct))
      yx xt tz yz zx ty

omit [Fintype V] in
private def incomingFromPair (edges : Finset (V × V)) (x y z : V) : Finset (V × V) :=
  ({(x,z),(y,z)} : Finset (V × V)).filter (· ∈ edges)

omit [Fintype V] in
/-- The directed arcs between two pairs, grouped by their target. -/
def arcsBetweenPairs (edges : Finset (V × V)) (x y z t : V) : Finset (V × V) :=
  incomingFromPair edges z t x ∪ incomingFromPair edges z t y ∪
    incomingFromPair edges x y z ∪ incomingFromPair edges x y t

omit [Fintype V] in
theorem mem_arcsBetweenPairs {edges : Finset (V × V)} {x y z t u v : V} :
    (u,v) ∈ arcsBetweenPairs edges x y z t ↔ (u,v) ∈ edges ∧
      ((u = x ∨ u = y) ∧ (v = z ∨ v = t) ∨ (u = z ∨ u = t) ∧ (v = x ∨ v = y)) := by
  simp only [arcsBetweenPairs,incomingFromPair,mem_union,mem_filter,mem_insert,mem_singleton,Prod.mk.injEq]
  tauto

omit [Fintype V] in
private theorem incomingFromPair_nonempty {edges : Finset (V × V)} {x y z : V} :
    (incomingFromPair edges x y z).Nonempty → (x,z) ∈ edges ∨ (y,z) ∈ edges := by
  rintro ⟨edge,incoming⟩
  rcases mem_insert.mp (mem_filter.mp incoming).1 with rfl | last
  · exact Or.inl (mem_filter.mp incoming).2
  · have eq := mem_singleton.mp last
    exact Or.inr (eq ▸ (mem_filter.mp incoming).2)

/-- Two disjoint reciprocal pairs have at most three cross arcs among
the consecutive comparisons in a half-four-free system. Each target
takes at most one cross arc. Saturating all four targets forces one of
the two forbidden patterns. -/
theorem halfFour_adjacent_arcsBetweenPairs_le_three
    (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k) {x y z t : V}
    (distinct : Function.Injective (![x,y,z,t] : Fin 4 → V))
    (xy : (x,y) ∈ arcs) (yx : (y,x) ∈ arcs) (zt : (z,t) ∈ arcs) (tz : (t,z) ∈ arcs) :
    (arcsBetweenPairs arcs x y z t).card ≤ 3 := by
  have apart {a b c : V} : (a,b) ∈ arcs → (b,a) ∈ arcs → (a,c) ∈ arcs → (b,c) ∉ arcs :=
    halfThree_adjacent_no_common_out free (by omega)
  let A := incomingFromPair arcs z t x
  let B := incomingFromPair arcs z t y
  let C := incomingFromPair arcs x y z
  let D := incomingFromPair arcs x y t
  have oneA : A.card ≤ 1 := card_filter_pair_le_one_of_missing _ _ _ (apart zt tz)
  have oneB : B.card ≤ 1 := card_filter_pair_le_one_of_missing _ _ _ (apart zt tz)
  have oneC : C.card ≤ 1 := card_filter_pair_le_one_of_missing _ _ _ (apart xy yx)
  have oneD : D.card ≤ 1 := card_filter_pair_le_one_of_missing _ _ _ (apart xy yx)
  have total : (arcsBetweenPairs arcs x y z t).card ≤ A.card+B.card+C.card+D.card := by
    change (A ∪ B ∪ C ∪ D).card ≤ _
    have first := card_union_le A B
    have second := card_union_le (A ∪ B) C
    have third := card_union_le (A ∪ B ∪ C) D
    omega
  by_contra! high
  have toX := incomingFromPair_nonempty (card_pos.mp (show 0 < A.card by omega))
  have toY := incomingFromPair_nonempty (card_pos.mp (show 0 < B.card by omega))
  have toZ := incomingFromPair_nonempty (card_pos.mp (show 0 < C.card by omega))
  have toT := incomingFromPair_nonempty (card_pos.mp (show 0 < D.card by omega))
  rcases toX with zx | tx
  · exact halfFour_adjacent_no_full_cross_indegree free four distinct xy yx zt tz zx toY toZ toT
  · exact halfFour_adjacent_no_full_cross_indegree free four (swap_last_vertices distinct)
      xy yx tz zt tx toY.symm toT toZ

end OnlineReachabilityPreservers
