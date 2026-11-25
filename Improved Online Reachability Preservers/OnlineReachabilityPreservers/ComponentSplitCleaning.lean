import Mathlib.Data.Finset.Max
import OnlineReachabilityPreservers.CyclicSplits
import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.OfflineOrderedBlocks

/-! Cut paths between strongly connected precedence components. Distinct
rank intervals allow repeated parent paths in a projected bridge to be
shortened while keeping the river and the last arc's parent. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

private inductive IncreasingRoute {I : Type*} (step : I → ℕ → ℕ → Prop) :
    ℕ → ℕ → List I → List ℕ → Prop
  | nil (u : ℕ) : IncreasingRoute step u u [] [u]
  | cons {u v w : ℕ} {a : I} {labels : List I} {indices : List ℕ}
      (strict : u < v) (edge : step a u v) (tail : IncreasingRoute step v w labels indices) :
      IncreasingRoute step u w (a :: labels) (u :: indices)

namespace IncreasingRoute

private theorem corners_between {I : Type*} {step : I → ℕ → ℕ → Prop} {u w : ℕ}
    {labels : List I} {indices : List ℕ} (route : IncreasingRoute step u w labels indices) :
    u ≤ w ∧ ∀ j ∈ indices, u ≤ j ∧ j ≤ w := by
  induction route with
  | nil u => simp
  | @cons a b c owner ls xs strict edge remainder ih =>
    have finish := strict.le.trans ih.1
    refine ⟨finish, ?_⟩
    intro j on
    rcases List.mem_cons.mp on with rfl | later
    · exact ⟨le_rfl, finish⟩
    · exact ⟨strict.le.trans (ih.2 j later).1, (ih.2 j later).2⟩

private theorem distinct_indices {I : Type*} {step : I → ℕ → ℕ → Prop} {u w : ℕ}
    {labels : List I} {indices : List ℕ} (route : IncreasingRoute step u w labels indices) : indices.Nodup := by
  induction route with
  | nil u => simp
  | @cons a b c owner ls xs strict edge remainder ih =>
    exact List.nodup_cons.mpr ⟨fun earlier => (remainder.corners_between.2 a earlier).1.not_gt strict, ih⟩

private theorem coordinates {I : Type*} {step : I → ℕ → ℕ → Prop} {u w : ℕ}
    {labels : List I} {indices : List ℕ} (route : IncreasingRoute step u w labels indices) :
    ∃ v : Fin (labels.length + 1) → ℕ, List.ofFn v = indices ∧ v 0 = u ∧
      v (Fin.last labels.length) = w ∧ ∀ i, step (labels.get i) (v i.castSucc) (v i.succ) := by
  induction route with
  | nil u => exact ⟨fun _ => u, by simp, rfl, rfl, fun i => i.elim0⟩
  | @cons u v w a labels indices strict edge tail ih =>
    obtain ⟨x, shape, first, last, steps⟩ := ih
    let all : Fin ((a :: labels).length + 1) → ℕ := Fin.cases u x
    refine ⟨all, ?_, rfl, last, ?_⟩
    · rw [List.ofFn_succ]
      change u :: List.ofFn x = u :: indices
      rw [shape]
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · change step a u (x 0)
        rwa [first]
      · exact steps j

end IncreasingRoute

private theorem compressForwardRepeatedLabels {I : Type*} [DecidableEq I] {step : I → ℕ → ℕ → Prop}
    (label : ℕ → I) (n : ℕ) (shortcuts : ∀ i j, i ≤ j → j < n → label i = label j → step (label i) i (j + 1)) :
    ∀ start ≤ n, ∃ labels indices, IncreasingRoute step start n labels indices ∧ labels.Nodup ∧
      labels.length ≤ n - start ∧ (∀ a ∈ labels, ∃ i, start ≤ i ∧ i < n ∧ label i = a) ∧
      labels.getLast? = (if start < n then some (label (n - 1)) else none) := by
  have recur (fuel : ℕ) : ∀ start ≤ n, n - start ≤ fuel →
      ∃ labels indices, IncreasingRoute step start n labels indices ∧ labels.Nodup ∧
        labels.length ≤ n - start ∧ (∀ a ∈ labels, ∃ i, start ≤ i ∧ i < n ∧ label i = a) ∧
        labels.getLast? = (if start < n then some (label (n - 1)) else none) := by
    induction fuel with
    | zero =>
      intro start bound left
      have ends : start = n := by omega
      subst start
      exact ⟨[], [n], .nil n, by simp, by simp, by simp, by simp⟩
    | succ fuel ih =>
      intro start bound left
      by_cases done : start = n
      · subst start
        exact ⟨[], [n], .nil n, by simp, by simp, by simp, by simp⟩
      have before : start < n := bound.lt_of_ne done
      let carries := (Ico start n).filter (fun i => label i = label start)
      have startInside : start ∈ carries := mem_filter.mpr ⟨mem_Ico.mpr ⟨le_rfl, before⟩, rfl⟩
      let last := carries.max' ⟨start, startInside⟩
      have lastInside : last ∈ carries := max'_mem _ _
      have same := (mem_filter.mp lastInside).2
      obtain ⟨afterStart, lastBound⟩ := mem_Ico.mp (mem_filter.mp lastInside).1
      obtain ⟨ls, cs, route, distinct, length, used, final⟩ := ih (last + 1) (by omega) (by omega)
      have fresh : label start ∉ ls := by
        intro seen
        obtain ⟨i, afterLast, inside, sameLabel⟩ := used _ seen
        have accepted : i ∈ carries := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, inside⟩, sameLabel⟩
        exact (show i ≤ last from le_max' _ _ accepted).not_gt (by omega)
      refine ⟨label start :: ls, start :: cs, .cons (by omega) (shortcuts start last afterStart lastBound same.symm) route,
        List.nodup_cons.mpr ⟨fresh, distinct⟩, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro a on
        rcases List.mem_cons.mp on with rfl | other
        · exact ⟨start, le_rfl, before, rfl⟩
        · obtain ⟨i, afterLast, inside, equal⟩ := used a other
          exact ⟨i, by omega, inside, equal⟩
      · rw [List.getLast?_cons, final, ite_eq_left before]
        by_cases more : last + 1 < n
        · simp [more]
        · have lastIndex : n - 1 = last := by omega
          simp [more, lastIndex, same]
  exact fun start bound => recur (n - start) start bound le_rfl

private theorem bridge_from_forward_repetitions {I V : Type*} [DecidableEq I]
    (before : I → V → V → Prop) (v : ℕ → V) (label : ℕ → I) (river : I) (n : ℕ) (positive : 0 < n)
    (different : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (riverStep : before river (v 0) (v n)) (notRiver : ∀ i < n, river ≠ label i)
    (shortcuts : ∀ i j, i ≤ j → j < n → label i = label j → before (label i) (v i) (v (j + 1))) :
    ∃ k, k + 1 ≤ n ∧ ∃ b : Bridge before k, b.river = river ∧ b.arc (Fin.last k) = label (n - 1) := by
  obtain ⟨labels, indices, route, unique, count, used, final⟩ := compressForwardRepeatedLabels
    (step := fun a i j => before a (v i) (v j)) label n shortcuts 0 (Nat.zero_le n)
  have support := route.corners_between.2
  have indicesSimple := route.distinct_indices
  have separate (a : I) (ha : a ∈ labels) : river ≠ a := by
    obtain ⟨i, _, inside, same⟩ := used a ha
    exact same ▸ notRiver i inside
  obtain ⟨corner, shape, start, finish, edges⟩ := route.coordinates
  have distinct : Function.Injective corner := by
    rw [← shape, List.nodup_ofFn] at indicesSimple
    exact indicesSimple
  have indexCap (i : Fin (labels.length + 1)) : corner i ≤ n := by
    apply (support _ ?_).2
    rw [← shape]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have vInjective : Function.Injective (v ∘ corner) :=
    fun i j eq => distinct (different _ (indexCap _) _ (indexCap _) eq)
  cases labels with
  | nil =>
    have equal : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    have endpoint : 0 = n := start.symm.trans ((congrArg corner equal).trans finish)
    omega
  | cons a tail =>
    have finish' : corner (Fin.last (tail.length + 1)) = n := finish
    let out : Bridge before tail.length := ⟨v ∘ corner, (a :: tail).get, river, vInjective, List.nodup_iff_injective_get.mp unique,
      fun i => separate _ (List.get_mem (a :: tail) i), by simpa only [Function.comp_apply, start, finish'] using riverStep, edges⟩
    refine ⟨tail.length, by simpa using count, out, rfl, ?_⟩
    have nonempty : a :: tail ≠ [] := by simp
    rw [List.getLast?_eq_some_getLast nonempty, ite_eq_left positive, List.getLast_eq_getElem] at final
    exact Option.some.inj final

local notation "Before" => SourceAudit.BeforeIn

private noncomputable def precedenceRank {n p : ℕ} (paths : Fin p → List (Fin n)) (x : Fin n) : ℕ :=
  (reaches (condensation (pathPrecedenceGraph paths)) (componentLabel (pathPrecedenceGraph paths) x)).card

private theorem precedenceRank_order {n p : ℕ} {paths : Fin p → List (Fin n)} {i x y}
    (forward : Before paths i x y) (apart : ¬ SameComponent (pathPrecedenceGraph paths) x y) :
    precedenceRank paths x < precedenceRank paths y := by
  classical
  let G := pathPrecedenceGraph paths
  have edge : Edge G x y := by
    unfold G Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _, i, forward⟩
  have crossed : Edge (condensation G) (componentLabel G x) (componentLabel G y) :=
    edge_condensation.mpr ⟨fun e => apart (componentLabel_eq.mp e), x, y, edge, rfl, rfl⟩
  exact reaches_card_lt (condensation_dag G) crossed

private theorem precedenceRank_same {n p : ℕ} {paths : Fin p → List (Fin n)} {x y}
    (same : SameComponent (pathPrecedenceGraph paths) x y) :
    precedenceRank paths x = precedenceRank paths y := by
  unfold precedenceRank
  rw [componentLabel_eq.mpr same]

private theorem precedenceRank_mono {n p : ℕ} {paths : Fin p → List (Fin n)} {i x y}
    (forward : Before paths i x y) : precedenceRank paths x ≤ precedenceRank paths y := by
  by_cases same : SameComponent (pathPrecedenceGraph paths) x y
  · exact (precedenceRank_same same).le
  · exact (precedenceRank_order forward same).le

private theorem split_precedenceRank_order {n p : ℕ} {paths : Fin p → List (Fin n)} (D : ℕ)
    (i : Fin p) (simple : (paths i).Nodup) :
    (splitListVertices paths D i).Pairwise
      (fun x y => precedenceRank paths x.fst ≤ precedenceRank paths y.fst) := by
  let project (v : ListVertexBlockIndex paths D) : Fin n := v.fst
  have ordered : ((splitListVertices paths D i).map project).Pairwise
      (fun x y => precedenceRank paths x ≤ precedenceRank paths y) := by
    change ((splitListVertices paths D i).map (fun v => v.fst)).Pairwise _
    rw [splitListVertices_project]
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb ab
    have step : Before paths i (paths i)[a] (paths i)[b] :=
      ⟨List.getElem_mem ha, List.getElem_mem hb, by simpa only [simple.idxOf_getElem] using ab⟩
    exact precedenceRank_mono step
  exact (List.pairwise_map (f := project)
    (R := fun x y => precedenceRank paths x ≤ precedenceRank paths y)).mp ordered

private theorem bridge_of_rank_separated_split {V I J : Type*} [DecidableEq V] [DecidableEq I]
    {paths : I → List V} {pieces : J → List V} {k : ℕ}
    (parent : J → I) (rank : V → ℕ)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (monotone : ∀ {i x y}, Before paths i x y → rank x ≤ rank y)
    (separated : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank x < rank y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank y < rank x))
    (b : Bridge (Before pieces) k) :
    ∃ j ≤ k, ∃ old : Bridge (Before paths) j,
      old.river = parent b.river ∧ old.arc (Fin.last j) = parent (b.arc (Fin.last k)) := by
  let n := k + 1
  let v (i : ℕ) := b.vertex ⟨min i (k + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩
  let owner (i : ℕ) := if h : i < n then parent (b.arc ⟨i, h⟩) else parent b.river
  have fromFin (i : Fin (k + 2)) : v i.val = b.vertex i := by
    have bound : i.val ≤ k + 1 := Nat.le_of_lt_succ i.isLt
    exact congrArg b.vertex (Fin.ext (min_eq_left bound))
  have injective : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j := by
    intro i hi j hj equal
    have a : v i = b.vertex ⟨i, Nat.lt_succ_of_le hi⟩ := fromFin ⟨i, Nat.lt_succ_of_le hi⟩
    have c : v j = b.vertex ⟨j, Nat.lt_succ_of_le hj⟩ := fromFin ⟨j, Nat.lt_succ_of_le hj⟩
    exact congrArg Fin.val (b.distinctVertices (a.symm.trans (equal.trans c)))
  let arc (i : ℕ) (h : i < n) := b.arc ⟨i, h⟩
  have arcOwner (i : ℕ) (hi : i < n) : owner i = parent (arc i hi) := by simp [owner, arc, hi]
  have next (i : ℕ) (hi : i < n) : Before pieces (arc i hi) (v i) (v (i + 1)) := by
    let slot : Fin (k + 1) := ⟨i, hi⟩
    have first : v i = b.vertex slot.castSucc := fromFin slot.castSucc
    have last : v (i + 1) = b.vertex slot.succ := fromFin slot.succ
    rw [first, last]
    exact b.arcStep slot
  have river : Before pieces b.river (v 0) (v n) := by
    have first : v 0 = b.vertex 0 := fromFin (0 : Fin (k + 2))
    have last : v n = b.vertex (Fin.last (k + 1)) := fromFin (Fin.last (k + 1))
    rw [first, last]
    exact b.riverStep
  have along (i j : ℕ) (ij : i ≤ j) (jn : j ≤ n) : rank (v i) ≤ rank (v j) := by
    induction j, ij using Nat.le_induction with
    | base => exact le_rfl
    | succ j ij ih =>
      have hj : j < n := by omega
      exact (ih hj.le).trans (monotone (steps (next j hj)))
  have noRiver (i : ℕ) (hi : i < n) : parent b.river ≠ owner i := by
    rw [arcOwner i hi]
    intro same
    rcases separated (b.river_ne_arc ⟨i, hi⟩) same with left | right
    · exact (left _ river.2.1 _ (next i hi).1).not_ge (along i n hi.le le_rfl)
    · exact (right _ river.1 _ (next i hi).2.1).not_ge (along 0 (i + 1) (Nat.zero_le _) (by omega))
  have compressible (i j : ℕ) (ij : i ≤ j) (jn : j < n) (same : owner i = owner j) :
      Before paths (owner i) (v i) (v (j + 1)) := by
    by_cases eq : i = j
    · subst j
      rw [arcOwner _ jn]
      exact steps (next i jn)
    have inside : i < n := ij.trans_lt jn
    have sameParent : parent (arc i inside) = parent (arc j jn) := by
      simpa only [arcOwner i inside, arcOwner j jn] using same
    have distinct : arc i inside ≠ arc j jn := fun h => eq (congrArg Fin.val (b.distinctArcs h))
    have xOn : v i ∈ paths (parent (arc i inside)) := (steps (next i inside)).1
    have yOn : v (j + 1) ∈ paths (parent (arc i inside)) := sameParent.symm ▸ (steps (next j jn)).2.1
    have sep : rank (v i) ≠ rank (v (j + 1)) := by
      rcases separated distinct sameParent with forward | backward
      · exact (forward _ (next i inside).1 _ (next j jn).2.1).ne
      · exact (backward _ (next i inside).1 _ (next j jn).2.1).ne'
    have orderedRanks := (along i (j + 1) (by omega) (by omega)).lt_of_ne sep
    have apart : v i ≠ v (j + 1) := fun h => sep (congrArg rank h)
    rcases listBefore_total xOn yOn apart with order | backward
    · rwa [arcOwner _ inside]
    · exact (orderedRanks.not_ge (monotone backward)).elim
  obtain ⟨size', shorter, original, riverOwner, lastOwner⟩ := bridge_from_forward_repetitions (Before paths) v owner (parent b.river) n
    (by unfold n; omega) injective (steps river) noRiver compressible
  refine ⟨size', by unfold n at shorter; omega, original, riverOwner, lastOwner.trans ?_⟩
  have lastArc : n - 1 = k := by simp [n]
  rw [lastArc, arcOwner k (Nat.lt_succ_self k)]
  rfl

/-- A split with disjoint rank intervals on each parent preserves any full
bridge cutoff. Forward repetitions in the projected chain are shortened. -/
theorem bridgeFree_of_rank_separated_split {V I J : Type*} [DecidableEq V] [DecidableEq I]
    {paths : I → List V} {pieces : J → List V} {cutoff : ℕ} (free : BridgeFree (Before paths) cutoff)
    (parent : J → I) (rank : V → ℕ)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (monotone : ∀ {i x y}, Before paths i x y → rank x ≤ rank y)
    (separated : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank x < rank y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank y < rank x)) :
    BridgeFree (Before pieces) cutoff := by
  intro k size
  refine ⟨fun b => ?_⟩
  obtain ⟨j, smaller, old, _, _⟩ := bridge_of_rank_separated_split parent rank steps monotone separated b
  exact (free (k := j) (by omega)).false old

/-- A rank-separated split that preserves the order of different parent
paths also preserves half-bridge exclusion at any cutoff. -/
theorem halfBridgeFree_of_rank_separated_split {V I J : Type*} [DecidableEq V] [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List V} {cutoff : ℕ} (free : HalfBridgeFree (Before paths) cutoff)
    (parent : J → I) (arrival : Monotone parent) (rank : V → ℕ)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (monotone : ∀ {i x y}, Before paths i x y → rank x ≤ rank y)
    (separated : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank x < rank y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank y < rank x)) :
    HalfBridgeFree (Before pieces) cutoff := by
  intro k size b earlier
  obtain ⟨j, smaller, old, riverOwner, lastOwner⟩ := bridge_of_rank_separated_split parent rank steps monotone separated b
  have parentOrder := arrival earlier.le
  rw [← riverOwner, ← lastOwner] at parentOrder
  exact free (k := j) (by omega) old (parentOrder.lt_of_ne (old.river_ne_arc _).symm)

/-- Ordered pieces that keep the occurrences of each precedence component
together preserve full bridge exclusion at any cutoff. -/
theorem bridgeFree_of_component_respecting_split {n p cutoff : ℕ} {J : Type*}
    {paths : Fin p → List (Fin n)} {pieces : J → List (Fin n)}
    (free : BridgeFree (Before paths) cutoff) (parent : J → Fin p)
    (simple : ∀ i, (paths i).Nodup) (sub : ∀ i, (pieces i).Sublist (paths (parent i)))
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, Before paths (parent i) x y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, Before paths (parent i) y x))
    (components : ∀ {i j}, i ≠ j → parent i = parent j →
      ∀ x ∈ pieces i, ∀ y ∈ pieces j, ¬ SameComponent (pathPrecedenceGraph paths) x y) :
    BridgeFree (Before pieces) cutoff := by
  classical
  apply bridgeFree_of_rank_separated_split free parent (precedenceRank paths)
  · intro i x y h
    exact listBefore_of_sublist (paths := fun j => paths (parent j)) (cut := pieces)
      (simple _) (sub i) h
  · exact fun h => precedenceRank_mono h
  · intro i j apart same
    rcases ordered apart same with forward | reverse
    · left
      intro x hx y hy
      exact precedenceRank_order (forward x hx y hy) (components apart same x hx y hy)
    · right
      intro x hx y hy
      exact precedenceRank_order (reverse x hx y hy)
        (fun e => components apart same x hx y hy e.symm)

private def rankSeparatedRows {V : Type*} (rank : V → ℕ) (groups : List (List V)) : Prop :=
  groups.Pairwise (fun a b => ∀ x ∈ a, ∀ y ∈ b, rank x < rank y)

private theorem rankSeparatedRows_tail {V : Type*} {rank : V → ℕ} {a : List V} {groups : List (List V)}
    (sep : rankSeparatedRows rank (a :: groups)) : rankSeparatedRows rank groups := List.Pairwise.tail sep

private theorem exists_constant_rank_runs {V : Type*} (rank : V → ℕ) {row : List V}
    (ordered : row.Pairwise (fun x y => rank x ≤ rank y)) :
    ∃ groups : List (List V), groups.flatten = row ∧
      (∀ group ∈ groups, group ≠ [] ∧ ∃ r, ∀ x ∈ group, rank x = r) ∧ rankSeparatedRows rank groups := by
  induction row with
  | nil => exact ⟨[], rfl, by simp, by exact List.Pairwise.nil⟩
  | cons x row ih =>
    obtain ⟨above, tailOrdered⟩ := List.pairwise_cons.mp ordered
    obtain ⟨groups, flatten, ranges, separation⟩ := ih tailOrdered
    cases groups with
    | nil =>
      have empty : row = [] := flatten.symm
      subst row
      refine ⟨[[x]], rfl, ?_, ?_⟩
      · simp only [List.mem_singleton, forall_eq]
        exact ⟨by simp, rank x, by simp⟩
      · unfold rankSeparatedRows
        simp
    | cons first rest =>
      obtain ⟨someFirst, shared⟩ := ranges first List.mem_cons_self
      obtain ⟨r, same⟩ := shared
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ someFirst
      have rootY : rank y = r := same y hy
      have tailY : y ∈ row := by
        rw [← flatten]
        exact List.mem_flatten.mpr ⟨first, List.mem_cons_self, hy⟩
      have room : rank x ≤ r := by simpa only [rootY] using above y tailY
      have restSep := rankSeparatedRows_tail separation
      have firstBefore : ∀ group ∈ rest, ∀ u ∈ first, ∀ v ∈ group, rank u < rank v :=
        (List.pairwise_cons.mp (show (first :: rest).Pairwise _ from separation)).1
      have xBeforeRest (group : List V) (on : group ∈ rest) (z : V) (hz : z ∈ group) :
          rank x < rank z := (above y tailY).trans_lt (firstBefore group on y hy z hz)
      by_cases sameX : rank x = r
      · refine ⟨(x :: first) :: rest, ?_, ?_, ?_⟩
        · simpa only [List.flatten_cons, List.cons_append] using congrArg (List.cons x) flatten
        · intro group on
          rcases List.mem_cons.mp on with rfl | after
          · refine ⟨by simp, r, ?_⟩
            intro v hv
            rcases List.mem_cons.mp hv with rfl | old
            · exact sameX
            · exact same v old
          · exact ranges group (List.mem_cons_of_mem _ after)
        · unfold rankSeparatedRows
          refine List.pairwise_cons.mpr ⟨?_, restSep⟩
          intro group on u hu z hz
          rcases List.mem_cons.mp hu with rfl | onFirst
          · exact xBeforeRest group on z hz
          · exact firstBefore group on u onFirst z hz
      · refine ⟨[x] :: first :: rest, ?_, ?_, ?_⟩
        · simpa only [List.flatten_cons, List.singleton_append] using congrArg (List.cons x) flatten
        · intro group on
          rcases List.mem_cons.mp on with rfl | later
          · exact ⟨by simp, rank x, by simp⟩
          · exact ranges group later
        · unfold rankSeparatedRows
          refine List.pairwise_cons.mpr ⟨?_, separation⟩
          intro group on u hu z hz
          obtain rfl := List.mem_singleton.mp hu
          rcases List.mem_cons.mp on with rfl | later
          · rw [same z hz]
            exact room.lt_of_ne sameX
          · exact xBeforeRest group later z hz

private theorem pack_separated_runs {V : Type*} (rank : V → ℕ) (small width : ℕ) (fits : small ≤ width)
    {groups : List (List V)} (separated : rankSeparatedRows rank groups)
    (chunkCap : ∀ block ∈ groups, block.length ≤ small) :
    ∃ pieces : List (List V), pieces.flatten = groups.flatten ∧ rankSeparatedRows rank pieces ∧
      (∀ block ∈ pieces, block.length ≤ width) ∧
      (∀ block ∈ pieces.tail, width + 1 - small ≤ block.length) := by
  induction groups with
  | nil => exact ⟨[], rfl, List.Pairwise.nil, by simp, by simp⟩
  | cons head tail ih =>
    obtain ⟨origOrder, restSep⟩ := List.pairwise_cons.mp (show rankSeparatedRows rank (head :: tail) from separated)
    have headCap := chunkCap head List.mem_cons_self
    obtain ⟨packed, flat, order, cap, heavy⟩ := ih restSep (fun a h => chunkCap a (List.mem_cons_of_mem _ h))
    have headBefore (block : List V) (on : block ∈ packed) (x : V) (hx : x ∈ head) (y : V) (hy : y ∈ block) :
        rank x < rank y := by
      have appears : y ∈ tail.flatten := flat ▸ List.mem_flatten.mpr ⟨block, on, hy⟩
      obtain ⟨group, groupOn, member⟩ := List.mem_flatten.mp appears
      exact origOrder group groupOn x hx y member
    cases packed with
    | nil =>
      refine ⟨[head], ?_, by simp [rankSeparatedRows], ?_, by simp⟩
      · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [← flat]
        simp
      · simpa using headCap.trans fits
    | cons first rest =>
      have firstBefore := (List.pairwise_cons.mp (show rankSeparatedRows rank (first :: rest) from order)).1
      have tailSep := rankSeparatedRows_tail order
      by_cases room : head.length + first.length ≤ width
      · refine ⟨(head ++ first) :: rest, ?_, ?_, ?_, heavy⟩
        · simp only [List.flatten_cons, List.append_assoc]
          rw [← flat]
          rfl
        · unfold rankSeparatedRows
          refine List.pairwise_cons.mpr ⟨?_, tailSep⟩
          intro block on x hx y hy
          rcases List.mem_append.mp hx with inHead | inFirst
          · exact headBefore block (List.mem_cons_of_mem _ on) x inHead y hy
          · exact firstBefore block on x inFirst y hy
        · intro block on
          rcases List.mem_cons.mp on with rfl | later
          · simpa only [List.length_append] using room
          · exact cap block (List.mem_cons_of_mem _ later)
      · refine ⟨head :: first :: rest, ?_, ?_, ?_, ?_⟩
        · simp only [List.flatten_cons]
          exact congrArg (head++·) flat
        · unfold rankSeparatedRows
          exact List.pairwise_cons.mpr ⟨headBefore, order⟩
        · intro block on
          rcases List.mem_cons.mp on with rfl | later
          · exact headCap.trans fits
          · exact cap block later
        · intro block on
          rcases List.mem_cons.mp on with rfl | later
          · omega
          · exact heavy block later

private theorem packedCount {V : Type*} (minimum : ℕ) (pieces : List (List V))
    (heavy : ∀ block ∈ pieces.tail, minimum ≤ block.length) :
    minimum * pieces.length ≤ pieces.flatten.length + minimum := by
  cases pieces with
  | nil => simp
  | cons first rest =>
    have restCount : minimum * rest.length ≤ rest.flatten.length := by
      rw [List.length_flatten]
      simpa [Nat.mul_comm] using List.sum_le_sum (l := rest) (f := fun _ => minimum)
        (g := List.length) heavy
    simp only [List.length_cons, List.flatten_cons, List.length_append, Nat.mul_succ]
    omega

/-- The number of occurrences on a path in the precedence component of
a vertex. The precedence graph uses all strict comparisons along the paths. -/
noncomputable def precedenceComponentVisitLength {n p : ℕ} (paths : Fin p → List (Fin n))
    (i : Fin p) (x : Fin n) : ℕ :=
  ((paths i).filter (fun y =>
    decide (componentLabel (pathPrecedenceGraph paths) x = componentLabel (pathPrecedenceGraph paths) y))).length

private theorem small_component_rank_fibre {n p : ℕ} (paths : Fin p → List (Fin n))
    (limit : ℕ) (small : ∀ i x, precedenceComponentVisitLength paths i x ≤ limit)
    (i : Fin p) (r : ℕ) :
    ((paths i).filter (fun y => decide (precedenceRank paths y = r))).length ≤ limit := by
  classical
  let fibre := (paths i).filter (fun y => decide (precedenceRank paths y = r))
  change fibre.length ≤ limit
  by_cases empty : fibre = []
  · simp [empty]
  obtain ⟨x, on⟩ := List.exists_mem_of_ne_nil fibre empty
  have xOn := List.mem_filter.mp on
  have same {y} (hy : y ∈ paths i) (h : precedenceRank paths y = r) :
      SameComponent (pathPrecedenceGraph paths) x y := by
    by_contra apart
    have ranks : precedenceRank paths x = precedenceRank paths y := (of_decide_eq_true xOn.2).trans h.symm
    have different : x ≠ y := by
      intro e
      subst y
      exact apart (SameComponent.refl _ _)
    rcases listBefore_total xOn.1 hy different with forward | reverse
    · exact (precedenceRank_order forward apart).ne ranks
    · exact (precedenceRank_order reverse (fun a => apart a.symm)).ne' ranks
  let inComponent (y : Fin n) :=
    decide (componentLabel (pathPrecedenceGraph paths) x = componentLabel (pathPrecedenceGraph paths) y)
  have keeps : fibre.filter inComponent = fibre := by
    apply List.filter_eq_self.mpr
    intro y hy
    obtain ⟨onRow, onRank⟩ := List.mem_filter.mp hy
    exact decide_eq_true (componentLabel_eq.mpr (same onRow (of_decide_eq_true onRank)))
  have sub : fibre.Sublist (paths i) := List.filter_sublist
  have contained := sub.filter inComponent
  rw [keeps] at contained
  exact contained.length_le.trans (small i x)

private theorem packedWidthPieces {V : Type*} (rank : V → ℕ) (limit width : ℕ) (fits : limit ≤ width)
    (row : List V) (ordered : row.Pairwise (fun x y => rank x ≤ rank y))
    (small : ∀ r, (row.filter (fun y => decide (rank y = r))).length ≤ limit) :
    ∃ pieces : List (List V), pieces.flatten = row ∧ rankSeparatedRows rank pieces ∧
      (∀ block ∈ pieces, block.length ≤ width) ∧
      (width + 1 - limit) * pieces.length ≤ row.length + (width + 1 - limit) := by
  obtain ⟨runs, flat, constant, separated⟩ := exists_constant_rank_runs rank ordered
  have short (run : List V) (on : run ∈ runs) : run.length ≤ limit := by
    obtain ⟨_, r, rankEq⟩ := constant run on
    have sub : run.Sublist row := flat ▸ List.sublist_flatten_of_mem on
    let matchRank (x : V) := decide (rank x = r)
    have all : run.filter matchRank = run := List.filter_eq_self.mpr (fun x hx => decide_eq_true (rankEq x hx))
    have filtered := sub.filter matchRank
    rw [all] at filtered
    exact filtered.length_le.trans (small r)
  obtain ⟨pieces, flat', separation, cap, heavy⟩ := pack_separated_runs rank limit width fits separated short
  exact ⟨pieces, flat'.trans flat, separation, cap, by simpa only [flat', flat] using packedCount _ pieces heavy⟩

set_option maxHeartbeats 1000000 in
private theorem frozen_cleaning_of_small_precedence_components {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x
      ≤ (∑ i, (paths i).length)/p)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * (∑ i, (paths i).length)/n))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4 * M/n
  let L := 4 * M/p
  let smallSize := M/p
  let minimum := L + 1 - smallSize
  have fits : smallSize ≤ L := Nat.div_le_div_right (by omega)
  have minimumPositive : 0 < minimum := by unfold minimum; omega
  obtain ⟨dPos, dRoom, _⟩ := four_average_width hn dense
  have copied := (regularization_list_counts paths simple (D := D) dPos Nat.one_pos).1
  have vRoom : 3 * Fintype.card (ListVertexBlockIndex paths D) ≤ 4 * n := by
    change 3 * (M/D) ≤ n at dRoom
    rw [Fintype.card_fin] at copied
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n + M/D at copied
    omega
  let rows := splitListVertices paths D
  let rank (v : ListVertexBlockIndex paths D) := precedenceRank paths v.fst
  have order (i : Fin p) : (rows i).Pairwise (fun x y => rank x ≤ rank y) := by
    exact split_precedenceRank_order D i (simple i)
  have fibreCap (i : Fin p) (r : ℕ) : ((rows i).filter (fun v => decide (rank v = r))).length ≤ smallSize := by
    have filtered := congrArg (fun l : List (Fin n) =>
      (l.filter (fun v => decide (precedenceRank paths v = r))).length) (splitListVertices_project paths D i)
    rw [List.filter_map, List.length_map] at filtered
    exact filtered.trans_le (small_component_rank_fibre paths smallSize small i r)
  choose packed flatten separated cap count using fun i =>
    packedWidthPieces rank smallSize L fits (rows i) (order i) (fibreCap i)
  let P := Σₗ i : Fin p, Fin (packed i).length
  let pieces (i : P) := (packed i.1).get i.2
  have membership (i : P) : pieces i ∈ packed i.1 := List.get_mem _ _
  have sub (i : P) : (pieces i).Sublist (rows i.1) :=
    flatten i.1 ▸ List.sublist_flatten_of_mem (membership i)
  have apart {i j : P} (distinct : i ≠ j) (same : i.1 = j.1) :
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank x < rank y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank y < rank x) := by
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    change i = j at same
    subst j
    have different : a ≠ b := fun e => distinct (by cases e; rfl)
    have ordered := show (packed i).Pairwise _ from separated i
    rcases lt_or_gt_of_ne different with ab | ba
    · exact Or.inl (ordered.rel_get_of_lt ab)
    · right
      intro x hx y hy
      exact ordered.rel_get_of_lt ba y hy x hx
  have originalStep {i x y} (h : Before rows i x y) : Before paths i x.fst y.fst :=
    splitListVertices_step (simple i) h
  have pieceStep {i x y} (h : Before pieces i x y) : Before rows i.1 x y :=
    listBefore_of_sublist (paths := fun j : P => rows j.1) (cut := pieces)
      (splitListVertices_simple paths D i.1 (simple i.1)) (sub i) h
  have rankMono {i x y} (h : Before rows i x y) : rank x ≤ rank y :=
    precedenceRank_mono (originalStep h)
  have arrival : Monotone (fun i : P => i.1) := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with before | ⟨same, _⟩
    · exact before.le
    · exact same.le
  have packedLegal : localOrderAdmissible half k pieces := by
    cases half
    · exact bridgeFree_of_rank_separated_split legal (fun i : P => i.1) rank pieceStep rankMono apart
    · exact halfBridgeFree_of_rank_separated_split legal (fun i : P => i.1) arrival rank pieceStep rankMono apart
  have qRoom : 3 * Fintype.card P ≤ 4 * p := by
    have widthFloor : 4 * M < p * (L + 1) := Nat.lt_mul_div_succ (4 * M) hp
    have smallFloor : p * smallSize ≤ M := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self M p
    have enough : 3 * M ≤ p * minimum := by
      rw [show p * minimum = p * (L + 1) - p * smallSize by simp [minimum, Nat.mul_sub_left_distrib]]
      omega
    have total : minimum * (∑ i, (packed i).length) ≤ M + p * minimum := by
      rw [mul_sum]
      calc
        _ ≤ ∑ i, ((rows i).length + minimum) := Finset.sum_le_sum fun i _ => count i
        _ = _ := by simp [rows, M, sum_add_distrib]
    rw [Fintype.card_lex, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    apply Nat.le_of_mul_le_mul_left _ minimumPositive
    calc
      _ = 3 * (minimum * (∑ i, (packed i).length)) := by ring
      _ ≤ 3 * (M + p * minimum) := Nat.mul_le_mul_left _ total
      _ ≤ _ := by rw [show minimum * (4 * p) = 4 * (p * minimum) by ring]; omega
  have copiedDegree (v : ListVertexBlockIndex paths D) :
      (occurrences (fun i => (rows i).toFinset) v).card ≤ D := by
    simpa only [rows, splitListVertices_toFinset] using
      (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
  have degree (v : ListVertexBlockIndex paths D) : (occurrences (fun i => (pieces i).toFinset) v).card ≤ D := by
    refine le_trans ?_ (copiedDegree v)
    apply card_le_card_of_injOn (fun i : P => i.1)
    · intro i hi
      have contains := (mem_occurrences (marks := fun j => (pieces j).toFinset)).mp hi
      apply mem_occurrences.mpr
      exact List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp contains))
    · intro i hi j hj same
      by_contra different
      have inI := List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (pieces j).toFinset)).mp hi)
      have inJ := List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (pieces j).toFinset)).mp hj)
      rcases apart different same with forward | reverse
      · exact (forward v inI v inJ).false
      · exact (reverse v inI v inJ).false
  have total : (∑ i, (pieces i).length) = M := by
    change (∑ i : Sigma (fun j => Fin (packed j).length), ((packed i.1).get i.2).length) = M
    rw [Fintype.sum_sigma]
    unfold M
    apply sum_congr rfl
    intro i _
    rw [← splitListVertices_length paths D i, show splitListVertices paths D i = (packed i).flatten from (flatten i).symm,
      List.length_flatten]
    rw [← List.sum_ofFn]
    have lengthRows := congrArg (List.map List.length) (List.ofFn_get (packed i))
    rw [List.map_ofFn] at lengthRows
    exact congrArg List.sum lengthRows
  exact regularization_list_frozen_after_caps_with_room (half := half) pieces
    (fun i => (sub i).nodup (splitListVertices_simple paths D i.1 (simple i.1)))
    packedLegal hn hp dense long vRoom qRoom (fun i => cap i.1 _ (membership i)) degree total

/-- Full-bridge cleaning at the original fixed averages for a possibly cyclic
family, when no path spends more than one original mean path length inside
a single precedence strongly connected component. -/
theorem regularization_list_frozen_of_small_precedence_components {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x
      ≤ (∑ i, (paths i).length)/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have legal := free.split_list_vertices_any (copies := splitListVertices paths (4 * (∑ i, (paths i).length)/n))
    (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  exact frozen_cleaning_of_small_precedence_components (half := false) paths simple hn hp dense long small legal

/-- The component-based construction can preserve exclusion at every size
when the input excludes every full bridge. -/
theorem regularization_list_frozen_allFull_of_small_precedence_components {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : ∀ j, IsEmpty (Bridge (Before paths) j)) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x
      ≤ (∑ i, (paths i).length)/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ j, IsEmpty (Bridge (Before clean) j)) ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n', fitsV, p', fitsP, clean, simple', cutoff, retained, cap, caps⟩ :=
    regularization_list_frozen_of_small_precedence_components (k := p + 1)
      paths simple (fun _ _ => free _) hn hp dense long small
  refine ⟨n', fitsV, p', fitsP, clean, simple', ?_, retained, cap, caps⟩
  intro j
  refine ⟨fun b => ?_⟩
  have arcCount := Fintype.card_le_of_injective _ b.distinctArcs
  simp only [Fintype.card_fin] at arcCount
  exact (cutoff (k := j) (by omega)).false b

private theorem split_list_vertices_half_of_degree_cap {n p k D : ℕ}
    {paths : Fin p → List (Fin n)} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (cap : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    HalfBridgeFree (Before (splitListVertices paths D)) k := by
  let marks (i : Fin p) := (paths i).toFinset
  let rows := splitListVertices paths D
  have sameBlock {i x} (on : x ∈ rows i) : x.2.val = 0 := by
    have belongs := List.mem_toFinset.mpr on
    change x ∈ (splitListVertices paths D i).toFinset at belongs
    rw [splitListVertices_toFinset] at belongs
    change x ∈ splitVertices marks D i at belongs
    obtain ⟨vertex, _, rfl⟩ := mem_map.mp belongs
    change (predecessors (occurrences marks vertex.val) i).card / D = 0
    have original : i ∈ occurrences marks vertex.val := mem_occurrences.mpr vertex.property
    have before : predecessors (occurrences marks vertex.val) i ⊂ occurrences marks vertex.val := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
      intro eq
      have onEarlier : i ∈ predecessors (occurrences marks vertex.val) i := by rwa [eq]
      exact (lt_irrefl i) (mem_filter.mp onEarlier).2
    exact Nat.div_eq_of_lt ((card_lt_card before).trans_le (cap _))
  have equalCopy {x y : ListVertexBlockIndex paths D} (same : x.1 = y.1)
      (xBlock : x.2.val = 0) (yBlock : y.2.val = 0) : x = y := by
    rcases x with ⟨v, a⟩
    rcases y with ⟨w, b⟩
    change v = w at same
    subst w
    obtain rfl := Fin.ext (xBlock.trans yBlock.symm)
    rfl
  intro j size b earlier
  have onBlock (i : Fin (j + 2)) : (b.vertex i).2.val = 0 := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
    · exact sameBlock b.riverStep.1
    · exact sameBlock (b.arcStep a).2.1
  let old : Bridge (Before paths) j :=
    ⟨fun i => (b.vertex i).fst, b.arc, b.river,
      fun i j eq => b.distinctVertices (equalCopy eq (onBlock i) (onBlock j)),
      b.distinctArcs, b.river_ne_arc, splitListVertices_step (simple _) b.riverStep,
      fun i => splitListVertices_step (simple _) (b.arcStep i)⟩
  exact free size old earlier

/-- The same component-based cuts preserve half exclusion. For the degree
split it suffices that the input excludes full bridges through two less
than the half cutoff, that the half cutoff is at most four, or that all
input degrees already fit the upper cap. -/
theorem regularization_list_frozen_half_of_small_precedence_components {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (degreeSafe : k ≤ 4 ∨ BridgeFree (Before paths) (k - 2) ∨
      ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4 * (∑ i, (paths i).length)/n)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x
      ≤ (∑ i, (paths i).length)/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply frozen_cleaning_of_small_precedence_components (half := true) paths simple hn hp dense long small
  rcases degreeSafe with short | full | capped
  · exact free.split_list_vertices_short short (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  · exact free.split_list_vertices_of_full full (by omega) (·.fst)
      (fun {i _ _} => splitListVertices_step (simple i))
  · exact split_list_vertices_half_of_degree_cap simple free capped

end OnlineReachabilityPreservers
