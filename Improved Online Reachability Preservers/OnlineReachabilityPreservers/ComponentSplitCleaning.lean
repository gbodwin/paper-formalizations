import Mathlib.Data.List.Chain
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
      (∀ block ∈ pieces.tail, width + 1 - small ≤ block.length) ∧
      pieces.IsChain (fun a b => width + 1 ≤ a.length + b.length) := by
  induction groups with
  | nil => exact ⟨[], rfl, List.Pairwise.nil, by simp, by simp, .nil⟩
  | cons head tail ih =>
    obtain ⟨origOrder, restSep⟩ := List.pairwise_cons.mp (show rankSeparatedRows rank (head :: tail) from separated)
    have headCap := chunkCap head List.mem_cons_self
    obtain ⟨packed, flat, order, cap, heavy, pairs⟩ := ih restSep (fun a h => chunkCap a (List.mem_cons_of_mem _ h))
    have headBefore (block : List V) (on : block ∈ packed) (x : V) (hx : x ∈ head) (y : V) (hy : y ∈ block) :
        rank x < rank y := by
      have appears : y ∈ tail.flatten := flat ▸ List.mem_flatten.mpr ⟨block, on, hy⟩
      obtain ⟨group, groupOn, member⟩ := List.mem_flatten.mp appears
      exact origOrder group groupOn x hx y member
    cases packed with
    | nil =>
      refine ⟨[head], ?_, by simp [rankSeparatedRows], ?_, by simp, .singleton _⟩
      · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [← flat]
        simp
      · simpa using headCap.trans fits
    | cons first rest =>
      have firstBefore := (List.pairwise_cons.mp (show rankSeparatedRows rank (first :: rest) from order)).1
      have tailSep := rankSeparatedRows_tail order
      by_cases room : head.length + first.length ≤ width
      · refine ⟨(head ++ first) :: rest, ?_, ?_, ?_, heavy, ?_⟩
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
        · cases rest with
          | nil => exact .singleton _
          | cons second rest =>
            obtain ⟨large, later⟩ := List.isChain_cons_cons.mp pairs
            exact List.isChain_cons_cons.mpr ⟨by simp only [List.length_append]; omega, later⟩
      · refine ⟨head :: first :: rest, ?_, ?_, ?_, ?_, List.isChain_cons_cons.mpr ⟨by omega, pairs⟩⟩
        · simp only [List.flatten_cons]
          exact congrArg (head ++ ·) flat
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

private theorem packedPairCount {V : Type*} (width : ℕ) (pieces : List (List V))
    (pairs : pieces.IsChain (fun a b => width + 1 ≤ a.length + b.length)) :
    (width + 1) * pieces.length ≤ 2 * pieces.flatten.length + (width + 1) := by
  induction pieces using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b rest ih _ =>
    have large := (List.isChain_cons_cons.mp pairs).1
    have smaller := ih pairs.tail.tail
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
      (width + 1 - limit) * pieces.length ≤ row.length + (width + 1 - limit) ∧
      (width + 1) * pieces.length ≤ 2 * row.length + (width + 1) := by
  obtain ⟨runs, flat, constant, separated⟩ := exists_constant_rank_runs rank ordered
  have short (run : List V) (on : run ∈ runs) : run.length ≤ limit := by
    obtain ⟨_, r, rankEq⟩ := constant run on
    have sub : run.Sublist row := flat ▸ List.sublist_flatten_of_mem on
    let matchRank (x : V) := decide (rank x = r)
    have all : run.filter matchRank = run := List.filter_eq_self.mpr (fun x hx => decide_eq_true (rankEq x hx))
    have filtered := sub.filter matchRank
    rw [all] at filtered
    exact filtered.length_le.trans (small r)
  obtain ⟨pieces, flat', separation, cap, heavy, pairs⟩ := pack_separated_runs rank limit width fits separated short
  exact ⟨pieces, flat'.trans flat, separation, cap,
    by simpa only [flat', flat] using packedCount _ pieces heavy,
    by simpa only [flat', flat] using packedPairCount width pieces pairs⟩

set_option maxHeartbeats 1000000 in
private theorem frozen_cleaning_of_component_visits {n p k M retention vNum vDen pNum pDen : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (mass : (∑ i, (paths i).length) ≤ M) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (limit : ℕ) (fits : limit ≤ 4 * M / p)
    (small : ∀ i x, precedenceComponentVisitLength paths i x ≤ limit)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * M / n)))
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertexBudget : vNum * (n + M / (4 * M / n)) ≤ vDen * n)
    (pathBudget : ∀ q,
      let L := 4 * M / p
      let minimum := L + 1 - limit
      minimum * q ≤ M + p * minimum → (L + 1) * q ≤ 2 * M + p * (L + 1) → pNum * q ≤ pDen * p)
    (retained : (vDen * pDen) * (retention + 2) * M ≤
      2 * (vNum * pNum) * retention * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let D := 4 * M / n
  let L := 4 * M / p
  let minimum := L + 1 - limit
  obtain ⟨dPos, _, _⟩ := four_average_width hn dense
  have copied := (regularization_list_counts paths simple (D := D) dPos Nat.one_pos).1
  rw [Fintype.card_fin] at copied
  have copiedBound : Fintype.card (ListVertexBlockIndex paths D) ≤ n + M / D :=
    copied.trans (Nat.add_le_add_left (Nat.div_le_div_right mass) n)
  have vRoom : vNum * Fintype.card (ListVertexBlockIndex paths D) ≤ vDen * n :=
    (Nat.mul_le_mul_left vNum copiedBound).trans vertexBudget
  let rows := splitListVertices paths D
  let rank (v : ListVertexBlockIndex paths D) := precedenceRank paths v.fst
  have order (i : Fin p) : (rows i).Pairwise (fun x y => rank x ≤ rank y) := by
    exact split_precedenceRank_order D i (simple i)
  have fibreCap (i : Fin p) (r : ℕ) : ((rows i).filter (fun v => decide (rank v = r))).length ≤ limit := by
    have filtered := congrArg (fun l : List (Fin n) =>
      (l.filter (fun v => decide (precedenceRank paths v = r))).length) (splitListVertices_project paths D i)
    rw [List.filter_map, List.length_map] at filtered
    exact filtered.trans_le (small_component_rank_fibre paths limit small i r)
  choose packed flatten separated cap count pairs using fun i =>
    packedWidthPieces rank limit L fits (rows i) (order i) (fibreCap i)
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
  have qRoom : pNum * Fintype.card P ≤ pDen * p := by
    rw [Fintype.card_lex, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have rowMass : (∑ i, (rows i).length) ≤ M := by simpa only [rows, splitListVertices_length] using mass
    apply pathBudget
    · change minimum * (∑ i, (packed i).length) ≤ M + p * minimum
      rw [mul_sum]
      calc
        _ ≤ ∑ i, ((rows i).length + minimum) := Finset.sum_le_sum fun i _ => count i
        _ = (∑ i, (rows i).length) + p * minimum := by simp [sum_add_distrib]
        _ ≤ _ := Nat.add_le_add_right rowMass _
    · rw [mul_sum]
      calc
        _ ≤ ∑ i, (2 * (rows i).length + (L + 1)) := Finset.sum_le_sum fun i _ => pairs i
        _ = 2 * (∑ i, (rows i).length) + p * (L + 1) := by simp [sum_add_distrib, mul_sum]
        _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 2 rowMass) _
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
  have total : (∑ i, (pieces i).length) = ∑ i, (paths i).length := by
    change (∑ i : Sigma (fun j => Fin (packed j).length), ((packed i.1).get i.2).length) = _
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    rw [← splitListVertices_length paths D i, show splitListVertices paths D i = (packed i).flatten from (flatten i).symm,
      List.length_flatten]
    rw [← List.sum_ofFn]
    have lengthRows := congrArg (List.map List.length) (List.ofFn_get (packed i))
    rw [List.map_ofFn] at lengthRows
    exact congrArg List.sum lengthRows
  exact regularization_list_frozen_after_caps_with_ratios_of_mass (half := half) pieces
    (fun i => (sub i).nodup (splitListVertices_simple paths D i.1 (simple i.1)))
    packedLegal hn hp dense long vPos pPos vRatio pRatio vRoom qRoom
    (fun i => cap i.1 _ (membership i)) degree (total.trans_le mass) (by rw [total]; exact retained)

private theorem frozen_cleaning_of_small_precedence_components {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x ≤ (∑ i, (paths i).length) / p)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * (∑ i, (paths i).length) / n))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4 * M / n
  let L := 4 * M / p
  let limit := M / p
  let minimum := L + 1 - limit
  have fits : limit ≤ L := Nat.div_le_div_right (by omega)
  have minimumPositive : 0 < minimum := by unfold minimum; omega
  obtain ⟨_, vertexRoom, _⟩ := four_average_width hn dense
  have vertexBudget : 3 * (n + M / D) ≤ 4 * n := by
    change 3 * (M / D) ≤ n at vertexRoom
    omega
  have widthFloor : 4 * M < p * (L + 1) := Nat.lt_mul_div_succ (4 * M) hp
  have smallFloor : p * limit ≤ M := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self M p
  have enough : 3 * M ≤ p * minimum := by
    rw [show p * minimum = p * (L + 1) - p * limit by simp [minimum, Nat.mul_sub_left_distrib]]
    omega
  refine frozen_cleaning_of_component_visits (half := half) paths simple le_rfl hn hp dense long limit fits small legal
    (vNum := 3) (vDen := 4) (pNum := 3) (pDen := 4)
    (by decide) (by decide) (by decide) (by decide) vertexBudget ?_ (by omega)
  dsimp only
  intro q total _
  change minimum * q ≤ M + p * minimum at total
  apply Nat.le_of_mul_le_mul_left _ minimumPositive
  calc
    _ = 3 * (minimum * q) := by ring
    _ ≤ 3 * (M + p * minimum) := Nat.mul_le_mul_left _ total
    _ ≤ _ := by rw [show minimum * (4 * p) = 4 * (p * minimum) by ring]; omega

private theorem frozen_cleaning_of_width_precedence_components_of_mass {n p k M retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (mass : (∑ i, (paths i).length) ≤ M)
    (visits : ∀ i x, precedenceComponentVisitLength paths i x ≤ 4 * M / p)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * M / n)))
    (sparseRetention : 6 ≤ retention)
    (enough : 27 * (retention + 2) * M ≤ 28 * retention * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4 * M / n
  let L := 4 * M / p
  by_cases substantial : 2 * n ≤ M
  · obtain ⟨dPos, _, _⟩ := four_average_width hn dense
    have dFloor : 4 * M < n * (D + 1) := Nat.lt_mul_div_succ (4 * M) hn
    rw [Nat.mul_succ] at dFloor
    have reserve : 7 * M ≤ 2 * (n * D) := by omega
    have trim : 7 * (M / D) ≤ 2 * n := by
      apply Nat.le_of_mul_le_mul_right _ dPos
      calc
        _ = 7 * ((M / D) * D) := by ring
        _ ≤ 7 * M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
        _ ≤ _ := reserve.trans_eq (by ring)
    have vertexBudget : 7 * (n + M / D) ≤ 9 * n := by omega
    refine frozen_cleaning_of_component_visits (half := half) paths simple mass hn hp dense long L le_rfl visits legal
      (vNum := 7) (vDen := 9) (pNum := 2) (pDen := 3)
      (by decide) (by decide) (by decide) (by decide) vertexBudget ?_ enough
    dsimp only
    intro q _ pairs
    change (L + 1) * q ≤ 2 * M + p * (L + 1) at pairs
    have lFloor : 4 * M < p * (L + 1) := Nat.lt_mul_div_succ (4 * M) hp
    have positive : 0 < L + 1 := Nat.succ_pos L
    apply Nat.le_of_mul_le_mul_left _ positive
    calc
      _ = 2 * ((L + 1) * q) := by ring
      _ ≤ 2 * (2 * M + p * (L + 1)) := Nat.mul_le_mul_left _ pairs
      _ ≤ 3 * (p * (L + 1)) := by omega
      _ = _ := by ring
  · have light : M ≤ 3 * max n p := by have top := le_max_left n p; omega
    obtain ⟨n', fitsV, p', fitsP, clean, simple', free, keep, cap, caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long light
    have allowed : localOrderAdmissible half k clean := by
      cases half
      · exact free
      · exact free.halfFree
    exact ⟨n', fitsV, p', fitsP, clean, simple', allowed,
      keep.trans (Nat.mul_le_mul_right _ sparseRetention), cap, caps⟩

private theorem frozen_cleaning_of_width_precedence_components {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (visits : ∀ i x, precedenceComponentVisitLength paths i x ≤ 4 * (∑ i, (paths i).length) / p)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * (∑ i, (paths i).length) / n))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 54 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_width_precedence_components_of_mass paths simple hn hp dense long le_rfl visits legal
    (by decide) (by norm_num)

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

/-- If no component visit exceeds the full original upper length cap,
full-bridge cleaning at any cutoff retains one fifty-fourth of the mass. -/
theorem regularization_list_frozen_of_precedence_visits_within_cap {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (visits : ∀ i x, precedenceComponentVisitLength paths i x ≤ 4 * (∑ i, (paths i).length) / p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 54 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have legal := free.split_list_vertices_any (copies := splitListVertices paths (4 * (∑ i, (paths i).length) / n))
    (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  exact frozen_cleaning_of_width_precedence_components (half := false) paths simple hn hp dense long visits legal

private theorem bridgeFree_all_of_path_budget {V : Type*} {p' p : ℕ} {before : Fin p' → V → V → Prop}
    (fits : p' ≤ p) (cutoff : BridgeFree before (p + 1)) :
    ∀ j, IsEmpty (Bridge before j) := by
  intro j
  refine ⟨fun b => ?_⟩
  have arcCount := Fintype.card_le_of_injective _ b.distinctArcs
  simp only [Fintype.card_fin] at arcCount
  exact (cutoff (k := j) (by omega)).false b

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
  exact ⟨n', fitsV, p', fitsP, clean, simple', bridgeFree_all_of_path_budget fitsP cutoff, retained, cap, caps⟩

/-- Capping the length of each component visit at the full original upper
cap also works for full exclusion at every size. -/
theorem regularization_list_frozen_allFull_of_precedence_visits_within_cap {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : ∀ j, IsEmpty (Bridge (Before paths) j)) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (visits : ∀ i x, precedenceComponentVisitLength paths i x ≤ 4 * (∑ i, (paths i).length) / p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ j, IsEmpty (Bridge (Before clean) j)) ∧
      M ≤ 54 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n', fitsV, p', fitsP, clean, simple', cutoff, retained, cap, caps⟩ :=
    regularization_list_frozen_of_precedence_visits_within_cap (k := p + 1)
      paths simple (fun _ _ => free _) hn hp dense long visits
  exact ⟨n', fitsV, p', fitsP, clean, simple', bridgeFree_all_of_path_budget fitsP cutoff, retained, cap, caps⟩

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

private theorem split_list_vertices_half_of_degree_condition {n p k D : ℕ}
    {paths : Fin p → List (Fin n)} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (degreeSafe : k ≤ 4 ∨ BridgeFree (Before paths) (k - 2) ∨
      ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    HalfBridgeFree (Before (splitListVertices paths D)) k := by
  rcases degreeSafe with short | full | capped
  · exact free.split_list_vertices_short short (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  · exact free.split_list_vertices_of_full full (by omega) (·.fst)
      (fun {i _ _} => splitListVertices_step (simple i))
  · exact split_list_vertices_half_of_degree_cap simple free capped

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
  exact frozen_cleaning_of_small_precedence_components (half := true) paths simple hn hp dense long small
    (split_list_vertices_half_of_degree_condition simple free degreeSafe)

/-- For half exclusion, a safe degree split and component visits within
the upper length cap suffice to retain one fifty-fourth of the mass. -/
theorem regularization_list_frozen_half_of_precedence_visits_within_cap {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (degreeSafe : k ≤ 4 ∨ BridgeFree (Before paths) (k - 2) ∨
      ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4 * (∑ i, (paths i).length) / n)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (visits : ∀ i x, precedenceComponentVisitLength paths i x ≤ 4 * (∑ i, (paths i).length) / p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 54 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  exact frozen_cleaning_of_width_precedence_components (half := true) paths simple hn hp dense long visits
    (split_list_vertices_half_of_degree_condition simple free degreeSafe)

/-- Delete entire precedence component visits longer than the supplied cap.
The test uses the components of the original family. -/
noncomputable def pruneLongPrecedenceVisits {n p : ℕ} (paths : Fin p → List (Fin n))
    (limit : ℕ) (i : Fin p) : List (Fin n) :=
  (paths i).filter (fun x => decide (precedenceComponentVisitLength paths i x ≤ limit))

private theorem before_pruneLongPrecedenceVisits {n p limit : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) {i : Fin p} {x y : Fin n}
    (step : Before (pruneLongPrecedenceVisits paths limit) i x y) : Before paths i x y :=
  listBefore_of_sublist (simple i) List.filter_sublist step

private theorem pruneLongPrecedenceVisits_simple {n p limit : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (i : Fin p) : (pruneLongPrecedenceVisits paths limit i).Nodup :=
  (simple i).filter _

/-- Removing these visits preserves the two bridge modes and caps every
visit in the resulting precedence graph. -/
theorem pruneLongPrecedenceVisits_spec {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (limit : ℕ) :
    let kept := pruneLongPrecedenceVisits paths limit
    localOrderAdmissible half k kept ∧ (∑ i, (kept i).length) ≤ ∑ i, (paths i).length ∧
      ∀ i x, precedenceComponentVisitLength kept i x ≤ limit := by
  classical
  intro kept
  have sub (i : Fin p) : (kept i).Sublist (paths i) := List.filter_sublist
  have lifts : ∀ (i : Fin p) (x y : Fin n), Before kept i x y → Before paths i x y :=
    fun _ _ _ => before_pruneLongPrecedenceVisits simple
  have valid : localOrderAdmissible half k kept := by
    cases half
    · intro j hj
      exact ⟨fun b => (allowed hj).false (b.mapPaths id Function.injective_id lifts)⟩
    · intro j hj b earlier
      exact allowed hj (b.mapPaths id Function.injective_id lifts) earlier
  refine ⟨valid, sum_le_sum (fun i _ => (sub i).length_le), ?_⟩
  have edges : pathPrecedenceGraph kept ⊆ pathPrecedenceGraph paths := by
    intro e
    simp only [pathPrecedenceGraph, mem_filter, mem_univ, true_and]
    rintro ⟨i, step⟩
    exact ⟨i, lifts _ _ _ step⟩
  have label {x y : Fin n} (same : componentLabel (pathPrecedenceGraph kept) x =
      componentLabel (pathPrecedenceGraph kept) y) : componentLabel (pathPrecedenceGraph paths) x =
        componentLabel (pathPrecedenceGraph paths) y := by
    obtain ⟨forward, back⟩ := componentLabel_eq.mp same
    exact componentLabel_eq.mpr ⟨reach_mono edges forward, reach_mono edges back⟩
  intro i x
  let old (y : Fin n) := decide (componentLabel (pathPrecedenceGraph paths) x =
    componentLabel (pathPrecedenceGraph paths) y)
  let new (y : Fin n) := decide (componentLabel (pathPrecedenceGraph kept) x =
    componentLabel (pathPrecedenceGraph kept) y)
  let visit := (kept i).filter new
  change visit.length ≤ limit
  by_cases short : precedenceComponentVisitLength paths i x ≤ limit
  · have same : visit.filter old = visit := List.filter_eq_self.mpr (fun y present =>
      decide_eq_true (label (of_decide_eq_true (List.mem_filter.mp present).2)))
    have below : visit.Sublist (paths i) := List.filter_sublist.trans (sub i)
    have contained := below.filter old
    rw [same] at contained
    exact contained.length_le.trans short
  · have empty : visit = [] := List.eq_nil_iff_forall_not_mem.mpr (fun y present => by
      obtain ⟨keptY, same⟩ := List.mem_filter.mp present
      have shortY : precedenceComponentVisitLength paths i y ≤ limit :=
        of_decide_eq_true (List.mem_filter.mp keptY).2
      have equal : precedenceComponentVisitLength paths i x = precedenceComponentVisitLength paths i y := by
        simp only [precedenceComponentVisitLength, label (of_decide_eq_true same)]
      exact short (equal ▸ shortY))
    simp [empty]

/-- It is enough to discard at most one fifty-sixth of the mass in long
visits. The caps are still measured against the original averages. -/
theorem regularization_list_frozen_of_few_long_precedence_visits {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (mostly : let M := ∑ i, (paths i).length
      55 * M ≤ 56 * ∑ i, (pruneLongPrecedenceVisits paths (4 * M / p) i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 108 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  intro M
  let kept := pruneLongPrecedenceVisits paths (4 * M / p)
  have simple' := pruneLongPrecedenceVisits_simple (limit := 4 * M / p) simple
  obtain ⟨legal, mass, cap⟩ := pruneLongPrecedenceVisits_spec (half := false) paths simple free (4 * M / p)
  have split := legal.split_list_vertices_any (copies := splitListVertices kept (4 * M / n))
    (·.fst) (fun {i _ _} => splitListVertices_step (simple' i))
  exact frozen_cleaning_of_width_precedence_components_of_mass (half := false) kept simple'
    hn hp dense long mass cap split (by decide) (by
      dsimp only at mostly
      dsimp only [kept, M]
      omega)

/-- The same mass guarantee and original caps hold with full exclusion
at all sizes. -/
theorem regularization_list_frozen_allFull_of_few_long_precedence_visits {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : ∀ j, IsEmpty (Bridge (Before paths) j)) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (mostly : let M := ∑ i, (paths i).length
      55 * M ≤ 56 * ∑ i, (pruneLongPrecedenceVisits paths (4 * M / p) i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ j, IsEmpty (Bridge (Before clean) j)) ∧
      M ≤ 108 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n', fitsV, p', fitsP, clean, simple', cutoff, retained, cap, caps⟩ :=
    regularization_list_frozen_of_few_long_precedence_visits (k := p + 1)
      paths simple (fun _ _ => free _) hn hp dense long mostly
  exact ⟨n', fitsV, p', fitsP, clean, simple', bridgeFree_all_of_path_budget fitsP cutoff, retained, cap, caps⟩

/-- Long visits can be removed before half-bridge cleaning under the same
degree-split conditions, retaining at least one part in 108. -/
theorem regularization_list_frozen_half_of_few_long_precedence_visits {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k)
    (degreeSafe : k ≤ 4 ∨ BridgeFree (Before paths) (k - 2) ∨
      ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4 * (∑ i, (paths i).length) / n)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (mostly : let M := ∑ i, (paths i).length
      55 * M ≤ 56 * ∑ i, (pruneLongPrecedenceVisits paths (4 * M / p) i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 108 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  intro M
  let kept := pruneLongPrecedenceVisits paths (4 * M / p)
  have simple' := pruneLongPrecedenceVisits_simple (limit := 4 * M / p) simple
  obtain ⟨legal, mass, cap⟩ := pruneLongPrecedenceVisits_spec (half := true) paths simple free (4 * M / p)
  have safe : k ≤ 4 ∨ BridgeFree (Before kept) (k - 2) ∨
      ∀ v, (occurrences (fun i => (kept i).toFinset) v).card ≤ 4 * M / n := by
    rcases degreeSafe with short | full | degrees
    · exact Or.inl short
    · exact Or.inr (Or.inl (pruneLongPrecedenceVisits_spec (half := false) paths simple full (4 * M / p)).1)
    · right
      right
      intro v
      apply le_trans (card_le_card ?_) (degrees v)
      intro i hi
      simp only [mem_occurrences, List.mem_toFinset, kept, pruneLongPrecedenceVisits] at hi ⊢
      exact (List.mem_filter.mp hi).1
  have split := split_list_vertices_half_of_degree_condition simple' legal safe
  exact frozen_cleaning_of_width_precedence_components_of_mass (half := true) kept simple'
    hn hp dense long mass cap split (by decide) (by
      dsimp only at mostly
      dsimp only [kept, M]
      omega)

/-- Different pieces of a parent lie in its strict path order, and the
projected precedence graph has no short return across any cut in that row. -/
def ShortReturnSeparated {V W I J : Type*} [DecidableEq V] [DecidableEq W]
    (G : Arcs V) (project : W → V) (paths : I → List W)
    (pieces : J → List W) (parent : J → I) (cutoff : ℕ) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → parent i = parent j →
    (∀ x ∈ pieces i, ∀ y ∈ pieces j,
      Before paths (parent i) x y ∧ project y ∉ reachIn G (project x) (cutoff-1)) ∨
    (∀ y ∈ pieces j, ∀ x ∈ pieces i,
      Before paths (parent i) y x ∧ project x ∉ reachIn G (project y) (cutoff-1))

private theorem mem_reachIn_of_le {V : Type*} [DecidableEq V] {G : Arcs V} {s t : V} {a b : ℕ}
    (le : a ≤ b) (member : s ∈ reachIn G t a) : s ∈ reachIn G t b := by
  induction b, le using Nat.le_induction with
  | base => exact member
  | succ d _ ih => exact reachIn_subset_succ G t d ih

theorem ShortReturnSeparated.mono {V W I J : Type*} [DecidableEq V] [DecidableEq W]
    {G : Arcs V} {project : W → V} {paths : I → List W} {pieces : J → List W}
    {parent : J → I} {large small : ℕ} (separated : ShortReturnSeparated G project paths pieces parent large)
    (fits : small ≤ large) : ShortReturnSeparated G project paths pieces parent small := by
  intro i j different same
  have short : small-1 ≤ large-1 := Nat.sub_le_sub_right fits 1
  rcases separated different same with earlier | later
  · left
    intro x hx y hy
    exact ⟨(earlier x hx y hy).1,fun member => (earlier x hx y hy).2 (mem_reachIn_of_le short member)⟩
  · right
    intro y hy x hx
    exact ⟨(later y hy x hx).1,fun member => (later y hy x hx).2 (mem_reachIn_of_le short member)⟩

private theorem mem_reachIn_of_steps {V : Type*} [DecidableEq V] {G : Arcs V} (v : ℕ → V) (n : ℕ)
    (arcs : ∀ i < n, Edge G (v i) (v (i+1))) (i j : ℕ) (ordered : i ≤ j) (inside : j ≤ n)
    (depth : ℕ) (long : j-i ≤ depth) : v i ∈ reachIn G (v j) depth := by
  have exact (i d : ℕ) (fits : i+d ≤ n) : v i ∈ reachIn G (v (i+d)) d := by
    induction d generalizing i with
    | zero => exact target_mem_reachIn G (v i) 0
    | succ d ih =>
      have next := ih (i+1) (by omega)
      have index : i+1+d = i+(d+1) := by omega
      rw [index] at next
      exact reachIn_succ.mpr (Or.inr ⟨v (i+1),arcs i (by omega),next⟩)
  have same : i+(j-i) = j := by omega
  have step := exact i (j-i) (by omega)
  rw [same] at step
  exact mem_reachIn_of_le long step

private theorem bridge_of_shortReturnSeparated_split {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [DecidableEq I] {cutoff k : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V) (parent : J → I)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (projects : ∀ {i x y}, Before paths i x y → Edge G (project x) (project y))
    (separated : ShortReturnSeparated G project paths pieces parent (cutoff-2))
    (b : Bridge (Before pieces) k) (small : k+2 ≤ cutoff) :
    ∃ j ≤ k, ∃ old : Bridge (Before paths) j,
      old.river = parent b.river ∧ old.arc (Fin.last j) = parent (b.arc (Fin.last k)) := by
  let endIndex := k+1
  let v (i : ℕ) := b.vertex ⟨min i (k+1),Nat.lt_succ_of_le (min_le_right _ _)⟩
  let owner (i : ℕ) := if atArc : i < endIndex then parent (b.arc ⟨i,atArc⟩) else parent b.river
  have fromFin (i : Fin (k+2)) : v i.val = b.vertex i := by
    have fit : i.val ≤ k+1 := Nat.le_of_lt_succ i.isLt
    exact congrArg b.vertex (Fin.ext (min_eq_left fit))
  have injective : ∀ i ≤ endIndex, ∀ j ≤ endIndex, v i = v j → i = j := by
    intro i hi j hj equal
    have a : v i = b.vertex ⟨i,Nat.lt_succ_of_le hi⟩ := fromFin ⟨i,Nat.lt_succ_of_le hi⟩
    have c : v j = b.vertex ⟨j,Nat.lt_succ_of_le hj⟩ := fromFin ⟨j,Nat.lt_succ_of_le hj⟩
    exact congrArg Fin.val (b.distinctVertices (a.symm.trans (equal.trans c)))
  let arc (i : ℕ) (hi : i < endIndex) := b.arc ⟨i,hi⟩
  have kind (i : ℕ) (hi : i < endIndex) : owner i = parent (arc i hi) := by simp [owner,arc,hi]
  have step (i : ℕ) (hi : i < endIndex) : Before pieces (arc i hi) (v i) (v (i+1)) := by
    let slot : Fin (k+1) := ⟨i,hi⟩
    have src : v i = b.vertex slot.castSucc := fromFin slot.castSucc
    have dst : v (i+1) = b.vertex slot.succ := fromFin slot.succ
    rw [src,dst]
    exact b.arcStep slot
  have river : Before pieces b.river (v 0) (v endIndex) := by
    have src : v 0 = b.vertex 0 := fromFin (0 : Fin (k+2))
    have dst : v endIndex = b.vertex (Fin.last (k+1)) := fromFin (Fin.last (k+1))
    rw [src,dst]
    exact b.riverStep
  have edge (i : ℕ) (hi : i < endIndex) : Edge G (project (v i)) (project (v (i+1))) :=
    projects (steps (step i hi))
  have along (i j : ℕ) (ij : i ≤ j) (inside : j ≤ endIndex) (length : j-i ≤ (cutoff-2)-1) :
      project (v i) ∈ reachIn G (project (v j)) ((cutoff-2)-1) :=
    mem_reachIn_of_steps (project ∘ v) endIndex edge i j ij inside _ length
  have noRiver (i : ℕ) (hi : i < endIndex) : parent b.river ≠ owner i := by
    rw [kind i hi]
    intro same
    have cuts := separated (b.river_ne_arc ⟨i,hi⟩) same
    have disjoint (x : W) (onRiver : x ∈ pieces b.river) (onArc : x ∈ pieces (arc i hi)) : False := by
      rcases cuts with forward | reverse
      · exact listBefore_ne (forward x onRiver x onArc).1 rfl
      · exact listBefore_ne (reverse x onArc x onRiver).1 rfl
    have pos : 0 < i := by
      by_contra! first
      have atStart : i = 0 := by omega
      exact disjoint (v 0) river.1 (atStart ▸ (step i hi).1)
    have internal : i+1 < endIndex := by
      by_contra! last
      have atEnd : i+1 = endIndex := by omega
      exact disjoint (v endIndex) river.2.1 (atEnd ▸ (step i hi).2.1)
    rcases cuts with forward | reverse
    · exact (forward _ river.2.1 _ (step i hi).2.1).2
        (along (i+1) endIndex internal.le le_rfl (by dsimp only [endIndex]; omega))
    · exact (reverse _ (step i hi).1 _ river.1).2
        (along 0 i (Nat.zero_le _) hi.le (by dsimp only [endIndex] at internal; omega))
  have shorten (i j : ℕ) (ij : i ≤ j) (jn : j < endIndex) (same : owner i = owner j) :
      Before paths (owner i) (v i) (v (j+1)) := by
    by_cases eq : i = j
    · subst j
      rw [kind i jn]
      exact steps (step i jn)
    have inside := ij.trans_lt jn
    have parentEq : parent (arc i inside) = parent (arc j jn) := by
      simpa only [kind i inside,kind j jn] using same
    have different : arc i inside ≠ arc j jn := fun equal => eq (congrArg Fin.val (b.distinctArcs equal))
    rcases separated different parentEq with forward | reverse
    · rw [kind i inside]
      exact (forward _ (step i inside).1 _ (step j jn).2.1).1
    · exact ((reverse _ (step j jn).1 _ (step i inside).2.1).2
        (along (i+1) j (by omega) jn.le (by dsimp only [endIndex] at jn; omega))).elim
  obtain ⟨size', short, original, riverOwner, last⟩ := bridge_from_forward_repetitions
    (Before paths) v owner (parent b.river) endIndex (by dsimp [endIndex]; omega)
    injective (steps river) noRiver shorten
  refine ⟨size',by dsimp only [endIndex] at short; omega,original,riverOwner,last.trans ?_⟩
  have final : endIndex-1 = k := by simp [endIndex]
  rw [final,kind k (Nat.lt_succ_self k)]
  rfl

/-- The shortest return forced by separated pieces omits the endpoint arcs
of the detour. The original bridge cutoff thus only needs a radius of
`cutoff - 3` for returns. -/
theorem bridgeFree_of_shortReturnSeparated_smaller_cutoff {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [DecidableEq I] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V)
    (free : BridgeFree (Before paths) cutoff) (parent : J → I)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (projects : ∀ {i x y}, Before paths i x y → Edge G (project x) (project y))
    (separated : ShortReturnSeparated G project paths pieces parent (cutoff-2)) : BridgeFree (Before pieces) cutoff := by
  intro k size
  refine ⟨fun b => ?_⟩
  obtain ⟨j,short,old,_,_⟩ := bridge_of_shortReturnSeparated_split G project parent steps projects separated b size
  exact (free (k := j) (by omega)).false old

/-- The same shorter return radius preserves half exclusion when the
pieces preserve their parents' arrival order. -/
theorem halfBridgeFree_of_shortReturnSeparated_smaller_cutoff {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [LinearOrder I] [LinearOrder J] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V)
    (free : HalfBridgeFree (Before paths) cutoff) (parent : J → I) (arrives : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (projects : ∀ {i x y}, Before paths i x y → Edge G (project x) (project y))
    (separated : ShortReturnSeparated G project paths pieces parent (cutoff-2)) : HalfBridgeFree (Before pieces) cutoff := by
  intro k size b earlier
  obtain ⟨j,short,old,river,last⟩ := bridge_of_shortReturnSeparated_split G project parent steps projects separated b size
  have ordered := arrives earlier.le
  rw [← river, ← last] at ordered
  exact free (k := j) (by omega) old (ordered.lt_of_ne (old.river_ne_arc _).symm)

/-- A split that excludes short returns across cuts preserves every full
bridge exclusion through the given cutoff. Longer cycles may remain. -/
theorem bridgeFree_of_shortReturnSeparated_split {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [DecidableEq I] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V)
    (free : BridgeFree (Before paths) cutoff) (parent : J → I)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (projects : ∀ {i x y}, Before paths i x y → Edge G (project x) (project y))
    (separated : ShortReturnSeparated G project paths pieces parent cutoff) : BridgeFree (Before pieces) cutoff :=
  bridgeFree_of_shortReturnSeparated_smaller_cutoff G project free parent steps projects
    (separated.mono (Nat.sub_le _ _))

/-- A split with no short returns also preserves half exclusion if the
pieces preserve their parents' arrival order. -/
theorem halfBridgeFree_of_shortReturnSeparated_split {V W I J : Type*}
    [DecidableEq V] [DecidableEq W] [LinearOrder I] [LinearOrder J] {cutoff : ℕ}
    {paths : I → List W} {pieces : J → List W} (G : Arcs V) (project : W → V)
    (free : HalfBridgeFree (Before paths) cutoff) (parent : J → I) (arrives : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (projects : ∀ {i x y}, Before paths i x y → Edge G (project x) (project y))
    (separated : ShortReturnSeparated G project paths pieces parent cutoff) : HalfBridgeFree (Before pieces) cutoff :=
  halfBridgeFree_of_shortReturnSeparated_smaller_cutoff G project free parent arrives steps projects
    (separated.mono (Nat.sub_le _ _))

/-- Every nonempty directed cycle in the precedence graph has length
greater than `cutoff`. The condition is expressed using a bounded return
search from each edge's head to its tail. -/
def NoShortPrecedenceCycle {n p : ℕ} (paths : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  ∀ ⦃x y⦄, Edge (pathPrecedenceGraph paths) x y →
    y ∉ reachIn (pathPrecedenceGraph paths) x (cutoff-1)

theorem NoShortPrecedenceCycle.mono {n p small large : ℕ} {paths : Fin p → List (Fin n)}
    (noCycles : NoShortPrecedenceCycle paths large) (fits : small ≤ large) :
    NoShortPrecedenceCycle paths small := by
  intro x y edge back
  exact noCycles edge (mem_reachIn_of_le (Nat.sub_le_sub_right fits 1) back)

/-- Projected river endpoints remain distinct. A collision leaving a single
exterior arc would give a two-bridge, so only cycles through `k - 3` matter. -/
theorem splitListVertices_halfFree_of_noShortPrecedenceCycle_smaller_cutoff {n p k D : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (longCycles : NoShortPrecedenceCycle paths (k-3)) :
    HalfBridgeFree (Before (splitListVertices paths D)) k := by
  classical
  intro j size b earlier
  let G := pathPrecedenceGraph paths
  let last := j+1
  let v (i : ℕ) := (b.vertex ⟨min i (j+1),Nat.lt_succ_of_le (min_le_right _ _)⟩).fst
  have fromFin (i : Fin (j+2)) : v i.val = (b.vertex i).fst := by
    have fit : i.val ≤ j+1 := Nat.le_of_lt_succ i.isLt
    exact congrArg (fun a => (b.vertex a).fst) (Fin.ext (min_eq_left fit))
  have river : Before paths b.river (v 0) (v last) := by
    have first : v 0 = (b.vertex 0).fst := fromFin (0 : Fin (j+2))
    have finish : v last = (b.vertex (Fin.last (j+1))).fst := fromFin (Fin.last (j+1))
    rw [first,finish]
    exact splitListVertices_step (simple _) b.riverStep
  have pathStep (i : ℕ) (hi : i < last) : Before paths (b.arc ⟨i,hi⟩) (v i) (v (i+1)) := by
    let slot : Fin (j+1) := ⟨i,hi⟩
    have source : v i = (b.vertex slot.castSucc).fst := fromFin slot.castSucc
    have target : v (i+1) = (b.vertex slot.succ).fst := fromFin slot.succ
    rw [source,target]
    exact splitListVertices_step (simple _) (b.arcStep slot)
  have edge (i : ℕ) (hi : i < last) : Edge G (v i) (v (i+1)) := by
    unfold G Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _,b.arc ⟨i,hi⟩,pathStep i hi⟩
  have noExterior (i : ℕ) (hi : i < last) (first : v i = v 0) (finish : v (i+1) = v last) : False := by
    have step := pathStep i hi
    rw [first,finish] at step
    exact no_parallel_list_steps free (by omega) (b.river_ne_arc _) river step
  have separate {a c : Fin (j+2)} (forward : a < c) (equal : (b.vertex a).fst = (b.vertex c).fst) : False := by
    have fits : c.val ≤ last := Nat.le_of_lt_succ c.isLt
    have before : a.val < c.val := forward
    have same : v a.val = v c.val := (fromFin a).trans (equal.trans (fromFin c).symm)
    have span : c.val-a.val+1 < last := by
      by_contra! whole
      have ends : (a.val = 0 ∧ c.val = last) ∨ (a.val = 0 ∧ c.val+1 = last) ∨
          (a.val = 1 ∧ c.val = last) := by omega
      rcases ends with ⟨head,tail⟩ | ⟨head,tail⟩ | ⟨head,tail⟩
      · exact listBefore_ne river (by rwa [head,tail] at same)
      · exact noExterior c.val (by omega) (by simpa only [head] using same.symm) (congrArg v tail)
      · exact noExterior 0 (by omega) rfl (by rwa [head,tail] at same)
    have step := edge a.val (by omega)
    have back := mem_reachIn_of_steps v last edge (a.val+1) c.val (by omega) fits ((k-3)-1)
      (by dsimp only [last] at span; omega)
    rw [← same] at back
    exact longCycles step back
  have injective : Function.Injective (fun i => (b.vertex i).fst) := by
    intro a c equal
    by_contra distinct
    rcases lt_or_gt_of_ne distinct with forward | backward
    · exact separate forward equal
    · exact separate backward equal.symm
  let original : Bridge (Before paths) j :=
    ⟨fun i => (b.vertex i).fst,b.arc,b.river,injective,b.distinctArcs,b.river_ne_arc,
      splitListVertices_step (simple _) b.riverStep,fun slot => splitListVertices_step (simple _) (b.arcStep slot)⟩
  exact free size original earlier

/-- A collision of projected detour corners would close a short directed
walk. With no such return, the vertex split keeps the last arc and river. -/
theorem splitListVertices_halfFree_of_noShortPrecedenceCycle {n p k D : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (longCycles : NoShortPrecedenceCycle paths k) :
    HalfBridgeFree (Before (splitListVertices paths D)) k :=
  splitListVertices_halfFree_of_noShortPrecedenceCycle_smaller_cutoff paths simple free
    (longCycles.mono (Nat.sub_le _ _))

private theorem width_blocks_admissible_of_noShortPrecedenceCycle {n p k D L : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : localOrderAdmissible half k (splitListVertices paths D))
    (longCycles : NoShortPrecedenceCycle paths (k-2)) : localOrderAdmissible half k (listRegularizedPaths paths D L) := by
  classical
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let parent (j : ListBlockIndex copies L) := j.fst
  let G := pathPrecedenceGraph paths
  let copy := fun v : ListVertexBlockIndex paths D => v.fst
  have projects {i x y} (step : Before copies i x y) : Edge G (copy x) (copy y) := by
    have order := splitListVertices_step (simple i) step
    unfold G Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _,i,order⟩
  have steps {i x y} (step : Before pieces i x y) : Before copies (parent i) x y :=
    listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (splitListVertices_simple paths D i.fst (simple i.fst)) List.filter_sublist step
  have separated : ShortReturnSeparated G copy copies pieces parent (k-2) := by
    intro i j distinct same
    rcases contiguousBlocks_separated distinct same with earlier | later
    · left
      intro x hx y hy
      exact ⟨earlier hx hy,longCycles (projects (earlier hx hy))⟩
    · right
      intro y hy x hx
      exact ⟨later hx hy,longCycles (projects (later hx hy))⟩
  have arrivals : Monotone parent := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with earlier | ⟨same, _⟩
    · exact earlier.le
    · exact same.le
  cases half
  · exact bridgeFree_of_shortReturnSeparated_smaller_cutoff G copy legal parent steps projects separated
  · exact halfBridgeFree_of_shortReturnSeparated_smaller_cutoff G copy legal parent arrivals steps projects separated

private theorem frozen_cleaning_of_noShortPrecedenceCycle_of_mass {n p k M retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (longCycles : NoShortPrecedenceCycle paths (k-2))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (upper : (∑ i, (paths i).length) ≤ M)
    (lower : 8*(retention+2)*M ≤ 9*retention*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have copyLegal : localOrderAdmissible half k (splitListVertices paths (4*M/n)) := by
    cases half
    · exact free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
    · exact splitListVertices_halfFree_of_noShortPrecedenceCycle_smaller_cutoff paths simple free
        (longCycles.mono (by omega))
  have legal := width_blocks_admissible_of_noShortPrecedenceCycle (L := 4*M/p) paths simple copyLegal longCycles
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple legal hn hp dense long upper lower

/-- At bridge cutoff `k`, the original factor-four width blocks suffice if
there are no precedence cycles of length at most `k - 2`. -/
theorem regularization_list_frozen_of_noShortPrecedenceCycle_smaller_cutoff {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (longCycles : NoShortPrecedenceCycle paths (k-2))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_noShortPrecedenceCycle_of_mass paths simple free longCycles
    hn hp dense long le_rfl (by omega)

/-- The original factor-four width cuts suffice when the precedence graph
has no directed cycle through the bridge cutoff. Longer cycles may remain.
Both vertices and paths can be split in either bridge mode. -/
theorem regularization_list_frozen_of_noShortPrecedenceCycle {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (longCycles : NoShortPrecedenceCycle paths k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_noShortPrecedenceCycle_smaller_cutoff paths simple free
    (longCycles.mono (Nat.sub_le _ _)) hn hp dense long

/-- If deleting at most one eighteenth of the incidences removes the
short precedence cycles, cleaning keeps one thirty-second of the original
mass and uses the original budgets and averages. -/
theorem regularization_list_frozen_after_short_cycle_deletions_smaller_cutoff {n p k : ℕ} {half : Bool}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (sub : ∀ i, (kept i).Sublist (paths i))
    (longCycles : NoShortPrecedenceCycle kept (k-2))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  intro M
  have lifts (i : Fin p) (x y : Fin n) (step : Before kept i x y) : Before paths i x y :=
    listBefore_of_sublist (simple i) (sub i) step
  have monoFull {size : ℕ} (full : BridgeFree (Before paths) size) : BridgeFree (Before kept) size := by
    intro j hj
    exact ⟨fun b => (full hj).false (b.mapPaths id Function.injective_id lifts)⟩
  have valid : localOrderAdmissible half k kept := by
    cases half
    · exact monoFull free
    · intro j hj b arrival
      exact free hj (b.mapPaths id Function.injective_id lifts) arrival
  refine frozen_cleaning_of_noShortPrecedenceCycle_of_mass kept (fun i => (sub i).nodup (simple i))
    valid longCycles hn hp dense long (sum_le_sum (fun i _ => (sub i).length_le)) ?_
  change 17*M ≤ 18*(∑ i, (kept i).length) at retained
  omega

/-- Removing short cycles through the bridge cutoff also suffices. -/
theorem regularization_list_frozen_after_short_cycle_deletions {n p k : ℕ} {half : Bool}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (sub : ∀ i, (kept i).Sublist (paths i))
    (longCycles : NoShortPrecedenceCycle kept k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_after_short_cycle_deletions_smaller_cutoff paths kept simple free sub
    (longCycles.mono (Nat.sub_le _ _)) hn hp dense long retained

end OnlineReachabilityPreservers
