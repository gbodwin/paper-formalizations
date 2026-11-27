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

private theorem splitListVertices_rank_order {n p : ℕ} {paths : Fin p → List (Fin n)} (D : ℕ)
    (i : Fin p) (simple : (paths i).Nodup) (rank : Fin n → ℕ)
    (monotone : ∀ {x y}, Before paths i x y → rank x ≤ rank y) :
    (splitListVertices paths D i).Pairwise (fun x y => rank x.fst ≤ rank y.fst) := by
  let project (v : ListVertexBlockIndex paths D) : Fin n := v.fst
  have ordered : ((splitListVertices paths D i).map project).Pairwise
      (fun x y => rank x ≤ rank y) := by
    change ((splitListVertices paths D i).map (fun v => v.fst)).Pairwise _
    rw [splitListVertices_project]
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb ab
    have step : Before paths i (paths i)[a] (paths i)[b] :=
      ⟨List.getElem_mem ha, List.getElem_mem hb, by simpa only [simple.idxOf_getElem] using ab⟩
    exact monotone step
  exact (List.pairwise_map (f := project)
    (R := fun x y => rank x ≤ rank y)).mp ordered

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

private def RankedCopiedAssemblyAdmissible {V : Type*} [LinearOrder V] {p : ℕ}
    (rows : Fin p → List V) (k : ℕ) (half : Bool) (rank : Fin p → V → ℕ) : Prop :=
  ∀ {sizes : Fin p → ℕ}
    (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
    (∀ i, (pieces i).Sublist (rows i.fst)) →
    (∀ {i j}, i ≠ j → i.fst = j.fst →
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank i.fst x < rank i.fst y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rank i.fst y < rank i.fst x)) →
    localOrderAdmissible half k pieces

private abbrev RankedRunAssemblyAdmissible {n p : ℕ} (paths : Fin p → List (Fin n))
    (D k : ℕ) (half : Bool) (rank : Fin p → Fin n → ℕ) : Prop :=
  RankedCopiedAssemblyAdmissible (splitListVertices paths D) k half (fun i v => rank i v.fst)

set_option maxHeartbeats 1000000 in
private theorem frozen_cleaning_after_ranked_copied_rows {V : Type*} [LinearOrder V] [Fintype V]
    {n p k M retention vNum vDen pNum pDen : ℕ} {half : Bool}
    (rows : Fin p → List V) (simple : ∀ i, (rows i).Nodup)
    (mass : (∑ i, (rows i).length) ≤ M) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (limit : ℕ) (fits : limit ≤ 4*M/p)
    (rowRank : Fin p → V → ℕ) (order : ∀ i, (rows i).Pairwise (fun x y => rowRank i x ≤ rowRank i y))
    (fibreCap : ∀ i r, ((rows i).filter (fun x => decide (rowRank i x = r))).length ≤ limit)
    (legal : RankedCopiedAssemblyAdmissible rows k half rowRank)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vRoom : vNum*Fintype.card V ≤ vDen*n)
    (copiedDegree : ∀ v, (occurrences (fun i => (rows i).toFinset) v).card ≤ 4*M/n)
    (pathBudget : ∀ q,
      let L := 4*M/p
      let minimum := L+1-limit
      minimum*q ≤ M+p*minimum → (L+1)*q ≤ 2*M+p*(L+1) → pNum*q ≤ pDen*p)
    (retained : (vDen*pDen)*(retention+2)*M ≤ 2*(vNum*pNum)*retention*(∑ i, (rows i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let D := 4*M/n
  let L := 4*M/p
  let minimum := L+1-limit
  choose packed flatten separated cap count pairs using fun i =>
    packedWidthPieces (rowRank i) limit L fits (rows i) (order i) (fibreCap i)
  let P := Σₗ i : Fin p, Fin (packed i).length
  let pieces (i : P) := (packed i.1).get i.2
  have membership (i : P) : pieces i ∈ packed i.1 := List.get_mem _ _
  have sub (i : P) : (pieces i).Sublist (rows i.1) :=
    flatten i.1 ▸ List.sublist_flatten_of_mem (membership i)
  have apart {i j : P} (distinct : i ≠ j) (same : i.1 = j.1) :
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rowRank i.fst x < rowRank i.fst y) ∨
      (∀ x ∈ pieces i, ∀ y ∈ pieces j, rowRank i.fst y < rowRank i.fst x) := by
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
  have packedLegal := legal pieces sub apart
  have qRoom : pNum * Fintype.card P ≤ pDen * p := by
    rw [Fintype.card_lex, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    apply pathBudget
    · change minimum * (∑ i, (packed i).length) ≤ M + p * minimum
      rw [mul_sum]
      calc
        _ ≤ ∑ i, ((rows i).length + minimum) := Finset.sum_le_sum fun i _ => count i
        _ = (∑ i, (rows i).length) + p * minimum := by simp [sum_add_distrib]
        _ ≤ _ := Nat.add_le_add_right mass _
    · rw [mul_sum]
      calc
        _ ≤ ∑ i, (2 * (rows i).length + (L + 1)) := Finset.sum_le_sum fun i _ => pairs i
        _ = 2 * (∑ i, (rows i).length) + p * (L + 1) := by simp [sum_add_distrib, mul_sum]
        _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 2 mass) _
  have degree (v : V) : (occurrences (fun i => (pieces i).toFinset) v).card ≤ D := by
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
  have total : (∑ i, (pieces i).length) = ∑ i, (rows i).length := by
    change (∑ i : Sigma (fun j => Fin (packed j).length), ((packed i.1).get i.2).length) = _
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    change (∑ q : Fin (packed i).length, ((packed i).get q).length) = (rows i).length
    have sameLength := congrArg List.length (flatten i)
    rw [← sameLength,List.length_flatten]
    rw [← List.sum_ofFn]
    have lengthRows := congrArg (List.map List.length) (List.ofFn_get (packed i))
    rw [List.map_ofFn] at lengthRows
    exact congrArg List.sum lengthRows
  exact regularization_list_frozen_after_caps_with_ratios_of_mass (half := half) pieces
    (fun i => (sub i).nodup (simple i.1))
    packedLegal hn hp dense long vPos pPos vRatio pRatio vRoom qRoom
    (fun i => cap i.1 _ (membership i)) degree (total.trans_le mass) (by rw [total]; exact retained)

set_option maxHeartbeats 1000000 in
private theorem frozen_cleaning_of_ranked_runs {n p k M retention vNum vDen pNum pDen : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (mass : (∑ i, (paths i).length) ≤ M) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (limit : ℕ) (fits : limit ≤ 4 * M / p)
    (rank : Fin p → Fin n → ℕ)
    (monotone : ∀ {i x y}, Before paths i x y → rank i x ≤ rank i y)
    (small : ∀ i r, ((paths i).filter (fun x => decide (rank i x = r))).length ≤ limit)
    (legal : RankedRunAssemblyAdmissible paths (4 * M / n) k half rank)
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
  obtain ⟨dPos, _, _⟩ := four_average_width hn dense
  have copied := (regularization_list_counts paths simple (D := D) dPos Nat.one_pos).1
  rw [Fintype.card_fin] at copied
  have copiedBound : Fintype.card (ListVertexBlockIndex paths D) ≤ n + M / D :=
    copied.trans (Nat.add_le_add_left (Nat.div_le_div_right mass) n)
  have vRoom : vNum * Fintype.card (ListVertexBlockIndex paths D) ≤ vDen * n :=
    (Nat.mul_le_mul_left vNum copiedBound).trans vertexBudget
  let rows := splitListVertices paths D
  let rowRank (i : Fin p) (v : ListVertexBlockIndex paths D) := rank i v.fst
  have order (i : Fin p) : (rows i).Pairwise (fun x y => rowRank i x ≤ rowRank i y) :=
    splitListVertices_rank_order D i (simple i) (rank i) monotone
  have fibreCap (i : Fin p) (r : ℕ) : ((rows i).filter (fun v => decide (rowRank i v = r))).length ≤ limit := by
    have filtered := congrArg (fun l : List (Fin n) =>
      (l.filter (fun v => decide (rank i v = r))).length) (splitListVertices_project paths D i)
    rw [List.filter_map, List.length_map] at filtered
    exact filtered.trans_le (small i r)
  have copiedDegree (v : ListVertexBlockIndex paths D) :
      (occurrences (fun i => (rows i).toFinset) v).card ≤ D := by
    simpa only [rows, splitListVertices_toFinset] using
      (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
  have rowMass : (∑ i, (rows i).length) ≤ M := by simpa only [rows,splitListVertices_length] using mass
  have enough : (vDen*pDen)*(retention+2)*M ≤ 2*(vNum*pNum)*retention*(∑ i, (rows i).length) := by
    simpa only [rows,splitListVertices_length] using retained
  exact frozen_cleaning_after_ranked_copied_rows rows (fun i => splitListVertices_simple paths D i (simple i))
    rowMass hn hp dense long limit fits rowRank order fibreCap legal vPos pPos vRatio pRatio
    vRoom copiedDegree pathBudget enough

set_option maxHeartbeats 1000000 in
private theorem componentRankAssemblyAdmissible {n p k D : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : localOrderAdmissible half k (splitListVertices paths D)) :
    RankedRunAssemblyAdmissible paths D k half (fun _ => precedenceRank paths) := by
  intro sizes pieces sub apart
  let P := Σₗ i : Fin p, Fin (sizes i)
  let rank (v : ListVertexBlockIndex paths D) := precedenceRank paths v.fst
  have pieceStep {i x y} (step : Before pieces i x y) : Before (splitListVertices paths D) i.fst x y :=
    listBefore_of_sublist (paths := fun j : P => splitListVertices paths D j.fst)
      (splitListVertices_simple paths _ i.fst (simple i.fst)) (sub i) step
  have rankMono {i x y} (step : Before (splitListVertices paths D) i x y) : rank x ≤ rank y :=
    precedenceRank_mono (splitListVertices_step (simple i) step)
  have arrival : Monotone (fun i : P => i.fst) := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with before | ⟨same, _⟩
    · exact before.le
    · exact same.le
  cases half
  · exact bridgeFree_of_rank_separated_split legal (fun i : P => i.fst) rank pieceStep rankMono apart
  · exact halfBridgeFree_of_rank_separated_split legal (fun i : P => i.fst) arrival rank pieceStep rankMono apart

private theorem frozen_cleaning_of_small_ranked_runs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (rank : Fin p → Fin n → ℕ)
    (monotone : ∀ {i x y}, Before paths i x y → rank i x ≤ rank i y)
    (small : ∀ i r, ((paths i).filter (fun x => decide (rank i x = r))).length ≤ (∑ i, (paths i).length) / p)
    (legal : RankedRunAssemblyAdmissible paths (4 * (∑ i, (paths i).length) / n) k half rank) :
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
  refine frozen_cleaning_of_ranked_runs (half := half) paths simple le_rfl hn hp dense long limit fits
    rank monotone small legal
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

private theorem frozen_cleaning_of_small_precedence_components {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : ∀ i x, precedenceComponentVisitLength paths i x ≤ (∑ i, (paths i).length) / p)
    (legal : localOrderAdmissible half k (splitListVertices paths (4 * (∑ i, (paths i).length) / n))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_small_ranked_runs paths simple hn hp dense long
    (fun _ => precedenceRank paths) (fun step => precedenceRank_mono step)
    (small_component_rank_fibre paths _ small) (componentRankAssemblyAdmissible paths simple legal)

private theorem frozen_width_copy_budget {n p M : ℕ}
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (substantial : 2*n ≤ M) :
    let D := 4*M/n
    let L := 4*M/p
    7*(n+M/D) ≤ 9*n ∧
      (∀ q, (L+1)*q ≤ 2*M+p*(L+1) → 2*q ≤ 3*p) := by
  let D := 4*M/n
  let L := 4*M/p
  obtain ⟨dPos, _, _⟩ := four_average_width hn dense
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
  refine ⟨vertexBudget,?_⟩
  intro q pairs
  change (L + 1) * q ≤ 2 * M + p * (L + 1) at pairs
  have lFloor : 4 * M < p * (L + 1) := Nat.lt_mul_div_succ (4 * M) hp
  have positive : 0 < L + 1 := Nat.succ_pos L
  apply Nat.le_of_mul_le_mul_left _ positive
  calc
    _ = 2 * ((L + 1) * q) := by ring
    _ ≤ 2 * (2 * M + p * (L + 1)) := Nat.mul_le_mul_left _ pairs
    _ ≤ 3 * (p * (L + 1)) := by omega
    _ = _ := by ring

private theorem frozen_cleaning_of_width_ranked_runs_of_mass {n p k M retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (mass : (∑ i, (paths i).length) ≤ M)
    (rank : Fin p → Fin n → ℕ)
    (monotone : ∀ {i x y}, Before paths i x y → rank i x ≤ rank i y)
    (runs : ∀ i r, ((paths i).filter (fun x => decide (rank i x = r))).length ≤ 4 * M / p)
    (legal : RankedRunAssemblyAdmissible paths (4 * M / n) k half rank)
    (sparseRetention : 6 ≤ retention)
    (enough : 27 * (retention + 2) * M ≤ 28 * retention * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4 * M / n
  let L := 4 * M / p
  by_cases substantial : 2 * n ≤ M
  · obtain ⟨vertexBudget,pathRoom⟩ := frozen_width_copy_budget hn hp dense substantial
    refine frozen_cleaning_of_ranked_runs (half := half) paths simple mass hn hp dense long L le_rfl
      rank monotone runs legal
      (vNum := 7) (vDen := 9) (pNum := 2) (pDen := 3)
      (by decide) (by decide) (by decide) (by decide) vertexBudget ?_ enough
    dsimp only
    intro q _ pairs
    exact pathRoom q pairs
  · have light : M ≤ 3 * max n p := by have top := le_max_left n p; omega
    obtain ⟨n', fitsV, p', fitsP, clean, simple', free, keep, cap, caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long light
    have allowed : localOrderAdmissible half k clean := by
      cases half
      · exact free
      · exact free.halfFree
    exact ⟨n', fitsV, p', fitsP, clean, simple', allowed,
      keep.trans (Nat.mul_le_mul_right _ sparseRetention), cap, caps⟩

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
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_width_ranked_runs_of_mass paths simple hn hp dense long mass
    (fun _ => precedenceRank paths) (fun step => precedenceRank_mono step)
    (small_component_rank_fibre paths _ visits) (componentRankAssemblyAdmissible paths simple legal)
    sparseRetention enough

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

private theorem localOrderAdmissible_of_sublist {V : Type*} [DecidableEq V] {p k : ℕ} {half : Bool}
    {paths kept : Fin p → List V} (simple : ∀ i, (paths i).Nodup)
    (sub : ∀ i, (kept i).Sublist (paths i))
    (free : localOrderAdmissible half k paths) : localOrderAdmissible half k kept := by
  have lifts (i : Fin p) (x y : V) (step : Before kept i x y) : Before paths i x y :=
    listBefore_of_sublist (simple i) (sub i) step
  cases half
  · intro j size
    exact ⟨fun b => (free size).false (b.mapPaths id Function.injective_id lifts)⟩
  · intro j size b earlier
    exact free size (b.mapPaths id Function.injective_id lifts) earlier

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
    (projects : ∀ {i x y}, Before pieces i x y → Edge G (project x) (project y))
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
    projects (step i hi)
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
  obtain ⟨j,short,old,_,_⟩ := bridge_of_shortReturnSeparated_split G project parent steps  (fun {_ _ _} step => projects (steps step)) separated b size
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
  obtain ⟨j,short,old,river,last⟩ := bridge_of_shortReturnSeparated_split G project parent steps  (fun {_ _ _} step => projects (steps step)) separated b size
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

/-- A bounded return is forbidden when its endpoints lie across an actual
width-block cut of an original row. Returns inside one block can remain. -/
def NoShortReturnAcrossWidthCuts {n p : ℕ} (paths : Fin p → List (Fin n)) (width cutoff : ℕ) : Prop :=
  ∀ ⦃i x y⦄, Before paths i x y → (paths i).idxOf x / width ≠ (paths i).idxOf y / width →
    y ∉ reachIn (pathPrecedenceGraph paths) x ((cutoff-2)-1)

theorem NoShortPrecedenceCycle.noShortReturnAcrossWidthCuts {n p k L : ℕ} {paths : Fin p → List (Fin n)}
    (longCycles : NoShortPrecedenceCycle paths (k-2)) : NoShortReturnAcrossWidthCuts paths L k := by
  classical
  intro i x y before _
  apply longCycles
  unfold Edge pathPrecedenceGraph
  exact mem_filter.mpr ⟨mem_univ _,i,before⟩

private theorem splitListVertices_idxOf_project {n p : ℕ} (paths : Fin p → List (Fin n))
    (D : ℕ) (i : Fin p) (simple : (paths i).Nodup) {v : ListVertexBlockIndex paths D}
    (member : v ∈ splitListVertices paths D i) :
    (paths i).idxOf v.fst = (splitListVertices paths D i).idxOf v := by
  let row := splitListVertices paths D i
  let index := row.idxOf v
  let project := fun a : ListVertexBlockIndex paths D => a.fst
  have on : index < row.length := List.idxOf_lt_length_of_mem member
  have onMap : index < (row.map project).length := by simpa only [List.length_map] using on
  have sameRow : row.map project = paths i := splitListVertices_project paths D i
  have atIndex : (row.map project)[index] = v.fst := by
    rw [List.getElem_map]
    exact congrArg project (List.getElem_idxOf on)
  have mappedSimple : (row.map project).Nodup := sameRow.symm ▸ simple
  rw [← sameRow,← atIndex]
  exact mappedSimple.idxOf_getElem index onMap

private theorem width_blocks_admissible_of_noShortReturnAcrossWidthCuts {n p k D L : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : localOrderAdmissible half k (splitListVertices paths D))
    (noReturns : NoShortReturnAcrossWidthCuts paths L k) : localOrderAdmissible half k (listRegularizedPaths paths D L) := by
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
  have separatedIndices {i j : ListBlockIndex copies L} (distinct : i ≠ j) (same : i.fst = j.fst)
      {x y} (hx : x ∈ pieces i) (hy : y ∈ pieces j) :
      (paths i.fst).idxOf (copy x) / L ≠ (paths i.fst).idxOf (copy y) / L := by
    rcases i with ⟨a,ia⟩
    rcases j with ⟨b,jb⟩
    change a = b at same
    subst b
    obtain ⟨onX,blockX⟩ := mem_localPathBlock.mp hx
    obtain ⟨onY,blockY⟩ := mem_localPathBlock.mp hy
    change (paths a).idxOf x.fst / L ≠ (paths a).idxOf y.fst / L
    rw [splitListVertices_idxOf_project paths D a (simple a) onX,
      splitListVertices_idxOf_project paths D a (simple a) onY]
    intro eq
    exact distinct (congrArg (Sigma.mk a) (Fin.ext (blockX.symm.trans (eq.trans blockY))))
  have separated : ShortReturnSeparated G copy copies pieces parent (k-2) := by
    intro i j distinct same
    rcases contiguousBlocks_separated distinct same with earlier | later
    · left
      intro x hx y hy
      have step := earlier hx hy
      exact ⟨step,noReturns (splitListVertices_step (simple _) step) (separatedIndices distinct same hx hy)⟩
    · right
      intro y hy x hx
      have step := later hx hy
      exact ⟨step,noReturns (splitListVertices_step (simple _) step) (separatedIndices distinct same hx hy).symm⟩
  have arrivals : Monotone parent := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with earlier | ⟨same, _⟩
    · exact earlier.le
    · exact same.le
  cases half
  · exact bridgeFree_of_shortReturnSeparated_smaller_cutoff G copy legal parent steps projects separated
  · exact halfBridgeFree_of_shortReturnSeparated_smaller_cutoff G copy legal parent arrivals steps projects separated

/-- Each of these conditions suffices for the degree split to preserve
half exclusion at the given cutoff. -/
def HalfDegreeSplitCondition {n p : ℕ} (paths : Fin p → List (Fin n)) (width cutoff : ℕ) : Prop :=
  NoShortPrecedenceCycle paths (cutoff-3) ∨ cutoff ≤ 4 ∨ BridgeFree (Before paths) (cutoff-2) ∨
    ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ width

private theorem splitListVertices_admissible_of_halfDegreeSplitCondition {n p k D : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths)
    (halfSafe : half = true → HalfDegreeSplitCondition paths D k) :
    localOrderAdmissible half k (splitListVertices paths D) := by
  cases half
  · exact free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  · rcases halfSafe rfl with noCycles | degreeSafe
    · exact splitListVertices_halfFree_of_noShortPrecedenceCycle_smaller_cutoff paths simple free noCycles
    · exact split_list_vertices_half_of_degree_condition simple free degreeSafe

private theorem frozen_cleaning_of_noShortReturnAcrossWidthCuts_of_mass {n p k M retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (returns : NoShortReturnAcrossWidthCuts paths (4*M/p) k)
    (halfSafe : half = true → HalfDegreeSplitCondition paths (4*M/n) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (upper : (∑ i, (paths i).length) ≤ M)
    (lower : 8*(retention+2)*M ≤ 9*retention*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have copyLegal := splitListVertices_admissible_of_halfDegreeSplitCondition paths simple free halfSafe
  have legal := width_blocks_admissible_of_noShortReturnAcrossWidthCuts paths simple copyLegal returns
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple legal hn hp dense long upper lower

/-- At cutoff `k`, test short returns only across the actual factor-four
width cuts. In half mode use one of the sufficient degree-splitting conditions. -/
theorem regularization_list_frozen_of_noShortReturnAcrossWidthCuts {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (returns : NoShortReturnAcrossWidthCuts paths (4*(∑ i, (paths i).length)/p) k)
    (halfSafe : half = true → HalfDegreeSplitCondition paths (4*(∑ i, (paths i).length)/n) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_noShortReturnAcrossWidthCuts_of_mass paths simple free returns halfSafe
    hn hp dense long le_rfl (by omega)

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
  regularization_list_frozen_of_noShortReturnAcrossWidthCuts paths simple free hn hp dense long
    longCycles.noShortReturnAcrossWidthCuts (fun _ => Or.inl (longCycles.mono (by omega)))

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

/-- Rowwise deletions costing at most `M / 18` can be combined with the
local return condition at the original width to retain `M / 32`. -/
theorem regularization_list_frozen_after_width_cut_deletions {n p k : ℕ} {half : Bool}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (sub : ∀ i, (kept i).Sublist (paths i))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (returns : NoShortReturnAcrossWidthCuts kept (4*(∑ i, (paths i).length)/p) k)
    (halfSafe : half = true → HalfDegreeSplitCondition kept (4*(∑ i, (paths i).length)/n) k)
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  intro M
  have valid := localOrderAdmissible_of_sublist simple sub free
  refine frozen_cleaning_of_noShortReturnAcrossWidthCuts_of_mass kept (fun i => (sub i).nodup (simple i))
    valid returns halfSafe hn hp dense long (sum_le_sum (fun i _ => (sub i).length_le)) ?_
  change 17*M ≤ 18*(∑ i, (kept i).length) at retained
  omega

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
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_after_width_cut_deletions paths kept simple free sub hn hp dense long
    longCycles.noShortReturnAcrossWidthCuts (fun _ => Or.inl (longCycles.mono (by omega))) retained

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

/-- A cut before `boundary` in row `i` is safe if no short precedence
return crosses it. The bound on the return length is `cutoff - 3`. -/
def IsSafeShortReturnCut {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p)
    (cutoff boundary : ℕ) : Prop :=
  ∀ ⦃x y⦄, Before paths i x y → (paths i).idxOf x < boundary → boundary ≤ (paths i).idxOf y →
    y ∉ reachIn (pathPrecedenceGraph paths) x ((cutoff-2)-1)

private noncomputable def shortReturnCutsThrough (safe : ℕ → Prop)
    (index : ℕ) : Finset ℕ := by
  classical
  exact (range (index+1)).filter safe

private theorem mem_shortReturnCutsThrough {safe : ℕ → Prop}
    {index b : ℕ} :
    b ∈ shortReturnCutsThrough safe index ↔ b ≤ index ∧ safe b := by
  classical
  simp only [shortReturnCutsThrough,mem_filter,mem_range,Nat.lt_succ_iff]

/-- The last safe boundary up to a vertex in one row. The cut at zero
is always safe, even in an empty row. Equal ranks form contiguous runs. -/
noncomputable def shortReturnCutRank {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff : ℕ) (i : Fin p) (x : Fin n) : ℕ :=
  (shortReturnCutsThrough (IsSafeShortReturnCut paths i cutoff) ((paths i).idxOf x)).max'
    ⟨0,mem_shortReturnCutsThrough.mpr ⟨Nat.zero_le _,fun {_ _} _ h => (Nat.not_lt_zero _ h).elim⟩⟩

private theorem shortReturnCutRank_mem {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff : ℕ) (i : Fin p) (x : Fin n) :
    shortReturnCutRank paths cutoff i x ∈ shortReturnCutsThrough (IsSafeShortReturnCut paths i cutoff) ((paths i).idxOf x) :=
  max'_mem _ _

/-- Safe-cut ranks are nondecreasing along a row. -/
theorem shortReturnCutRank_mono {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cutoff : ℕ} {i : Fin p} {x y : Fin n} (before : Before paths i x y) :
    shortReturnCutRank paths cutoff i x ≤ shortReturnCutRank paths cutoff i y := by
  obtain ⟨index,safe⟩ := mem_shortReturnCutsThrough.mp (shortReturnCutRank_mem paths cutoff i x)
  exact le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨index.trans before.2.2.le,safe⟩)

/-- Two positions have strictly increasing ranks exactly when a safe cut lies
strictly after the first position and weakly before the second. -/
theorem shortReturnCutRank_lt_iff {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cutoff : ℕ} {i : Fin p} {x y : Fin n} :
    shortReturnCutRank paths cutoff i x < shortReturnCutRank paths cutoff i y ↔
    ∃ b, IsSafeShortReturnCut paths i cutoff b ∧ (paths i).idxOf x < b ∧ b ≤ (paths i).idxOf y := by
  constructor
  · intro increasing
    obtain ⟨index,safe⟩ := mem_shortReturnCutsThrough.mp (shortReturnCutRank_mem paths cutoff i y)
    refine ⟨shortReturnCutRank paths cutoff i y,safe,?_,index⟩
    by_contra! before
    exact increasing.not_ge (le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨before,safe⟩))
  · rintro ⟨b,safe,after,before⟩
    obtain ⟨rankIndex,_⟩ := mem_shortReturnCutsThrough.mp (shortReturnCutRank_mem paths cutoff i x)
    exact (rankIndex.trans_lt after).trans_le (le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨before,safe⟩))

/-- Certify a rank by exhibiting a safe cut and ruling out later cuts
through the given position. -/
theorem shortReturnCutRank_eq_of_cut {n p : ℕ} {paths : Fin p → List (Fin n)}
    {cutoff b : ℕ} {i : Fin p} {x : Fin n}
    (safe : IsSafeShortReturnCut paths i cutoff b) (before : b ≤ (paths i).idxOf x)
    (last : ∀ c, b < c → c ≤ (paths i).idxOf x → ¬ IsSafeShortReturnCut paths i cutoff c) :
    shortReturnCutRank paths cutoff i x = b := by
  apply le_antisymm
  · obtain ⟨index,allowed⟩ := mem_shortReturnCutsThrough.mp (shortReturnCutRank_mem paths cutoff i x)
    exact Nat.le_of_not_gt (fun later => last _ later index allowed)
  · exact le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨before,safe⟩)

/-- Number of occurrences in one run between successive safe cuts. -/
noncomputable def shortReturnRunLength {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff : ℕ) (i : Fin p) (rank : ℕ) : ℕ :=
  ((paths i).filter (fun x => decide (shortReturnCutRank paths cutoff i x = rank))).length

private theorem shortReturnRankAssemblyAdmissible {n p k D : ℕ} {half : Bool}
    (original paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (originalSimple : ∀ i, (original i).Nodup) (kept : ∀ i, (paths i).Sublist (original i))
    (legal : localOrderAdmissible half k (splitListVertices paths D)) :
    RankedRunAssemblyAdmissible paths D k half (shortReturnCutRank original k) := by
  classical
  intro sizes pieces sub apart
  let P := Σₗ i : Fin p, Fin (sizes i)
  let rows := splitListVertices paths D
  let G := pathPrecedenceGraph original
  let project := fun v : ListVertexBlockIndex paths D => v.fst
  let parent := fun i : P => i.fst
  have step {i x y} (before : Before pieces i x y) : Before rows (parent i) x y :=
    listBefore_of_sublist (paths := fun j : P => rows j.fst)
      (splitListVertices_simple paths D i.fst (simple i.fst)) (sub i) before
  have originalStep {i x y} (before : Before rows i x y) : Before original i (project x) (project y) :=
    listBefore_of_sublist (originalSimple i) (kept i) (splitListVertices_step (simple i) before)
  have projects {i x y} (before : Before rows i x y) : Edge G (project x) (project y) := by
    unfold G Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _,i,originalStep before⟩
  have directed {i x y} (hx : x ∈ rows i) (hy : y ∈ rows i)
      (ranked : shortReturnCutRank original k i (project x) < shortReturnCutRank original k i (project y)) :
      Before rows i x y ∧ project y ∉ reachIn G (project x) ((k-2)-1) := by
    have distinct : x ≠ y := fun e => ranked.ne (congrArg (shortReturnCutRank original k i ∘ project) e)
    rcases listBefore_total hx hy distinct with earlier | later
    · obtain ⟨b,safe,above,below⟩ := shortReturnCutRank_lt_iff.mp ranked
      exact ⟨earlier,safe (originalStep earlier) above below⟩
    · exact (ranked.not_ge (shortReturnCutRank_mono (originalStep later))).elim
  have separated : ShortReturnSeparated G project rows pieces parent (k-2) := by
    intro i j distinct parents
    rcases apart distinct parents with left | right
    · left
      intro x hx y hy
      exact directed ((sub i).subset hx) (parents.symm ▸ (sub j).subset hy) (left x hx y hy)
    · right
      intro y hy x hx
      exact directed (parents.symm ▸ (sub j).subset hy) ((sub i).subset hx) (right x hx y hy)
  have arrives : Monotone parent := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with earlier | ⟨same, _⟩
    · exact earlier.le
    · exact same.le
  cases half
  · exact bridgeFree_of_shortReturnSeparated_smaller_cutoff G project legal parent step projects separated
  · exact halfBridgeFree_of_shortReturnSeparated_smaller_cutoff G project legal parent arrives step projects separated

/-- The path split can choose where to cut. If each run of unsafe cuts
fits into the original width, safe boundaries can be packed to give all
four original-average caps and both original budgets. -/
theorem regularization_list_frozen_of_shortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (runs : ∀ i r, shortReturnRunLength paths k i r ≤ 4*(∑ i, (paths i).length)/p)
    (halfSafe : half = true → HalfDegreeSplitCondition paths (4*(∑ i, (paths i).length)/n) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 54*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_width_ranked_runs_of_mass paths simple hn hp dense long le_rfl
    (shortReturnCutRank paths k) (fun before => shortReturnCutRank_mono before) runs
    (shortReturnRankAssemblyAdmissible paths paths simple simple (fun _ => List.Sublist.refl _)
      (splitListVertices_admissible_of_halfDegreeSplitCondition paths simple free halfSafe))
    (by decide) (by norm_num)

/-- If each run fits into one original average path length, choosing
safe boundaries gives the original caps with retention `M / 16`. -/
theorem regularization_list_frozen_of_small_shortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (runs : ∀ i r, shortReturnRunLength paths k i r ≤ (∑ i, (paths i).length)/p)
    (halfSafe : half = true → HalfDegreeSplitCondition paths (4*(∑ i, (paths i).length)/n) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_small_ranked_runs paths simple hn hp dense long
    (shortReturnCutRank paths k) (fun before => shortReturnCutRank_mono before) runs
    (shortReturnRankAssemblyAdmissible paths paths simple simple (fun _ => List.Sublist.refl _)
      (splitListVertices_admissible_of_halfDegreeSplitCondition paths simple free halfSafe))

/-- Remove the occurrences in each original run longer than `width`. -/
noncomputable def pruneLongShortReturnRuns {n p : ℕ} (paths : Fin p → List (Fin n))
    (cutoff width : ℕ) (i : Fin p) : List (Fin n) :=
  (paths i).filter (fun x => decide (shortReturnRunLength paths cutoff i (shortReturnCutRank paths cutoff i x) ≤ width))

private theorem prunedShortReturnRuns_within_width {n p : ℕ}
    (paths : Fin p → List (Fin n)) (k width : ℕ) (i : Fin p) (r : ℕ) :
    ((pruneLongShortReturnRuns paths k width i).filter (fun x => decide (shortReturnCutRank paths k i x = r))).length ≤ width := by
  by_cases fits : shortReturnRunLength paths k i r ≤ width
  · exact ((List.filter_sublist (l := paths i)).filter _).length_le.trans fits
  · have empty : ((pruneLongShortReturnRuns paths k width i).filter
          (fun x => decide (shortReturnCutRank paths k i x = r))) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x on
      obtain ⟨kept,eq⟩ := List.mem_filter.mp on
      have short := of_decide_eq_true (List.mem_filter.mp kept).2
      rw [of_decide_eq_true eq] at short
      exact fits short
    simp [empty]

/-- Long runs may be pruned first if they contain at most one fifty-sixth
of the original incidence mass. The widths, retained ranks and all four
caps use the original rows and budgets. -/
theorem regularization_list_frozen_of_few_long_shortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (halfSafe : half = true → let M := ∑ i, (paths i).length
      HalfDegreeSplitCondition (pruneLongShortReturnRuns paths k (4*M/p)) (4*M/n) k)
    (mostly : let M := ∑ i, (paths i).length
      55*M ≤ 56*∑ i, (pruneLongShortReturnRuns paths k (4*M/p) i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 108*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let kept := pruneLongShortReturnRuns paths k (4*M/p)
  have subset (i : Fin p) : (kept i).Sublist (paths i) := List.filter_sublist
  have simpleKept (i : Fin p) := (subset i).nodup (simple i)
  have mass : (∑ i, (kept i).length) ≤ M := sum_le_sum fun i _ => (subset i).length_le
  have freeKept : localOrderAdmissible half k kept :=
    localOrderAdmissible_of_sublist simple subset free
  exact frozen_cleaning_of_width_ranked_runs_of_mass kept simpleKept hn hp dense long mass
    (shortReturnCutRank paths k) (fun before => shortReturnCutRank_mono
      (listBefore_of_sublist (simple _) (subset _) before))
    (prunedShortReturnRuns_within_width paths k (4*M/p))
    (shortReturnRankAssemblyAdmissible paths kept simpleKept simple subset
      (splitListVertices_admissible_of_halfDegreeSplitCondition kept simpleKept freeKept halfSafe))
    (by decide) (by dsimp only [kept,M]; dsimp only at mostly; omega)

/-- In full mode the degree split always preserves bridge exclusion. The absence
of short returns in the original precedence graph then permits the path cuts. -/
theorem listRegularizedPaths_fullFree_of_noShortPrecedenceCycle {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (longCycles : NoShortPrecedenceCycle paths (k-2)) (D L : ℕ) :
    BridgeFree (Before (listRegularizedPaths paths D L)) k :=
  width_blocks_admissible_of_noShortReturnAcrossWidthCuts (half := false) paths simple
    (free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i)))
    longCycles.noShortReturnAcrossWidthCuts

/-- The half-bridge cleaning only needs to rule out short walks between
different copies of the same vertex, alongside the width-cut condition. -/
theorem regularization_list_frozen_half_of_noShortSplitReturn {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (degreeSafe : NoShortSplitReturn (splitListVertices paths (4*(∑ i, (paths i).length)/n))
      (·.fst) (k-3))
    (returns : NoShortReturnAcrossWidthCuts paths (4*(∑ i, (paths i).length)/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have copyLegal := free.split_list_vertices_of_noShortSplitReturn _
    (fun {i _ _} => splitListVertices_step (simple i)) degreeSafe
  have legal := width_blocks_admissible_of_noShortReturnAcrossWidthCuts (half := true)
    paths simple copyLegal returns
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple legal hn hp dense long le_rfl (by omega)


/-- Precedence edges that actually occur in the listed pieces. -/
def listPiecePrecedenceGraph {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (pieces : I → List V) : Arcs V := by
  letI (x y : V) : DecidablePred (fun i => Before pieces i x y) := fun i => by
    unfold SourceAudit.BeforeIn
    infer_instance
  exact univ.filter fun e => ∃ i, Before pieces i e.1 e.2

theorem listPiecePrecedenceGraph_edge {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {pieces : I → List V} {x y : V} :
    Edge (listPiecePrecedenceGraph pieces) x y ↔ ∃ i, Before pieces i x y := by
  simp only [Edge,listPiecePrecedenceGraph,mem_filter,mem_univ,true_and]

/-- Search for a return across the width cut on the actual copied path
pieces. Edges lost in either split do not participate in this search. -/
def NoShortReturnAcrossCopiedWidthCuts {n p : ℕ} (paths : Fin p → List (Fin n))
    (D L cutoff : ℕ) : Prop :=
  let copies := splitListVertices paths D
  let graph := listPiecePrecedenceGraph (listRegularizedPaths paths D L)
  ∀ ⦃i x y⦄, Before copies i x y → (copies i).idxOf x/L ≠ (copies i).idxOf y/L →
    y ∉ reachIn graph x ((cutoff-2)-1)

private theorem project_reachIn {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : Arcs V} {H : Arcs W} (project : V → W)
    (edges : ∀ {x y}, Edge G x y → Edge H (project x) (project y)) {t : V} (radius : ℕ) :
    ∀ {s : V}, s ∈ reachIn G t radius → project s ∈ reachIn H (project t) radius := by
  induction radius with
  | zero =>
    intro s member
    have equal : s = t := mem_singleton.mp member
    exact mem_singleton.mpr (congrArg project equal)
  | succ radius earlier =>
    intro s member
    rcases reachIn_succ.mp member with reach | ⟨v,step,reach⟩
    · exact reachIn_succ.mpr (Or.inl (earlier reach))
    · exact reachIn_succ.mpr (Or.inr ⟨project v,edges step,earlier reach⟩)

/-- A width-cut certificate on the original graph also certifies the
actual copied piece graph. -/
theorem NoShortReturnAcrossWidthCuts.copied {n p D L k : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : NoShortReturnAcrossWidthCuts paths L k) :
    NoShortReturnAcrossCopiedWidthCuts paths D L k := by
  classical
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  let project (v : ListVertexBlockIndex paths D) := v.fst
  have lifted {x y} (edge : Edge (listPiecePrecedenceGraph pieces) x y) :
      Edge (pathPrecedenceGraph paths) (project x) (project y) := by
    obtain ⟨i,onPiece⟩ := listPiecePrecedenceGraph_edge.mp edge
    have onCopy : Before copies i.fst x y :=
      listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
        (splitListVertices_simple paths D i.fst (simple i.fst)) List.filter_sublist onPiece
    unfold Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _,i.fst,splitListVertices_step (simple i.fst) onCopy⟩
  intro i x y step different back
  have oldStep := splitListVertices_step (simple i) step
  have cut : (paths i).idxOf (project x)/L ≠ (paths i).idxOf (project y)/L := by
    rwa [splitListVertices_idxOf_project paths D i (simple i) step.1,
      splitListVertices_idxOf_project paths D i (simple i) step.2.1]
  exact free oldStep cut (project_reachIn project (fun {_ _} => lifted) _ back)

/-- Search for a short return using the pieces of these rows at the
given width. The rows can already have been restricted. -/
def NoShortReturnAcrossWidthCutsInPieces {p : ℕ} {V : Type*} [LinearOrder V] [Fintype V]
    (rows : Fin p → List V) (width cutoff : ℕ) : Prop :=
  let graph := listPiecePrecedenceGraph (splitListPaths rows width)
  ∀ ⦃i x y⦄, Before rows i x y → (rows i).idxOf x/width ≠ (rows i).idxOf y/width →
    y ∉ reachIn graph x ((cutoff-2)-1)

/-- Contiguous pieces preserve the requested exclusion when the relevant
short returns are absent from those pieces. -/
theorem splitListPaths_admissible_of_noShortReturnAcrossWidthCutsInPieces
    {p k L : ℕ} {V : Type*} [LinearOrder V] [Fintype V] {half : Bool}
    (rows : Fin p → List V) (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows) (noReturns : NoShortReturnAcrossWidthCutsInPieces rows L k) :
    localOrderAdmissible half k (splitListPaths rows L) := by
  let copies := rows
  let pieces := splitListPaths rows L
  let J := ListBlockIndex copies L
  let parent (j : J) := j.fst
  let G := listPiecePrecedenceGraph pieces
  have steps {i x y} (step : Before pieces i x y) : Before copies (parent i) x y :=
    listBefore_of_sublist (paths := fun j : J => copies (parent j))
      (simple i.fst) List.filter_sublist step
  have blockDistinct {i j : J} (different : i ≠ j) (same : parent i = parent j)
      {x y} (hx : x ∈ pieces i) (hy : y ∈ pieces j) :
      (copies (parent i)).idxOf x/L ≠ (copies (parent i)).idxOf y/L := by
    rcases i with ⟨a,u⟩
    rcases j with ⟨b,v⟩
    change a = b at same
    subst b
    have hxBlock := (mem_localPathBlock.mp hx).2
    have hyBlock := (mem_localPathBlock.mp hy).2
    intro equal
    exact different (congrArg (Sigma.mk a) (Fin.ext (hxBlock.symm.trans (equal.trans hyBlock))))
  have separated : ShortReturnSeparated G id copies pieces parent (k-2) := by
    intro i j different same
    rcases contiguousBlocks_separated different same with forward | backward
    · left
      intro x hx y hy
      have step := forward hx hy
      exact ⟨step,noReturns step (blockDistinct different same hx hy)⟩
    · right
      intro y hy x hx
      have step := backward hx hy
      exact ⟨step,noReturns step (blockDistinct different same hx hy).symm⟩
  have edges {i x y} (step : Before pieces i x y) : Edge G x y :=
    listPiecePrecedenceGraph_edge.mpr ⟨i,step⟩
  have project {d : ℕ} (b : Bridge (Before pieces) d) (small : d+2 ≤ k) :=
    bridge_of_shortReturnSeparated_split G id parent (fun {_ _ _} => steps)
      (fun {_ _ _} => edges) separated b small
  cases half
  · intro d small
    refine ⟨fun b => ?_⟩
    obtain ⟨j,bound,old,_,_⟩ := project b small
    exact (legal (k := j) (by omega)).false old
  · intro d small b earlier
    have arrives : Monotone parent := block_parent_mono (fun i => (copies i).toFinset) L
    obtain ⟨j,bound,old,river,last⟩ := project b small
    have noLater := arrives earlier.le
    rw [← river,← last] at noLater
    exact legal (k := j) (by omega) old (noLater.lt_of_ne (old.river_ne_arc _).symm)

/-- Only the strict comparisons available on actual path pieces can
witness a backwards return that prevents a bridge projection. -/
theorem listRegularizedPaths_admissible_of_noShortReturnAcrossCopiedWidthCuts
    {n p k D L : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : localOrderAdmissible half k (splitListVertices paths D))
    (noReturns : NoShortReturnAcrossCopiedWidthCuts paths D L k) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) :=
  splitListPaths_admissible_of_noShortReturnAcrossWidthCutsInPieces (splitListVertices paths D)
    (fun i => splitListVertices_simple paths D i (simple i)) legal noReturns

/-- Original-average cleaning after testing returns in the actual
piece graph. In half mode the degree split still needs a certificate. -/
theorem regularization_list_frozen_of_noShortReturnAcrossCopiedWidthCuts {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (returns : let M := ∑ i, (paths i).length
      NoShortReturnAcrossCopiedWidthCuts paths (4*M/n) (4*M/p) k)
    (halfSafe : let D := 4*(∑ i, (paths i).length)/n
      half = true → HalfDegreeSplitCondition paths D k ∨
        NoShortSplitReturn (splitListVertices paths D) (·.fst) (k-3)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*(∑ i, (paths i).length)/n
  have copied : localOrderAdmissible half k (splitListVertices paths D) := by
    cases half
    · exact free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
    · rcases halfSafe rfl with old | refined
      · exact splitListVertices_admissible_of_halfDegreeSplitCondition paths simple free (fun _ => old)
      · exact free.split_list_vertices_of_noShortSplitReturn (·.fst)
          (fun {i _ _} => splitListVertices_step (simple i)) refined
  have legal := listRegularizedPaths_admissible_of_noShortReturnAcrossCopiedWidthCuts paths simple copied returns
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple legal hn hp dense long le_rfl (by omega)


/-- Determine safe path boundaries in the copied rows before splitting any
of them. The graph keeps the degree-copy label at every vertex of a return. -/
def IsSafeCopiedReturnCut {n p : ℕ} (paths : Fin p → List (Fin n))
    (D : ℕ) (i : Fin p) (cutoff boundary : ℕ) : Prop :=
  let copies := splitListVertices paths D
  let graph := listPiecePrecedenceGraph copies
  ∀ ⦃x y⦄, Before copies i x y →
    (copies i).idxOf x < boundary → boundary ≤ (copies i).idxOf y →
    y ∉ reachIn graph x ((cutoff-2)-1)

/-- Index a run by the last safe boundary through its position. -/
noncomputable def copiedReturnCutRank {n p : ℕ} (paths : Fin p → List (Fin n))
    (D cutoff : ℕ) (i : Fin p) (x : Fin n) : ℕ :=
  (shortReturnCutsThrough (IsSafeCopiedReturnCut paths D i cutoff) ((paths i).idxOf x)).max'
    ⟨0,mem_shortReturnCutsThrough.mpr ⟨Nat.zero_le _,fun {_ _} _ h => (Nat.not_lt_zero _ h).elim⟩⟩

private theorem copiedReturnCutRank_mem {n p : ℕ} (paths : Fin p → List (Fin n)) (D cutoff : ℕ)
    (i : Fin p) (x : Fin n) :
    copiedReturnCutRank paths D cutoff i x ∈
      shortReturnCutsThrough (IsSafeCopiedReturnCut paths D i cutoff) ((paths i).idxOf x) :=
  max'_mem _ _

theorem copiedReturnCutRank_mono {n p D cutoff : ℕ} {paths : Fin p → List (Fin n)}
    {i : Fin p} {x y : Fin n} (before : Before paths i x y) :
    copiedReturnCutRank paths D cutoff i x ≤ copiedReturnCutRank paths D cutoff i y := by
  obtain ⟨index,safe⟩ := mem_shortReturnCutsThrough.mp (copiedReturnCutRank_mem paths D cutoff i x)
  exact le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨index.trans before.2.2.le,safe⟩)

theorem copiedReturnCutRank_lt_iff {n p D cutoff : ℕ} {paths : Fin p → List (Fin n)}
    {i : Fin p} {x y : Fin n} :
    copiedReturnCutRank paths D cutoff i x < copiedReturnCutRank paths D cutoff i y ↔
    ∃ b, IsSafeCopiedReturnCut paths D i cutoff b ∧ (paths i).idxOf x < b ∧ b ≤ (paths i).idxOf y := by
  constructor
  · intro increasing
    obtain ⟨index,safe⟩ := mem_shortReturnCutsThrough.mp (copiedReturnCutRank_mem paths D cutoff i y)
    refine ⟨copiedReturnCutRank paths D cutoff i y,safe,?_,index⟩
    by_contra! before
    exact increasing.not_ge (le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨before,safe⟩))
  · rintro ⟨b,safe,after,before⟩
    obtain ⟨rankIndex,_⟩ := mem_shortReturnCutsThrough.mp (copiedReturnCutRank_mem paths D cutoff i x)
    exact (rankIndex.trans_lt after).trans_le (le_max' _ _ (mem_shortReturnCutsThrough.mpr ⟨before,safe⟩))

/-- The length of one run when safe boundaries are tested on the degree
copies. Lengths count the same incidences as the original rows. -/
noncomputable def copiedShortReturnRunLength {n p : ℕ} (paths : Fin p → List (Fin n))
    (D cutoff : ℕ) (i : Fin p) (rank : ℕ) : ℕ :=
  ((paths i).filter (fun x => decide (copiedReturnCutRank paths D cutoff i x = rank))).length

set_option maxHeartbeats 800000 in
private theorem copiedReturnRankAssemblyAdmissible {n p k D : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (legal : localOrderAdmissible half k (splitListVertices paths D)) :
    RankedRunAssemblyAdmissible paths D k half (copiedReturnCutRank paths D k) := by
  intro sizes pieces sub apart
  let P := Σₗ i : Fin p, Fin (sizes i)
  let rows := splitListVertices paths D
  let G := listPiecePrecedenceGraph rows
  let parent (i : P) := i.fst
  have step {i x y} (before : Before pieces i x y) : Before rows (parent i) x y :=
    listBefore_of_sublist (paths := fun j : P => rows j.fst)
      (splitListVertices_simple paths D i.fst (simple i.fst)) (sub i) before
  have edge {i x y} (before : Before rows i x y) : Edge G x y :=
    listPiecePrecedenceGraph_edge.mpr ⟨i,before⟩
  have directed {i x y} (hx : x ∈ rows i) (hy : y ∈ rows i)
      (ranked : copiedReturnCutRank paths D k i x.fst < copiedReturnCutRank paths D k i y.fst) :
      Before rows i x y ∧ y ∉ reachIn G x ((k-2)-1) := by
    have different : x ≠ y := by
      intro eq
      exact ranked.ne (congrArg (fun v : ListVertexBlockIndex paths D => copiedReturnCutRank paths D k i v.fst) eq)
    rcases listBefore_total hx hy different with before | reverse
    · obtain ⟨b,cut,low,high⟩ := copiedReturnCutRank_lt_iff.mp ranked
      rw [splitListVertices_idxOf_project paths D i (simple i) hx] at low
      rw [splitListVertices_idxOf_project paths D i (simple i) hy] at high
      exact ⟨before,cut before low high⟩
    · exact (ranked.not_ge (copiedReturnCutRank_mono (splitListVertices_step (simple i) reverse))).elim
  have separated : ShortReturnSeparated G id rows pieces parent (k-2) := by
    intro i j different parents
    rcases apart different parents with left | right
    · left
      intro x hx y hy
      exact directed ((sub i).subset hx) (parents.symm ▸ (sub j).subset hy) (left x hx y hy)
    · right
      intro y hy x hx
      exact directed (parents.symm ▸ (sub j).subset hy) ((sub i).subset hx) (right x hx y hy)
  have arrives : Monotone parent := by
    intro i j h
    rcases Sigma.Lex.le_def.mp h with earlier | ⟨same,_⟩
    · exact earlier.le
    · exact same.le
  cases half
  · exact bridgeFree_of_shortReturnSeparated_smaller_cutoff G id legal parent step edge separated
  · exact halfBridgeFree_of_shortReturnSeparated_smaller_cutoff G id legal parent arrives step edge separated

/-- Pack complete runs between boundaries that are safe on the degree
copies. Runs fitting the factor-four cap give the frozen conclusion. -/
theorem regularization_list_frozen_of_copiedShortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (runs : let M := ∑ i, (paths i).length; ∀ i r, copiedShortReturnRunLength paths (4*M/n) k i r ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 54*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_width_ranked_runs_of_mass paths simple hn hp dense long le_rfl
    (copiedReturnCutRank paths (4*(∑ i, (paths i).length)/n) k) (fun before => copiedReturnCutRank_mono before) runs
    (copiedReturnRankAssemblyAdmissible paths simple copyLegal) (by decide) (by norm_num)

/-- When each run fits one original mean path length, safe boundaries on
the copied rows give the frozen conclusion with mass at least M/16. -/
theorem regularization_list_frozen_of_small_copiedShortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (runs : let M := ∑ i, (paths i).length; ∀ i r, copiedShortReturnRunLength paths (4*M/n) k i r ≤ M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_cleaning_of_small_ranked_runs paths simple hn hp dense long
    (copiedReturnCutRank paths (4*(∑ i, (paths i).length)/n) k) (fun before => copiedReturnCutRank_mono before) runs
    (copiedReturnRankAssemblyAdmissible paths simple copyLegal)


/-- Remove long runs without rebuilding the degree copies or changing
which boundaries are safe. -/
noncomputable def pruneLongCopiedReturnRuns {n p : ℕ} (paths : Fin p → List (Fin n))
    (D cutoff width : ℕ) (i : Fin p) : List (ListVertexBlockIndex paths D) :=
  (splitListVertices paths D i).filter fun v =>
    decide (copiedShortReturnRunLength paths D cutoff i (copiedReturnCutRank paths D cutoff i v.fst) ≤ width)


private theorem copiedShortReturnRunLength_eq_raw {n p D k : ℕ} (paths : Fin p → List (Fin n))
    (i : Fin p) (r : ℕ) :
    ((splitListVertices paths D i).filter (fun v => decide (copiedReturnCutRank paths D k i v.fst = r))).length =
      copiedShortReturnRunLength paths D k i r := by
  have projected := congrArg (fun l : List (Fin n) =>
    (l.filter (fun v => decide (copiedReturnCutRank paths D k i v = r))).length)
    (splitListVertices_project paths D i)
  rwa [List.filter_map,List.length_map] at projected

set_option maxHeartbeats 1500000 in
private theorem frozen_cleaning_after_restricting_fixed_copied_runs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (kept : let M := ∑ i, (paths i).length; Fin p → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length; ∀ i, (kept i).Sublist (splitListVertices paths (4*M/n) i))
    (fibreCap : let M := ∑ i, (paths i).length
      ∀ i r, ((kept i).filter (fun v => decide (copiedReturnCutRank paths (4*M/n) k i v.fst = r))).length ≤ 4*M/p)
    (keep : let M := ∑ i, (paths i).length; 55*M ≤ 56*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 108*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let V := ListVertexBlockIndex paths D
  let raw := splitListVertices paths D
  let rank (i : Fin p) (v : V) := copiedReturnCutRank paths D k i v.fst
  by_cases substantial : 2*n ≤ M
  · have stillSimple (i : Fin p) : (kept i).Nodup :=
      (sub i).nodup (splitListVertices_simple paths D i (simple i))
    have rowsOrder (i : Fin p) : (kept i).Pairwise (fun x y => rank i x ≤ rank i y) :=
      (splitListVertices_rank_order D i (simple i) (copiedReturnCutRank paths D k i)
        (fun {_ _} => copiedReturnCutRank_mono)).sublist (sub i)
    have mass : (∑ i, (kept i).length) ≤ M := by
      calc
        _ ≤ ∑ i, (raw i).length := sum_le_sum (fun i _ => (sub i).length_le)
        _ = M := sum_congr rfl (fun i _ => splitListVertices_length paths D i)
    have legal : RankedCopiedAssemblyAdmissible kept k half rank := by
      intro sizes pieces subPieces apart
      exact copiedReturnRankAssemblyAdmissible paths simple copyLegal pieces
        (fun i => (subPieces i).trans (sub i.fst)) apart
    have dPos : 0 < D := (four_average_width hn dense).1
    obtain ⟨vertexBudget,pathRoom⟩ := frozen_width_copy_budget hn hp dense substantial
    have rawCount := (regularization_list_counts paths simple (D := D) dPos Nat.one_pos).1
    rw [Fintype.card_fin] at rawCount
    have vRoom : 7*Fintype.card V ≤ 9*n := (Nat.mul_le_mul_left 7 rawCount).trans vertexBudget
    have degree (v : V) : (occurrences (fun i => (kept i).toFinset) v).card ≤ D := by
      have rawDegree : (occurrences (fun i => (raw i).toFinset) v).card ≤ D := by
        simpa only [raw,splitListVertices_toFinset] using
          (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
      apply le_trans (card_le_card ?_) rawDegree
      intro i member
      have present := List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (kept j).toFinset)).mp member)
      exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset present))
    refine frozen_cleaning_after_ranked_copied_rows kept stillSimple mass hn hp dense long L le_rfl
      rank rowsOrder fibreCap legal (vNum := 7) (vDen := 9) (pNum := 2) (pDen := 3)
      (by decide) (by decide) (by decide) (by decide) vRoom degree ?_ ?_
    · dsimp only
      intro q _ pairs
      exact pathRoom q pairs
    · change 55*M ≤ 56*(∑ i, (kept i).length) at keep
      omega
  · have sparse : M ≤ 3*max n p := by have bound := le_max_left n p; omega
    obtain ⟨v,vRoom,q,pRoom,clean,cleanSimple,free,mass,bound,caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long sparse
    have allowed : localOrderAdmissible half k clean := by
      cases half
      · exact free
      · exact free.halfFree
    exact ⟨v,vRoom,q,pRoom,clean,cleanSimple,allowed,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),bound,caps⟩


set_option maxHeartbeats 1500000 in
/-- If long runs use at most one fifty-sixth of the original mass, remove
them from the fixed copies and pack the remaining runs. -/
theorem regularization_list_frozen_of_few_long_copiedShortReturnRuns {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (keep : let M := ∑ i, (paths i).length
      55*M ≤ 56*(∑ i, (pruneLongCopiedReturnRuns paths (4*M/n) k (4*M/p) i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 108*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let V := ListVertexBlockIndex paths D
  let raw := splitListVertices paths D
  let kept := pruneLongCopiedReturnRuns paths D k L
  let rank (i : Fin p) (v : V) := copiedReturnCutRank paths D k i v.fst
  have sub (i : Fin p) : (kept i).Sublist (raw i) := List.filter_sublist
  refine frozen_cleaning_after_restricting_fixed_copied_runs paths simple hn hp dense long copyLegal kept sub ?_ keep
  dsimp only
  intro i r
  change ((kept i).filter (fun v => decide (rank i v = r))).length ≤ L
  by_cases fits : copiedShortReturnRunLength paths D k i r ≤ L
  · exact (((sub i).filter _).length_le.trans_eq (copiedShortReturnRunLength_eq_raw paths i r)).trans fits
  · have empty : ((kept i).filter (fun v => decide (rank i v = r))) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro v present
      obtain ⟨onRow,onRun⟩ := List.mem_filter.mp present
      have h : copiedShortReturnRunLength paths D k i (rank i v) ≤ L :=
        of_decide_eq_true (List.mem_filter.mp onRow).2
      rw [of_decide_eq_true onRun] at h
      exact fits h
    simp [empty]


private theorem filter_idxOf_lt_eq_take {V : Type*} [DecidableEq V] (row : List V)
    (simple : row.Nodup) (width : ℕ) :
    row.filter (fun v => decide (row.idxOf v < width)) = row.take width := by
  induction row generalizing width with
  | nil => simp
  | cons first tail inductionHypothesis =>
    obtain ⟨absent,tailSimple⟩ := List.nodup_cons.mp simple
    cases width with
    | zero => simp
    | succ width =>
      have filtered : tail.filter (fun v => decide ((first :: tail).idxOf v < width+1)) =
          tail.filter (fun v => decide (tail.idxOf v < width)) := by
        apply List.filter_congr
        intro v on
        have neq : first ≠ v := fun eq => absent (eq.symm ▸ on)
        rw [List.idxOf_cons_ne _ neq]
        simp only [Nat.succ_lt_succ_iff]
      simp only [List.filter_cons,List.idxOf_cons_self,Nat.zero_lt_succ,decide_true,ite_true,List.take_succ_cons]
      rw [filtered,inductionHypothesis tailSimple]

/-- Cap each run at the width while keeping its earliest copied
incidences, original degree-copy labels, and run ranks. -/
noncomputable def takeCopiedReturnRunPrefixes {n p : ℕ} (paths : Fin p → List (Fin n))
    (D cutoff width : ℕ) (i : Fin p) : List (ListVertexBlockIndex paths D) :=
  let row := splitListVertices paths D i
  let rank (v : ListVertexBlockIndex paths D) := copiedReturnCutRank paths D cutoff i v.fst
  row.filter fun v => decide ((row.filter (fun w => decide (rank w = rank v))).idxOf v < width)

/-- A clipped run keeps exactly its original length capped at the width. -/
theorem takeCopiedReturnRunPrefixes_run_length {n p D k : ℕ} (paths : Fin p → List (Fin n))
    {i : Fin p} (simple : (paths i).Nodup) (width r : ℕ) :
    ((takeCopiedReturnRunPrefixes paths D k width i).filter
      (fun v => decide (copiedReturnCutRank paths D k i v.fst = r))).length =
      min width (copiedShortReturnRunLength paths D k i r) := by
  let row := splitListVertices paths D i
  let rank (v : ListVertexBlockIndex paths D) := copiedReturnCutRank paths D k i v.fst
  let marked (r : ℕ) := row.filter (fun v => decide (rank v = r))
  have onlyRun : ((takeCopiedReturnRunPrefixes paths D k width i).filter (fun v => decide (rank v = r))) =
      (marked r).filter (fun v => decide ((marked r).idxOf v < width)) := by
    change (row.filter (fun v => decide ((marked (rank v)).idxOf v < width))).filter _ =
      (row.filter (fun v => decide (rank v = r))).filter _
    simp only [List.filter_filter]
    apply List.filter_congr
    intro v _
    by_cases same : rank v = r <;> simp [same]
  have runSimple : (marked r).Nodup := List.filter_sublist.nodup (splitListVertices_simple paths D i simple)
  calc
    _ = ((marked r).filter (fun v => decide ((marked r).idxOf v < width))).length :=
      congrArg List.length onlyRun
    _ = ((marked r).take width).length :=
      congrArg List.length (filter_idxOf_lt_eq_take (marked r) runSimple width)
    _ = _ := List.length_take.trans (congrArg (min width) (copiedShortReturnRunLength_eq_raw paths i r))

/-- Clip runs above the original path width with the copies fixed.
The mass condition pays for the clipped excess in the long runs. -/
theorem regularization_list_frozen_of_copiedReturnRunPrefixes {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (keep : let M := ∑ i, (paths i).length
      55*M ≤ 56*(∑ i, (takeCopiedReturnRunPrefixes paths (4*M/n) k (4*M/p) i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 108*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let kept := takeCopiedReturnRunPrefixes paths D k L
  refine frozen_cleaning_after_restricting_fixed_copied_runs paths simple hn hp dense long copyLegal kept
    (fun _ => List.filter_sublist) ?_ keep
  dsimp only
  intro i r
  exact (takeCopiedReturnRunPrefixes_run_length paths (D := D) (k := k) (simple i) L r).trans_le
    (min_le_left _ _)


private theorem list_length_eq_sum_rank_lengths {V : Type*} [DecidableEq V]
    (row : List V) (simple : row.Nodup) (rank : V → ℕ) (ranks : Finset ℕ)
    (rankIn : ∀ v ∈ row, rank v ∈ ranks) :
    row.length = ∑ r ∈ ranks, (row.filter (fun v => decide (rank v = r))).length := by
  calc
    _ = row.toFinset.card := (List.toFinset_card_of_nodup simple).symm
    _ = ∑ r ∈ ranks, (row.toFinset.filter (fun v => rank v = r)).card :=
      card_eq_sum_card_fiberwise (fun v hv => rankIn v (List.mem_toFinset.mp hv))
    _ = _ := by
      apply sum_congr rfl
      intro r _
      have counted := List.toFinset_card_of_nodup
        ((List.filter_sublist (p := fun v => decide (rank v = r))).nodup simple)
      rw [List.toFinset_filter] at counted
      simpa using counted

private noncomputable def occupiedCopiedReturnRunRanks {n p : ℕ} (paths : Fin p → List (Fin n))
    (D cutoff : ℕ) (i : Fin p) : Finset ℕ :=
  ((splitListVertices paths D i).map (fun v => copiedReturnCutRank paths D cutoff i v.fst)).toFinset

/-- The sum of the excesses above the width over all occupied copied runs. -/
noncomputable def copiedReturnRunExcess {n p : ℕ} (paths : Fin p → List (Fin n)) (D cutoff width : ℕ) : ℕ :=
  ∑ i : Fin p, ∑ r ∈ occupiedCopiedReturnRunRanks paths D cutoff i,
    (copiedShortReturnRunLength paths D cutoff i r-width)

/-- The clipped incidences and the discarded excess account for the whole
starting mass, including empty rows and runs shorter than the width. -/
theorem takeCopiedReturnRunPrefixes_mass_add_excess {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (D cutoff width : ℕ) :
    (∑ i, (takeCopiedReturnRunPrefixes paths D cutoff width i).length)+copiedReturnRunExcess paths D cutoff width =
      ∑ i, (paths i).length := by
  let raw := splitListVertices paths D
  let kept := takeCopiedReturnRunPrefixes paths D cutoff width
  let rank (i : Fin p) (v : ListVertexBlockIndex paths D) := copiedReturnCutRank paths D cutoff i v.fst
  let ranks := occupiedCopiedReturnRunRanks paths D cutoff
  let run (i : Fin p) (r : ℕ) := copiedShortReturnRunLength paths D cutoff i r
  have rawSimple (i : Fin p) : (raw i).Nodup := splitListVertices_simple paths D i (simple i)
  have subset (i : Fin p) : (kept i).Sublist (raw i) := List.filter_sublist
  have byRow (i : Fin p) : (kept i).length+(∑ r ∈ ranks i, (run i r-width)) = (paths i).length := by
    have rankIn {v : ListVertexBlockIndex paths D} (inside : v ∈ raw i) : rank i v ∈ ranks i :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨v,inside,rfl⟩)
    have keptCount : (kept i).length = ∑ r ∈ ranks i, min width (run i r) := calc
      _ = ∑ r ∈ ranks i, ((kept i).filter (fun v => decide (rank i v = r))).length :=
        list_length_eq_sum_rank_lengths (kept i) ((subset i).nodup (rawSimple i))
          (rank i) (ranks i) (fun _ h => rankIn ((subset i).subset h))
      _ = _ := sum_congr rfl (fun r _ => takeCopiedReturnRunPrefixes_run_length paths (simple i) width r)
    have rawCount : (raw i).length = ∑ r ∈ ranks i, run i r := calc
      _ = ∑ r ∈ ranks i, ((raw i).filter (fun v => decide (rank i v = r))).length :=
        list_length_eq_sum_rank_lengths (raw i) (rawSimple i) (rank i) (ranks i) (fun _ h => rankIn h)
      _ = _ := sum_congr rfl (fun r _ => copiedShortReturnRunLength_eq_raw paths i r)
    rw [keptCount,← sum_add_distrib,← splitListVertices_length paths D i,rawCount]
    apply sum_congr rfl
    intro r _
    omega
  have split :
      (∑ i : Fin p, ((kept i).length+(∑ r ∈ ranks i, (run i r-width)))) =
        (∑ i, (kept i).length)+(∑ i, ∑ r ∈ ranks i, (run i r-width)) :=
    sum_add_distrib
  have excessEq : copiedReturnRunExcess paths D cutoff width =
      ∑ i : Fin p, ∑ r ∈ ranks i, (run i r-width) := rfl
  rw [excessEq]
  exact split.symm.trans (sum_congr rfl (fun i _ => byRow i))

/-- If the total excess beyond the original width is at most one
fifty-sixth of the mass, clip it on the fixed degree copies. -/
theorem regularization_list_frozen_of_small_copiedReturnRun_excess {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (excess : let M := ∑ i, (paths i).length; 56*copiedReturnRunExcess paths (4*M/n) k (4*M/p) ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 108*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_of_copiedReturnRunPrefixes paths simple hn hp dense long copyLegal ?_
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  change 56*copiedReturnRunExcess paths D k L ≤ M at excess
  change 55*M ≤ 56*(∑ i, (takeCopiedReturnRunPrefixes paths D k L i).length)
  have exactMass := takeCopiedReturnRunPrefixes_mass_add_excess paths simple D k L
  change _ = M at exactMass
  omega

set_option maxHeartbeats 1200000 in
/-- The degree-side exclusion may be established on the retained
copied rows. The original degree labels and both original widths
are fixed. -/
theorem regularization_list_frozen_of_admissible_copied_row_deletions {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (kept : let M := ∑ i, (paths i).length; Fin p → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length; ∀ i, (kept i).Sublist (splitListVertices paths (4*M/n) i))
    (keptLegal : localOrderAdmissible half k kept)
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length))
    (returns : let M := ∑ i, (paths i).length; NoShortReturnAcrossWidthCutsInPieces kept (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let K := ∑ i, (kept i).length
  let D := 4*M/n
  let L := 4*M/p
  let V := ListVertexBlockIndex paths D
  let copied := splitListVertices paths D
  let pieces := splitListPaths kept L
  have copiedSimple (i : Fin p) : (copied i).Nodup := splitListVertices_simple paths D i (simple i)
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (copiedSimple i)
  have piecesSimple (i : ListBlockIndex kept L) : (pieces i).Nodup :=
    List.filter_sublist.nodup (keptSimple i.fst)
  have legal : localOrderAdmissible half k pieces :=
    splitListPaths_admissible_of_noShortReturnAcrossWidthCutsInPieces kept keptSimple keptLegal returns
  have upper : K ≤ M := calc
    _ ≤ ∑ i, (copied i).length := sum_le_sum (fun i _ => (sub i).length_le)
    _ = M := sum_congr rfl (fun i _ => splitListVertices_length paths D i)
  have exactMass : (∑ i, (pieces i).length) = K := splitListPaths_size kept keptSimple L
  obtain ⟨dPos,dRoom,_⟩ := four_average_width hn dense
  obtain ⟨lPos,lRoom,_⟩ := four_average_width hp long
  have countV : Fintype.card V ≤ n+M/D := by
    simpa only [Fintype.card_fin] using (regularization_list_counts paths simple (D := D) dPos lPos).1
  have countP : Fintype.card (ListBlockIndex kept L) ≤ p+K/L := by
    have count := blockIndex_card_precise (fun i => (kept i).toFinset) lPos
    have sizes : (∑ i, (kept i).toFinset.card) = K :=
      sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (keptSimple i))
    rw [sizes,Fintype.card_fin] at count
    exact count
  have vRoom : 3*Fintype.card V ≤ 4*n := by
    change 3*(M/D) ≤ n at dRoom
    omega
  have pRoom : 3*Fintype.card (ListBlockIndex kept L) ≤ 4*p := by
    change 3*(M/L) ≤ p at lRoom
    have trim : K/L ≤ M/L := Nat.div_le_div_right upper
    omega
  have length (i : ListBlockIndex kept L) : (pieces i).length ≤ L :=
    localPathBlock_length (kept i.fst) (keptSimple i.fst) lPos i.snd.val
  have degree (v : V) : (occurrences (fun i => (pieces i).toFinset) v).card ≤ D := by
    have copiedDegree : (occurrences (fun i => (copied i).toFinset) v).card ≤ D := by
      simpa only [copied,splitListVertices_toFinset] using
        (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
    refine (splitListPaths_degree kept L v).trans ((card_le_card ?_).trans copiedDegree)
    intro i member
    have onRow := List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (kept i).toFinset)).mp member)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset onRow))
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (half := half) (retention := 32)
    pieces piecesSimple legal hn hp dense long (vNum := 3) (vDen := 4) (pNum := 3) (pDen := 4)
    (by decide) (by decide) (by decide) (by decide) vRoom pRoom length degree (exactMass.trans_le upper) ?_
  rw [exactMass]
  change 17*M ≤ 18*K at retained
  omega

/-- Delete incidences from the fixed degree copies before testing the
width cuts. Up to M/18 deletions still allow both original budgets and
all four original-average caps. -/
theorem regularization_list_frozen_after_copied_row_deletions {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (kept : let M := ∑ i, (paths i).length; Fin p → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length; ∀ i, (kept i).Sublist (splitListVertices paths (4*M/n) i))
    (retained : 17*(∑ i, (paths i).length) ≤ 18*(∑ i, (kept i).length))
    (returns : let M := ∑ i, (paths i).length; NoShortReturnAcrossWidthCutsInPieces kept (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_admissible_copied_row_deletions paths simple hn hp dense long kept sub
    (localOrderAdmissible_of_sublist (fun i => splitListVertices_simple paths _ i (simple i)) sub copyLegal)
    retained returns

end OnlineReachabilityPreservers
