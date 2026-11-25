import Mathlib.Data.List.MinMax
import OnlineReachabilityPreservers.OfflineDemandLower
import OnlineReachabilityPreservers.LocalRegularization

/-! Ordered blocks give an acyclic lower construction for Lemma 14. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem flatten_length_le {A : Type*} (rows : List (List A)) (width : ℕ)
    (fits : ∀ row ∈ rows, row.length ≤ width) : rows.flatten.length ≤ rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have first := fits row (List.mem_cons_self ..)
    have tail := ih (fun a ha => fits a (List.mem_cons_of_mem _ ha))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

private theorem before_of_increasing_finset {V I : Type*} [LinearOrder V]
    {paths : I → List V} {i : I} (ordered : (paths i).Pairwise (· < ·))
    {x y : V} (step : PathBefore (fun j => (paths j).toFinset) i x y) : ListBefore paths i x y := by
  have hx := List.mem_toFinset.mp step.1
  have hy := List.mem_toFinset.mp step.2.1
  rcases listBefore_total hx hy step.2.2.ne with forward | backward
  · exact forward
  · have across := List.pairwise_iff_getElem.mp ordered ((paths i).idxOf y) ((paths i).idxOf x)
      (List.idxOf_lt_length_of_mem hy) (List.idxOf_lt_length_of_mem hx) backward.2.2
    rw [List.getElem_idxOf, List.getElem_idxOf] at across
    exact (step.2.2.asymm across).elim

/-- Each path may have its own block boundaries. Keeping its longest
increasing block loses at most the factor `blocks` and retains the original
vertex and distinct-demand counts in the lower construction. -/
theorem theorem14_lower_of_ordered_blocks {n p blocks : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (parts : Fin p → List (List (Fin n)))
    (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (partition : ∀ i, (parts i).flatten = paths i)
    (number : ∀ i, (parts i).length ≤ blocks)
    (ordered : ∀ i row, row ∈ parts i → row.Pairwise (· < ·)) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*blocks)*H.card := by
  let best (i : Fin p) := ((parts i).argmax List.length).getD []
  have found (i : Fin p) : best i ∈ (parts i).argmax List.length := by
    cases winner : (parts i).argmax List.length with
    | none => exact (nonempty i ((partition i).symm.trans (by simp [List.argmax_eq_none.mp winner]))).elim
    | some row => simp [best,winner]
  have selected (i : Fin p) : best i ∈ parts i := List.argmax_mem (found i)
  have subsets (i : Fin p) : (best i).Sublist (paths i) :=
    (partition i) ▸ List.sublist_flatten_of_mem (selected i)
  have fits (i : Fin p) : (paths i).length ≤ blocks * (best i).length := by
    rw [← partition i]
    exact (flatten_length_le (parts i) (best i).length (fun _ present => List.le_of_mem_argmax present (found i))).trans
      (Nat.mul_le_mul_right _ (number i))
  have bestNonempty (i : Fin p) : best i ≠ [] := by
    intro empty
    have bound := fits i
    rw [empty,List.length_nil,mul_zero] at bound
    exact nonempty i (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bound))
  let family (i : Fin p) := (best i).toFinset
  have touches (i : Fin p) : (family i).Nonempty := by
    cases h : best i with
    | nil => exact (bestNonempty i h).elim
    | cons a rest => exact ⟨a,by simp [family,h]⟩
  have allowed (k : ℕ) : IsEmpty (Bridge (PathBefore family) k) := by
    refine ⟨fun bridge => (free k).false (bridge.mapPaths id Function.injective_id ?_)⟩
    intro i x y step
    have inside := before_of_increasing_finset (paths := best) (ordered i (best i) (selected i)) step
    exact listBefore_of_sublist (simple i) (subsets i) inside
  have count : (∑ i, (paths i).length) ≤ blocks * ∑ i, (family i).card := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    rw [show (family i).card = (best i).length from List.toFinset_card_of_nodup ((subsets i).nodup (simple i))]
    exact fits i
  obtain ⟨G,D,acyclic,demands,size⟩ := theorem14_acyclic_extremal_lower hn hp family touches allowed
  refine ⟨G,D,acyclic,demands,fun H sub serves => ?_⟩
  calc
    _ ≤ blocks * ∑ i, (family i).card := count
    _ ≤ blocks * (12 * H.card) := Nat.mul_le_mul_left _ (size H sub serves)
    _ = (12*blocks)*H.card := by ring

/-- A single vertex numbering giving each path at most one descent
suffices for a factor-24 lower construction at the original budgets. -/
theorem theorem14_lower_of_one_descent {n p : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (cut : ∃ rank : Fin n ≃ Fin n, ∀ i, ∃ left right : List (Fin n), (paths i).map rank = left ++ right ∧
      left.Pairwise (· < ·) ∧ right.Pairwise (· < ·)) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ 24*H.card := by
  obtain ⟨rank, cuts⟩ := cut
  choose left right agreement orderedLeft orderedRight using cuts
  let ranked (i : Fin p) := (paths i).map rank
  have rankedSimple (i : Fin p) : (ranked i).Nodup := (simple i).map rank.injective
  have rankedNonempty (i : Fin p) : ranked i ≠ [] := by simpa [ranked] using nonempty i
  have undo (i : Fin p) : (ranked i).map rank.symm = paths i := by simp [ranked,List.map_map,Function.comp_def]
  have rankedFree (k : ℕ) : IsEmpty (Bridge (ListBefore ranked) k) := by
    refine ⟨fun bridge => (free k).false (bridge.mapVertices rank.symm rank.symm.injective ?_)⟩
    intro i x y step
    have original := listBefore_map rank.symm ((undo i).symm ▸ simple i) step
    simpa only [undo] using original
  have blocksAgree (i : Fin p) : ([left i,right i] : List (List (Fin n))).flatten = ranked i := by
    simpa [ranked] using (agreement i).symm
  have blocksOrdered (i : Fin p) (row : List (Fin n)) (present : row ∈ [left i,right i]) : row.Pairwise (· < ·) := by
    rcases List.mem_cons.mp present with same | same
    · exact same.symm ▸ orderedLeft i
    · rw [List.mem_singleton] at same
      exact same.symm ▸ orderedRight i
  simpa only [ranked, List.length_map] using
    theorem14_lower_of_ordered_blocks (blocks := 2) hn hp ranked (fun i => [left i,right i])
      rankedSimple rankedNonempty rankedFree blocksAgree (fun _ => by simp) blocksOrdered

/-- The one-descent condition can be applied after pruning opposite intersections.
That pruning retains at least half the mass and one vertex on each nonempty path. -/
theorem theorem14_lower_of_pruned_one_descent {n p : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (cut : ∃ rank : Fin n ≃ Fin n, ∀ i, ∃ left right : List (Fin n),
      (removeOppositeIntersections paths i).map rank = left ++ right ∧
      left.Pairwise (· < ·) ∧ right.Pairwise (· < ·)) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ 48*H.card := by
  let kept := removeOppositeIntersections paths
  have keptSimple (i : Fin p) : (kept i).Nodup := (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have keptNonempty (i : Fin p) : kept i ≠ [] :=
    List.ne_nil_of_mem (removeOppositeIntersections_getLast_mem simple i (nonempty i))
  have keptFree (k : ℕ) : IsEmpty (Bridge (ListBefore kept) k) :=
    removeOppositeIntersections_fullFree (k := k + 2) simple (fun j _ => free j) le_rfl
  have freeThree : HalfBridgeFree (ListBefore paths) 3 := fun j _ b _ => (free j).false b
  have mass := removeOppositeIntersections_mass simple freeThree le_rfl
  obtain ⟨G,D,acyclic,demands,size⟩ := theorem14_lower_of_one_descent hn hp kept keptSimple keptNonempty keptFree cut
  refine ⟨G,D,acyclic,demands,fun H sub serves => ?_⟩
  have bound := size H sub serves
  change (∑ i, (paths i).length) ≤ 2 * (∑ i, (kept i).length) at mass
  omega

end OnlineReachabilityPreservers
