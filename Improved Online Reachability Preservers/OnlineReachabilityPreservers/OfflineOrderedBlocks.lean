import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Dedup
import OnlineReachabilityPreservers.Components
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

/-- An increasing subsequence on each row gives an exact-count lower
construction controlled by the total retained mass. -/
theorem theorem14_lower_of_increasing_subsequences {n p loss : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths kept : Fin p → List (Fin n)) (rank : Fin n ≃ Fin n)
    (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, kept i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (subsets : ∀ i, (kept i).Sublist (paths i))
    (ordered : ∀ i, ((kept i).map rank).Pairwise (· < ·))
    (retained : (∑ i, (paths i).length) ≤ loss * ∑ i, (kept i).length) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*loss)*H.card := by
  let ranked (i : Fin p) := (kept i).map rank
  let family (i : Fin p) := (ranked i).toFinset
  have rankedSimple (i : Fin p) : (ranked i).Nodup := ((subsets i).nodup (simple i)).map rank.injective
  have undo (i : Fin p) : (ranked i).map rank.symm = kept i := by simp [ranked, List.map_map, Function.comp_def]
  have touches (i : Fin p) : (family i).Nonempty := by
    exact ⟨rank ((kept i).head (nonempty i)), List.mem_toFinset.mpr (List.mem_map_of_mem (List.head_mem _))⟩
  have allowed (k : ℕ) : IsEmpty (Bridge (PathBefore family) k) := by
    refine ⟨fun bridge => (free k).false (bridge.mapVertices rank.symm rank.symm.injective ?_)⟩
    intro i x y step
    have order := before_of_increasing_finset (paths := ranked) (ordered i) step
    have back := listBefore_map rank.symm ((undo i).symm ▸ (subsets i).nodup (simple i)) order
    exact listBefore_of_sublist (simple i) (subsets i) (by simpa only [undo] using back)
  have familyMass : (∑ i, (family i).card) = ∑ i, (kept i).length := by
    apply sum_congr rfl
    intro i _
    rw [show (family i).card = (ranked i).length from List.toFinset_card_of_nodup (rankedSimple i)]
    exact List.length_map rank
  obtain ⟨G,D,acyclic,demands,size⟩ := theorem14_acyclic_extremal_lower hn hp family touches allowed
  refine ⟨G,D,acyclic,demands,fun H sub serves => ?_⟩
  calc
    _ ≤ loss * (∑ i, (kept i).length) := retained
    _ ≤ loss * (12 * H.card) := Nat.mul_le_mul_left _ (familyMass ▸ size H sub serves)
    _ = (12*loss)*H.card := by ring

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
  have count : (∑ i, (paths i).length) ≤ blocks * ∑ i, (best i).length := by
    rw [mul_sum]
    exact sum_le_sum (fun i _ => fits i)
  exact theorem14_lower_of_increasing_subsequences hn hp paths best (Equiv.refl _) simple bestNonempty free subsets
    (fun i => by simpa using ordered i (best i) (selected i)) count

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

/-- Include an arc for every strict order comparison along an input path. -/
noncomputable def pathPrecedenceGraph {n p : ℕ} (paths : Fin p → List (Fin n)) : Arcs (Fin n) := by
  classical
  exact univ.filter (fun e => ∃ i, ListBefore paths i e.1 e.2)

/-- Retain one vertex for each strongly connected component visited by each
path. The component order makes the retained rows increasing in a common order.
The comparison uses the total number of component visits. -/
theorem theorem14_lower_of_component_visits {n p loss : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (retained : (∑ i, (paths i).length) ≤ loss *
      ∑ i, ((paths i).toFinset.image (componentLabel (pathPrecedenceGraph paths))).card) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*loss)*H.card := by
  classical
  let G := pathPrecedenceGraph paths
  let label := componentLabel G
  let kept (i : Fin p) := (paths i).pwFilter (fun x y => label x ≠ label y)
  have subsets (i : Fin p) : (kept i).Sublist (paths i) := List.pwFilter_sublist _
  have keptLabelsSimple (i : Fin p) : ((kept i).map label).Nodup :=
    List.pairwise_map.mpr (List.pairwise_pwFilter _)
  have covered (i : Fin p) (x : Fin n) (on : x ∈ paths i) : label x ∈ (kept i).map label := by
    by_contra missing
    have different : ∀ y ∈ kept i, label x ≠ label y := by
      intro y present same
      exact missing (same ▸ List.mem_map_of_mem present)
    have allDifferent := (List.forall_mem_pwFilter (R := fun x y => label x ≠ label y)
      (fun {a b c} apart => not_and_or.mp (fun h => apart (h.1.trans h.2))) x (paths i)).mp different
    exact allDifferent x on rfl
  have image_eq (i : Fin p) : (paths i).toFinset.image label = ((kept i).map label).toFinset := by
    ext a
    simp only [mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, on, rfl⟩
      exact List.mem_map.mp (covered i v on)
    · rintro ⟨v, on, rfl⟩
      exact ⟨v, (subsets i).subset on, rfl⟩
  have keptNonempty (i : Fin p) : kept i ≠ [] := by
    intro empty
    have on := covered i ((paths i).head (nonempty i)) (List.head_mem _)
    simp [empty] at on
  let key (v : Fin n) : ℕ ×ₗ Fin n := toLex ((reaches (condensation G) (label v)).card, v)
  let keys := Equiv.ofInjective key (fun _ _ eq => congrArg (fun a => (ofLex a).2) eq)
  let : Fintype (Set.range key) := Fintype.ofEquiv _ keys
  have cardKeys : Fintype.card (Set.range key) = n := (Fintype.card_congr keys).symm.trans (Fintype.card_fin n)
  let order := (Fintype.orderIsoFinOfCardEq (Set.range key) cardKeys).symm
  let rank := keys.trans order.toEquiv
  have ordered (i : Fin p) : ((kept i).map rank).Pairwise (· < ·) := by
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro a b ha hb ab
    have distinct := List.pairwise_iff_getElem.mp (List.pairwise_pwFilter
      (R := fun x y => label x ≠ label y) (paths i)) a b ha hb ab
    have strict : ListBefore kept i (kept i)[a] (kept i)[b] := by
      refine ⟨List.getElem_mem ha, List.getElem_mem hb, ?_⟩
      have keptSimple := (subsets i).nodup (simple i)
      simpa only [keptSimple.idxOf_getElem a ha, keptSimple.idxOf_getElem b hb] using ab
    have before := listBefore_of_sublist (simple i) (subsets i) strict
    have edge : Edge G (kept i)[a] (kept i)[b] := by
      unfold Edge G pathPrecedenceGraph
      exact mem_filter.mpr ⟨mem_univ _, i, before⟩
    have step : Edge (condensation G) (label (kept i)[a]) (label (kept i)[b]) :=
      edge_condensation.mpr ⟨distinct, _, _, edge, rfl, rfl⟩
    apply order.strictMono
    change key _ < key _
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (reaches_card_lt (condensation_dag G) step))
  have visits (i : Fin p) : ((paths i).toFinset.image label).card = (kept i).length := by
    rw [image_eq, List.toFinset_card_of_nodup (keptLabelsSimple i), List.length_map]
  apply theorem14_lower_of_increasing_subsequences hn hp paths kept rank simple keptNonempty free subsets ordered
  simpa only [← visits] using retained

/-- A uniform bound on the number of vertices of a path in any one
component suffices for the component-visit lower bound. -/
theorem theorem14_lower_of_bounded_component_intersections {n p width : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (bounded : ∀ i a, ((paths i).toFinset.filter fun v => componentLabel (pathPrecedenceGraph paths) v = a).card ≤ width) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*width)*H.card := by
  let label := componentLabel (pathPrecedenceGraph paths)
  have rowMass (i : Fin p) : (paths i).length ≤ width * ((paths i).toFinset.image label).card := by
    calc
      (paths i).length = (paths i).toFinset.card := (List.toFinset_card_of_nodup (simple i)).symm
      _ = ∑ a ∈ (paths i).toFinset.image label,
          ((paths i).toFinset.filter fun v => label v = a).card := card_eq_sum_card_image label _
      _ ≤ ∑ _a ∈ (paths i).toFinset.image label, width := sum_le_sum (fun a _ => bounded i a)
      _ = width * ((paths i).toFinset.image label).card := by
        simp [mul_comm]
  apply theorem14_lower_of_component_visits hn hp paths simple nonempty free
  rw [mul_sum]
  exact sum_le_sum (fun i _ => rowMass i)

end OnlineReachabilityPreservers
