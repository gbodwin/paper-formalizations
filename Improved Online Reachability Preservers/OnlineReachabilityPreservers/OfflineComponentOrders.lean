import Mathlib.Data.List.FinRange
import OnlineReachabilityPreservers.CyclicReturnOverlay
import OnlineReachabilityPreservers.OfflineOrderedBlocks
import OnlineReachabilityPreservers.LocalSourceCounting

/-! Combine ordered subsequences across components of the precedence graph. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The condensation orders all comparisons between components. Within a
component, any supplied order can break ties. -/
private theorem componentRanks_extend {n p : ℕ} (paths : Fin p → List (Fin n))
    (within : Fin n → ℕ) :
    ∃ rank : Fin n ≃ Fin n, ∀ i x y,
      ListBefore paths i x y →
      (componentLabel (pathPrecedenceGraph paths) x = componentLabel (pathPrecedenceGraph paths) y →
        within x < within y) → rank x < rank y := by
  classical
  let G := pathPrecedenceGraph paths
  let label := componentLabel G
  let C := condensation G
  let key (v : Fin n) : ℕ ×ₗ (ℕ ×ₗ Fin n) :=
    toLex ((reaches C (label v)).card, toLex (within v,v))
  let keys := Equiv.ofInjective key (fun _ _ eq => congrArg (fun a => (ofLex (ofLex a).2).2) eq)
  let : Fintype (Set.range key) := Fintype.ofEquiv _ keys
  have count : Fintype.card (Set.range key) = n := (Fintype.card_congr keys).symm.trans (Fintype.card_fin n)
  let order := (Fintype.orderIsoFinOfCardEq (Set.range key) count).symm
  refine ⟨keys.trans order.toEquiv, fun i x y before localOrder => order.strictMono ?_⟩
  change key x < key y
  apply Prod.Lex.toLex_lt_toLex.mpr
  by_cases same : label x = label y
  · refine Or.inr ⟨congrArg (fun a => (reaches C a).card) same, ?_⟩
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (localOrder same))
  · have edge : Edge G x y := by
      unfold Edge G pathPrecedenceGraph
      exact mem_filter.mpr ⟨mem_univ _, i, before⟩
    have crossed : Edge C (label x) (label y) :=
      edge_condensation.mpr ⟨same, x, y, edge, rfl, rfl⟩
    exact Or.inl (reaches_card_lt (condensation_dag G) crossed)

private theorem listBefore_lt_key {V I : Type*} [DecidableEq V] {paths : I → List V}
    (key : V → ℕ) {i : I} (ordered : (paths i).Pairwise (fun x y => key x < key y))
    {x y : V} (before : ListBefore paths i x y) : key x < key y := by
  have early := List.idxOf_lt_length_of_mem before.1
  have later := List.idxOf_lt_length_of_mem before.2.1
  have step := List.pairwise_iff_getElem.mp ordered _ _ early later before.2.2
  rwa [List.getElem_idxOf early, List.getElem_idxOf later] at step

/-- Stitch separately ordered subsequences from different strongly connected
components together. The local choices may be empty. A path with no kept
vertex gets a singleton, so the demand count stays exact. -/
theorem theorem14_lower_of_component_subsequences {n p loss : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (parts : Fin n → Fin p → List (Fin n))
    (within : Fin n → ℕ) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (subparts : ∀ c i, (parts c i).Sublist (paths i))
    (inside : ∀ c i v, v ∈ parts c i → componentLabel (pathPrecedenceGraph paths) v = c)
    (localOrder : ∀ c i, (parts c i).Pairwise (fun x y => within x < within y))
    (mass : (∑ i, (paths i).length) ≤ loss * ∑ i, ∑ c, (parts c i).length) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*loss)*H.card := by
  let label := componentLabel (pathPrecedenceGraph paths)
  let raw (i : Fin p) := (paths i).filter (fun v => decide (v ∈ parts (label v) i))
  let kept (i : Fin p) := if raw i = [] then [(paths i).head (nonempty i)] else raw i
  have rawSub (i : Fin p) : (raw i).Sublist (paths i) := List.filter_sublist
  have present (i : Fin p) (v : Fin n) : v ∈ raw i ↔ v ∈ paths i ∧ v ∈ parts (label v) i := by
    simp [raw]
  have keptSub (i : Fin p) : (kept i).Sublist (paths i) := by
    unfold kept
    split
    · exact List.singleton_sublist.mpr (List.head_mem _)
    · exact rawSub i
  have keptNonempty (i : Fin p) : kept i ≠ [] := by
    by_cases empty : raw i = [] <;> simp [kept, empty]
  have lengthKept (i : Fin p) : (raw i).length ≤ (kept i).length := by
    by_cases empty : raw i = [] <;> simp [kept, empty]
  have exactParts (i : Fin p) (c : Fin n) :
      ((raw i).toFinset.filter fun v => label v = c) = (parts c i).toFinset := by
    ext v
    simp only [mem_filter, List.mem_toFinset, present]
    constructor
    · rintro ⟨⟨_, on⟩, same⟩
      exact same ▸ on
    · intro on
      have same : label v = c := inside c i v on
      exact ⟨⟨(subparts c i).subset on, same.symm ▸ on⟩, same⟩
  have rawCount (i : Fin p) : (raw i).length = ∑ c : Fin n, (parts c i).length := by
    calc
      (raw i).length = (raw i).toFinset.card := (List.toFinset_card_of_nodup ((rawSub i).nodup (simple i))).symm
      _ = ∑ c : Fin n, ((raw i).toFinset.filter fun v => label v = c).card :=
        card_eq_sum_card_fiberwise (t := univ) (fun _ _ => mem_univ _)
      _ = _ := sum_congr rfl fun c _ => by
        rw [exactParts, List.toFinset_card_of_nodup ((subparts c i).nodup (simple i))]
  obtain ⟨rank, orderedStep⟩ := componentRanks_extend paths within
  have increasing (i : Fin p) : ((kept i).map rank).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    by_cases empty : raw i = []
    · simp [kept, empty]
    · have asRaw : kept i = raw i := by simp [kept, empty]
      rw [asRaw, List.pairwise_iff_getElem]
      intro a b ha hb ab
      let x := (raw i)[a]
      let y := (raw i)[b]
      have onX : x ∈ raw i := List.getElem_mem ha
      have onY : y ∈ raw i := List.getElem_mem hb
      have step : ListBefore raw i x y := by
        refine ⟨onX, onY, ?_⟩
        have nodup := (rawSub i).nodup (simple i)
        have ix : (raw i).idxOf x = a := nodup.idxOf_getElem a ha
        have iy : (raw i).idxOf y = b := nodup.idxOf_getElem b hb
        rw [ix, iy]
        exact ab
      have original := listBefore_of_sublist (simple i) (rawSub i) step
      apply orderedStep i x y original
      intro same
      let c := label x
      have inX : x ∈ parts c i := ((present i x).mp onX).2
      have sameLabel : label y = c := same.symm
      have inY : y ∈ parts c i := by simpa only [sameLabel] using ((present i y).mp onY).2
      have localStep := (listBefore_sublist_iff (simple i) (subparts c i) inX inY).mpr original
      exact listBefore_lt_key within (localOrder c i) localStep
  apply theorem14_lower_of_increasing_subsequences hn hp paths kept rank simple keptNonempty free keptSub increasing
  apply mass.trans
  apply Nat.mul_le_mul_left
  exact sum_le_sum fun i _ => (rawCount i).symm.le.trans (lengthKept i)

/-- The part of every row lying in one SCC of the precedence graph. -/
noncomputable def pathsInPrecedenceComponent {n p : ℕ} (paths : Fin p → List (Fin n)) (c : Fin n) :
    Fin p → List (Fin n) :=
  fun i => (paths i).filter (fun v => decide (componentLabel (pathPrecedenceGraph paths) v = c))

private theorem mem_pathsInPrecedenceComponent {n p : ℕ} {paths : Fin p → List (Fin n)}
    {c : Fin n} {i : Fin p} {v : Fin n} :
    v ∈ pathsInPrecedenceComponent paths c i ↔ v ∈ paths i ∧ componentLabel (pathPrecedenceGraph paths) v = c := by
  simp [pathsInPrecedenceComponent]

private theorem pathsInPrecedenceComponent_sublist {n p : ℕ} (paths : Fin p → List (Fin n))
    (c : Fin n) (i : Fin p) : (pathsInPrecedenceComponent paths c i).Sublist (paths i) :=
  List.filter_sublist

private theorem edge_pathPrecedenceGraph_iff {n p : ℕ} {paths : Fin p → List (Fin n)} {x y : Fin n} :
    Edge (pathPrecedenceGraph paths) x y ↔ ∃ i, ListBefore paths i x y := by
  classical
  simp [Edge, pathPrecedenceGraph]

/-- All strict steps between vertices of an SCC, and thus all paths
between vertices in that SCC, survive restricting the original rows. -/
theorem precedenceComponent_reach_iff {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) {c x y : Fin n}
    (cx : componentLabel (pathPrecedenceGraph paths) x = c)
    (cy : componentLabel (pathPrecedenceGraph paths) y = c) :
    Reach (pathPrecedenceGraph (pathsInPrecedenceComponent paths c)) x y ↔ Reach (pathPrecedenceGraph paths) x y := by
  let G := pathPrecedenceGraph paths
  let C := pathPrecedenceGraph (pathsInPrecedenceComponent paths c)
  have sub : C ⊆ G := by
    intro e seen
    obtain ⟨i, on⟩ := edge_pathPrecedenceGraph_iff.mp (show Edge C e.1 e.2 from seen)
    exact edge_pathPrecedenceGraph_iff.mpr
      ⟨i, listBefore_of_sublist (simple i) (pathsInPrecedenceComponent_sublist paths c i) on⟩
  have internalEdge {u v : Fin n} (original : Edge G u v)
      (cu : componentLabel G u = c) (cv : componentLabel G v = c) : Edge C u v := by
    obtain ⟨i, on⟩ := edge_pathPrecedenceGraph_iff.mp original
    have inU := (mem_pathsInPrecedenceComponent (i := i)).mpr ⟨on.1, cu⟩
    have inV := (mem_pathsInPrecedenceComponent (i := i)).mpr ⟨on.2.1, cv⟩
    exact edge_pathPrecedenceGraph_iff.mpr
      ⟨i, (listBefore_sublist_iff (simple i) (pathsInPrecedenceComponent_sublist paths c i) inU inV).mpr on⟩
  have lifts {t : Fin n} (before : Reach G x t) : componentLabel G t = c → Reach C x t := by
    induction before with
    | refl => intro _; exact .refl
    | @tail u v used edge ih =>
      intro endComponent
      have back := (componentLabel_eq.mp (cx.trans endComponent.symm)).2
      have middleComponent : componentLabel G u = c :=
        (componentLabel_eq.mpr ⟨.single edge, back.trans used⟩).trans endComponent
      exact (ih middleComponent).tail (internalEdge edge middleComponent endComponent)
  exact ⟨reach_mono sub, fun forward => lifts forward cy⟩

/-- Full bridge exclusion survives the separate restriction to each
strongly connected component. -/
theorem precedenceComponent_fullFree {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (c : Fin n) (k : ℕ) : IsEmpty (Bridge (ListBefore (pathsInPrecedenceComponent paths c)) k) := by
  refine ⟨fun bridge => (free k).false (bridge.mapPaths id Function.injective_id ?_)⟩
  intro i x y before
  exact listBefore_of_sublist (simple i) (pathsInPrecedenceComponent_sublist paths c i) before

private theorem pathsInPrecedenceComponent_sum_length {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (i : Fin p) :
    (paths i).length = ∑ c : Fin n, (pathsInPrecedenceComponent paths c i).length := by
  let label := componentLabel (pathPrecedenceGraph paths)
  calc
    (paths i).length = (paths i).toFinset.card := (List.toFinset_card_of_nodup (simple i)).symm
    _ = ∑ c : Fin n, ((paths i).toFinset.filter fun v => label v = c).card :=
      card_eq_sum_card_fiberwise (t := univ) (fun _ _ => mem_univ _)
    _ = _ := sum_congr rfl fun c _ => by
      have same : ((paths i).toFinset.filter fun v => label v = c) =
          (pathsInPrecedenceComponent paths c i).toFinset := by
        ext v
        simp [mem_pathsInPrecedenceComponent, label]
      rw [same, List.toFinset_card_of_nodup ((pathsInPrecedenceComponent_sublist paths c i).nodup (simple i))]

/-- A uniform mass-retention result on the component restrictions would
extend with the same loss to all simple full-bridge-free inputs. -/
theorem theorem14_lower_of_uniform_component_retention {n p loss : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (nonempty : ∀ i, paths i ≠ [])
    (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k))
    (localRetention : ∀ c : Fin n, ∃ (within : Fin n → ℕ) (keep : Fin p → List (Fin n)),
      (∀ i, (keep i).Sublist (pathsInPrecedenceComponent paths c i)) ∧
      (∀ i, (keep i).Pairwise (fun x y => within x < within y)) ∧
      (∑ i, (pathsInPrecedenceComponent paths c i).length) ≤ loss * ∑ i, (keep i).length) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).length) ≤ (12*loss)*H.card := by
  classical
  choose positions parts posSub posOrdered posMass using localRetention
  let label := componentLabel (pathPrecedenceGraph paths)
  let within (v : Fin n) := positions (label v) v
  have inside (c : Fin n) (i : Fin p) (v : Fin n) (on : v ∈ parts c i) : label v = c :=
    (mem_pathsInPrecedenceComponent.mp ((posSub c i).subset on)).2
  have increasing (c : Fin n) (i : Fin p) : (parts c i).Pairwise (fun x y => within x < within y) := by
    rw [List.pairwise_iff_getElem]
    intro x y hx hy earlier
    have pair := List.pairwise_iff_getElem.mp (posOrdered c i) x y hx hy earlier
    simpa only [within, inside c i _ (List.getElem_mem hx), inside c i _ (List.getElem_mem hy)] using pair
  refine theorem14_lower_of_component_subsequences hn hp paths parts within simple nonempty free
    (fun c i => (posSub c i).trans (pathsInPrecedenceComponent_sublist paths c i)) inside increasing ?_
  calc
    (∑ i, (paths i).length) = ∑ i, ∑ c : Fin n, (pathsInPrecedenceComponent paths c i).length :=
      sum_congr rfl fun i _ => pathsInPrecedenceComponent_sum_length simple i
    _ = ∑ c : Fin n, ∑ i, (pathsInPrecedenceComponent paths c i).length := sum_comm
    _ ≤ ∑ c : Fin n, loss * ∑ i, (parts c i).length := sum_le_sum (fun c _ => posMass c)
    _ = loss * ∑ i, ∑ c : Fin n, (parts c i).length := by rw [← mul_sum, sum_comm]

section VisitCounterexample

open SourceAudit

private theorem singleReturnPaths_unique {V : Type*} (base : Unit → List V)
    {i j : ReturnPath Unit} {x y : ReturnVertex V Unit} (distinct : i ≠ j)
    (xi : x ∈ returnPaths base i) (xj : x ∈ returnPaths base j)
    (yi : y ∈ returnPaths base i) (yj : y ∈ returnPaths base j) : x = y := by
  rcases i with ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rcases j with ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
    cases x <;> cases y <;> simp_all [returnPaths]

/-- Even three simple full-bridge-free rows can have arbitrarily many
incidences per visit to a strongly connected component. -/
theorem component_visit_mass_no_uniform_factor (loss : ℕ) :
    ∃ (n : ℕ) (paths : Fin 3 → List (Fin n)),
      (∀ i, (paths i).Nodup) ∧ (∀ i, paths i ≠ []) ∧
      (∀ k, IsEmpty (Bridge (ListBefore paths) k)) ∧
      (∀ i, removeOppositeIntersections paths i = paths i) ∧
      loss * (∑ i, ((paths i).toFinset.image (componentLabel (pathPrecedenceGraph paths))).card) <
        ∑ i, (paths i).length := by
  classical
  let base : Unit → List (Fin (3*loss+1)) := fun _ => List.finRange _
  let W := ReturnVertex (Fin (3*loss+1)) Unit
  let encode := Fintype.equivFin W
  let rowIndex : Fin 3 ≃ ReturnPath Unit :=
    (Fintype.equivFinOfCardEq (α := ReturnPath Unit) (by decide)).symm
  let rows := returnPaths base
  let paths (i : Fin 3) := (rows (rowIndex i)).map encode
  let G := pathPrecedenceGraph paths
  have simple (i : ReturnPath Unit) : (rows i).Nodup :=
    returnPaths_nodup (fun _ => List.nodup_finRange _) i
  have rankedSimple (i : Fin 3) : (paths i).Nodup := (simple _).map encode.injective
  have nonempty (i : Fin 3) : paths i ≠ [] := by
    have positive : 0 < (paths i).length := by
      simpa only [paths, List.length_map] using returnPaths_length_pos base (rowIndex i)
    intro empty
    simp [empty] at positive
  have baseFree (k : ℕ) : IsEmpty (Bridge (ListBefore base) k) := by
    refine ⟨fun b => b.river_ne_arc 0 (Subsingleton.elim _ _)⟩
  have free (k : ℕ) : IsEmpty (Bridge (ListBefore paths) k) := by
    refine ⟨fun b => (returnPaths_fullFree base baseFree k).false ?_⟩
    have undone (i : Fin 3) : (paths i).map encode.symm = rows (rowIndex i) := by
      simp [paths, List.map_map, Function.comp_def]
    have back := b.mapVertices encode.symm encode.symm.injective (fun i x y step => by
      have result := listBefore_map encode.symm ((undone i).symm ▸ simple (rowIndex i)) step
      simpa only [undone] using result)
    exact back.mapPaths rowIndex rowIndex.injective (fun _ _ _ step => step)
  have pruned (i : Fin 3) : removeOppositeIntersections paths i = paths i := by
    have inOriginal {j : Fin 3} {x : Fin (Fintype.card W)} (on : x ∈ paths j) :
        encode.symm x ∈ rows (rowIndex j) := by
      obtain ⟨v, onRow, rfl⟩ := List.mem_map.mp on
      simpa only [Equiv.symm_apply_apply] using onRow
    have sub := removeOppositeIntersections_sublist paths i
    apply sub.eq_of_length_le
    rw [← List.toFinset_card_of_nodup (rankedSimple i),
      ← List.toFinset_card_of_nodup (sub.nodup (rankedSimple i))]
    apply card_le_card
    intro x present
    apply List.mem_toFinset.mpr
    refine (removeOppositeIntersections_mem paths i x).mpr ⟨List.mem_toFinset.mp present, ?_⟩
    rintro ⟨j, earlier, y, forward, reverse⟩
    have back : ListBefore paths j y x := removeOppositeIntersections_before rankedSimple reverse
    exact (listBefore_ne forward) (encode.symm.injective <|
      singleReturnPaths_unique base (fun eq => earlier.ne (rowIndex.injective eq))
        (inOriginal back.2.1) (inOriginal forward.1) (inOriginal back.1) (inOriginal forward.2.1))
  have edge (i : ReturnPath Unit) (x y : W) (step : ListBefore rows i x y) :
      Edge G (encode x) (encode y) := by
    have new := listBefore_map encode ((simple i).map encode.injective) step
    have after : ListBefore paths (rowIndex.symm i) (encode x) (encode y) := by
      have eq : paths (rowIndex.symm i) = (rows i).map encode := by simp [paths]
      unfold SourceAudit.BeforeIn
      rw [eq]
      exact new
    unfold G Edge pathPrecedenceGraph
    exact mem_filter.mpr ⟨mem_univ _, rowIndex.symm i, after⟩
  let start : W := .start ()
  let finish : W := .finish ()
  let turn : W := .turn ()
  let middle : List W := (base ()).map ReturnVertex.original
  have mainRow : rows (.main ()) = start :: (middle ++ [finish]) := rfl
  have noFinish : finish ∉ middle := by simp [middle, finish]
  have startIndex : (rows (.main ())).idxOf start = 0 := by simp [mainRow]
  have finishIndex : (rows (.main ())).idxOf finish = middle.length + 1 := by
    rw [mainRow, List.idxOf_cons_ne _ (by simp [finish, start] : start ≠ finish),
      List.idxOf_append_of_notMem noFinish]
    simp
  have startFinish : Edge G (encode start) (encode finish) := by
    apply edge (.main ())
    refine ⟨by simp [mainRow], by simp [mainRow], ?_⟩
    rw [startIndex, finishIndex]
    omega
  have finishTurn : Edge G (encode finish) (encode turn) :=
    edge (.first ()) finish turn (by simp [SourceAudit.BeforeIn, rows, returnPaths, finish, turn])
  have turnStart : Edge G (encode turn) (encode start) :=
    edge (.second ()) turn start (by simp [SourceAudit.BeforeIn, rows, returnPaths, turn, start])
  have finishStart : Reach G (encode finish) (encode start) :=
    (Relation.ReflTransGen.single finishTurn).tail turnStart
  have sameComponent (v : W) : SameComponent G (encode v) (encode start) := by
    cases v with
    | start u => cases u; exact SameComponent.refl G _
    | finish u => cases u; exact ⟨finishStart, .single startFinish⟩
    | turn u => cases u; exact ⟨.single turnStart, (Relation.ReflTransGen.single startFinish).tail finishTurn⟩
    | original v =>
      have present : ReturnVertex.original v ∈ middle := by
        simp [middle, base]
      have mainPresent : ReturnVertex.original v ∈ rows (.main ()) := by
        simp [mainRow, present]
      have pos : (rows (.main ())).idxOf (.original v) = middle.idxOf (.original v) + 1 := by
        rw [mainRow, List.idxOf_cons_ne _ (by simp [start]), List.idxOf_append_of_mem present]
      have enter : Edge G (encode start) (encode (.original v)) := by
        apply edge (.main ())
        refine ⟨by simp [mainRow], mainPresent, ?_⟩
        rw [startIndex, pos]
        omega
      have leave : Edge G (encode (.original v)) (encode finish) := by
        apply edge (.main ())
        refine ⟨mainPresent, by simp [mainRow], ?_⟩
        rw [pos, finishIndex]
        exact Nat.succ_lt_succ (List.idxOf_lt_length_of_mem present)
      exact ⟨finishStart.head leave, .single enter⟩
  have one (i : Fin 3) : ((paths i).toFinset.image (componentLabel G)).card = 1 := by
    let root := componentLabel G (encode start)
    have all (v : Fin (Fintype.card W)) : componentLabel G v = root :=
      (encode.apply_symm_apply v) ▸ componentLabel_eq.mpr (sameComponent (encode.symm v))
    have image : (paths i).toFinset.image (componentLabel G) = {root} := by
      ext v
      simp only [mem_image, mem_singleton, List.mem_toFinset]
      constructor
      · rintro ⟨u, _, rfl⟩
        exact all u
      · rintro rfl
        exact ⟨(paths i).head (nonempty i), List.head_mem _, all _⟩
    rw [image, card_singleton]
  have mass : (∑ i, (paths i).length) = 3*loss+1+6 := by
    simp only [paths, List.length_map]
    rw [Equiv.sum_comp rowIndex (fun i => (rows i).length), returnPaths_mass]
    simp [base]
  refine ⟨Fintype.card W, paths, rankedSimple, nonempty, free, pruned, ?_⟩
  change loss * (∑ i, ((paths i).toFinset.image (componentLabel G)).card) < _
  simp only [one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one, mass]
  omega

end VisitCounterexample

end OnlineReachabilityPreservers
