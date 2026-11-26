import OnlineReachabilityPreservers.CommonPartitionCleaning

/-! For a color on each incidence, tag both the row pieces and vertex copies. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {I V C : Type*} [LinearOrder I] [LinearOrder V] [LinearOrder C]

omit [LinearOrder I] [LinearOrder V] in
/-- A row contributes its subsequence of a given color, and each retained
vertex is tagged with that color. The color may depend on the incidence. -/
def partitionListIncidencesByColor (paths : I → List V) (color : I → V → C)
    (piece : I ×ₗ C) : List (V ×ₗ C) :=
  ((paths (ofLex piece).1).filter fun v => decide (color (ofLex piece).1 v = (ofLex piece).2)).map
    (fun v => toLex (v, (ofLex piece).2))

omit [LinearOrder I] [LinearOrder V] in
theorem partitionListIncidencesByColor_simple (paths : I → List V) (color : I → V → C)
    (simple : ∀ i, (paths i).Nodup) (piece : I ×ₗ C) :
    (partitionListIncidencesByColor paths color piece).Nodup :=
  (List.filter_sublist.nodup (simple (ofLex piece).1)).map
    (fun _ _ equal => congrArg (fun v => (ofLex v).1) equal)

omit [LinearOrder I] [LinearOrder V] in
private theorem partitionListIncidencesByColor_mem {paths : I → List V} {color : I → V → C}
    {j : I ×ₗ C} {w : V ×ₗ C} : w ∈ partitionListIncidencesByColor paths color j ↔
      (ofLex w).1 ∈ paths (ofLex j).1 ∧ color (ofLex j).1 (ofLex w).1 = (ofLex w).2 ∧
      (ofLex w).2 = (ofLex j).2 := by
  constructor
  · intro member
    obtain ⟨v,inside,rfl⟩ := List.mem_map.mp member
    obtain ⟨onRow,selected⟩ := List.mem_filter.mp inside
    exact ⟨onRow,of_decide_eq_true selected,rfl⟩
  · rintro ⟨onRow,selected,same⟩
    exact List.mem_map.mpr ⟨(ofLex w).1,List.mem_filter.mpr ⟨onRow,decide_eq_true (selected.trans same)⟩,
      ofLex.injective (Prod.ext rfl same.symm)⟩

/-- Every bridge occupies one color. Projecting its vertices and its row
pieces within that color is injective, and the original arrival order
is preserved. Both bridge exclusions survive at every cutoff. -/
theorem partitionListIncidencesByColor_admissible (paths : I → List V) (color : I → V → C)
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (partitionListIncidencesByColor paths color) := by
  let pieces := partitionListIncidencesByColor paths color
  let parent (i : I ×ₗ C) := (ofLex i).1
  let untag (v : V ×ₗ C) := (ofLex v).1
  let rowColor (i : I ×ₗ C) := (ofLex i).2
  let vertexColor (v : V ×ₗ C) := (ofLex v).2
  let projected (i : I ×ₗ C) := (pieces i).map untag
  have tagged {i : I ×ₗ C} {v : V ×ₗ C} (member : v ∈ pieces i) : vertexColor v = rowColor i := by
    obtain ⟨old,_,equal⟩ := List.mem_map.mp member
    exact (congrArg vertexColor equal).symm
  have sublist (i : I ×ₗ C) : (projected i).Sublist (paths (parent i)) := by
    simp [projected, pieces, partitionListIncidencesByColor, parent, untag, List.map_map, Function.comp_def]
  have step {i : I ×ₗ C} {a b : V ×ₗ C} (before : ListBefore pieces i a b) :
      ListBefore paths (parent i) (untag a) (untag b) :=
    listBefore_of_sublist (paths := fun i : I ×ₗ C => paths (parent i)) (cut := projected)
      (simple (parent i)) (sublist i) (listBefore_map untag ((sublist i).nodup (simple (parent i))) before)
  have projectBridge {s : ℕ} (b : Bridge (ListBefore pieces) s) :
      ∃ original : Bridge (ListBefore paths) s,
        original.river = parent b.river ∧ ∀ i, original.arc i = parent (b.arc i) := by
    have sameVertexColor (i : Fin (s+2)) : vertexColor (b.vertex 0) = vertexColor (b.vertex i) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        exact ih.trans ((tagged (b.arcStep i).1).trans (tagged (b.arcStep i).2.1).symm)
    have sameRowColor (i : Fin (s+1)) : rowColor (b.arc i) = rowColor b.river :=
      (tagged (b.arcStep i).1).symm.trans ((sameVertexColor i.castSucc).symm.trans (tagged b.riverStep.1))
    have sameRow {i j : I ×ₗ C} (parents : parent i = parent j) (colors : rowColor i = rowColor j) : i = j :=
      ofLex.injective (Prod.ext parents colors)
    let original : Bridge (ListBefore paths) s :=
      ⟨untag ∘ b.vertex, parent ∘ b.arc, parent b.river,
        fun i j equal => b.distinctVertices (ofLex.injective
          (Prod.ext equal ((sameVertexColor i).symm.trans (sameVertexColor j)))),
        fun i j equal => b.distinctArcs (sameRow equal ((sameRowColor i).trans (sameRowColor j).symm)),
        fun i equal => b.river_ne_arc i (sameRow equal (sameRowColor i).symm),
        step b.riverStep, fun i => step (b.arcStep i)⟩
    exact ⟨original, rfl, fun _ => rfl⟩
  cases half
  · intro s size
    exact ⟨fun b => (allowed size).false (projectBridge b).choose⟩
  · intro s size b earlier
    obtain ⟨original, river, arcs⟩ := projectBridge b
    apply allowed size original
    rw [river, arcs]
    rcases Prod.Lex.lt_iff.mp earlier with older | ⟨same, _⟩
    · exact older
    · exact (original.river_ne_arc (Fin.last s) (river.trans (same.symm.trans (arcs _).symm))).elim

variable [Fintype I] [Fintype C]

omit [LinearOrder I] in
/-- Every original incidence belongs to exactly one color. -/
theorem partitionListIncidencesByColor_mass (paths : I → List V) (color : I → V → C)
    (simple : ∀ i, (paths i).Nodup) :
    (∑ j, (partitionListIncidencesByColor paths color j).length) = ∑ i, (paths i).length := by
  calc
    _ = ∑ j : I × C, (partitionListIncidencesByColor paths color (toLex j)).length :=
      (Equiv.sum_comp (toLex : (I × C) ≃ (I ×ₗ C)) _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro i _
      have count (c : C) :
          (partitionListIncidencesByColor paths color (toLex (i,c))).length =
            ((paths i).toFinset.filter fun v => color i v = c).card := by
        change (((paths i).filter fun v => decide (color i v = c)).map _).length = _
        rw [List.length_map, ← List.toFinset_card_of_nodup (List.filter_sublist.nodup (simple i))]
        congr 1
        ext v
        simp
      simp_rw [count]
      rw [← card_eq_sum_card_fiberwise (f := color i) (t := (univ : Finset C)) (by simp),
        List.toFinset_card_of_nodup (simple i)]

omit [LinearOrder I] in
/-- The degree of one copy counts exactly the original occurrences of
that vertex with its color. -/
theorem partitionListIncidencesByColor_degree (paths : I → List V) (color : I → V → C) (w : V ×ₗ C) :
    (occurrences (fun j => (partitionListIncidencesByColor paths color j).toFinset) w).card =
      ((occurrences (fun i => (paths i).toFinset) (ofLex w).1).filter
        (fun i => color i (ofLex w).1 = (ofLex w).2)).card := by
  let embed : I ↪ I ×ₗ C := ⟨fun i => toLex (i,(ofLex w).2), fun _ _ equal => congrArg (fun j => (ofLex j).1) equal⟩
  rw [← card_map embed]
  congr 1
  ext j
  simp only [mem_occurrences, List.mem_toFinset, partitionListIncidencesByColor_mem,
    mem_map, mem_filter]
  constructor
  · rintro ⟨inside,selected,same⟩
    exact ⟨(ofLex j).1,⟨inside,selected⟩,ofLex.injective (Prod.ext rfl same)⟩
  · rintro ⟨i,⟨inside,selected⟩,rfl⟩
    exact ⟨inside,selected,rfl⟩

omit [LinearOrder I] in
/-- A vertex contributes one occupied copy for each of its incident colors. -/
theorem incidenceColors_activeVertices_card [Fintype V] (paths : I → List V) (color : I → V → C) :
    (activeListVertices (partitionListIncidencesByColor paths color)).card =
      ∑ v, ((occurrences (fun i => (paths i).toFinset) v).image (fun i => color i v)).card := by
  let vertices := activeListVertices (partitionListIncidencesByColor paths color)
  let first := fun w : V ×ₗ C => (ofLex w).1
  let second := fun w : V ×ₗ C => (ofLex w).2
  have support (w : V ×ₗ C) : w ∈ vertices ↔ ∃ i, first w ∈ paths i ∧ color i (first w) = second w := by
    change w ∈ activeListVertices _ ↔ _
    simp only [activeListVertices, mem_biUnion, mem_univ, true_and, List.mem_toFinset,
      partitionListIncidencesByColor_mem]
    constructor
    · rintro ⟨j,inside,selected,_⟩
      exact ⟨(ofLex j).1,inside,selected⟩
    · rintro ⟨i,inside,selected⟩
      exact ⟨toLex (i,second w),inside,selected,rfl⟩
  rw [card_eq_sum_card_fiberwise (f := first) (t := (univ : Finset V)) (by simp)]
  apply sum_congr rfl
  intro v _
  let copy : C ↪ V ×ₗ C := ⟨fun c => toLex (v,c),fun _ _ equal => congrArg second equal⟩
  have fiber : vertices.filter (fun w => first w = v) =
      ((occurrences (fun i => (paths i).toFinset) v).image (fun i => color i v)).map copy := by
    ext w
    simp only [mem_filter, support, mem_map, mem_image, mem_occurrences, List.mem_toFinset]
    constructor
    · rintro ⟨⟨i,inside,selected⟩,base⟩
      subst v
      exact ⟨color i (first w),⟨i,inside,rfl⟩,ofLex.injective (Prod.ext rfl selected)⟩
    · rintro ⟨c,⟨i,inside,rfl⟩,rfl⟩
      exact ⟨⟨i,inside,rfl⟩,rfl⟩
  change (vertices.filter (fun w => first w = v)).card = _
  rw [fiber, card_map]

/-- A row contributes one occupied piece for each color appearing on it. -/
theorem incidenceColors_activeIndices_card (paths : I → List V) (color : I → V → C) :
    (activeListIndices (partitionListIncidencesByColor paths color)).card =
      ∑ i, ((paths i).toFinset.image (color i)).card := by
  let pieces := activeListIndices (partitionListIncidencesByColor paths color)
  let first := fun j : I ×ₗ C => (ofLex j).1
  let second := fun j : I ×ₗ C => (ofLex j).2
  have occupied (j : I ×ₗ C) : j ∈ pieces ↔ ∃ v, v ∈ paths (first j) ∧ color (first j) v = second j := by
    change j ∈ activeListIndices _ ↔ _
    simp only [activeListIndices, mem_filter, mem_univ, true_and]
    constructor
    · intro nonempty
      obtain ⟨w,inside⟩ := List.exists_mem_of_ne_nil _ nonempty
      obtain ⟨member,selected,same⟩ := partitionListIncidencesByColor_mem.mp inside
      exact ⟨(ofLex w).1,member,selected.trans same⟩
    · rintro ⟨v,inside,selected⟩ empty
      have member : toLex (v,second j) ∈ partitionListIncidencesByColor paths color j :=
        partitionListIncidencesByColor_mem.mpr ⟨inside,selected,rfl⟩
      rw [empty] at member
      exact List.not_mem_nil member
  rw [card_eq_sum_card_fiberwise (f := first) (t := (univ : Finset I)) (by simp)]
  apply sum_congr rfl
  intro i _
  let copy : C ↪ I ×ₗ C := ⟨fun c => toLex (i,c),fun _ _ equal => congrArg second equal⟩
  have fiber : pieces.filter (fun j => first j = i) = ((paths i).toFinset.image (color i)).map copy := by
    ext j
    simp only [mem_filter, occupied, mem_map, mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨⟨v,inside,selected⟩,base⟩
      subst i
      exact ⟨color (first j) v,⟨v,inside,rfl⟩,ofLex.injective (Prod.ext rfl selected)⟩
    · rintro ⟨c,⟨v,inside,rfl⟩,rfl⟩
      exact ⟨⟨v,inside,rfl⟩,rfl⟩
  change (pieces.filter (fun j => first j = i)).card = _
  rw [fiber, card_map]

/-- An incidence coloring gives frozen cleaning at every cutoff if its
occupied row and vertex copies meet the upper caps and fit within four
thirds of the respective original budgets. -/
theorem regularization_list_frozen_by_incidence_colors [Fintype V] {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (color : I → V → C)
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : 3 * (∑ v, ((occurrences (fun i => (paths i).toFinset) v).image (fun i => color i v)).card) ≤ 4*n)
    (families : 3 * (∑ i, ((paths i).toFinset.image (color i)).card) ≤ 4*p)
    (lengthCap : ∀ j, (partitionListIncidencesByColor paths color j).length ≤ 4*M/p)
    (degreeCap : ∀ v c, ((occurrences (fun i => (paths i).toFinset) v).filter (fun i => color i v = c)).card ≤ 4*M/n)
    (total : (∑ i, (paths i).length) = M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let pieces := partitionListIncidencesByColor paths color
  have pieceSimple : ∀ j, (pieces j).Nodup := partitionListIncidencesByColor_simple paths color simple
  have pieceLegal : localOrderAdmissible half k pieces :=
    partitionListIncidencesByColor_admissible paths color simple allowed
  apply regularization_list_frozen_after_caps_with_room (activeListPaths pieces)
    (activeListPaths_simple pieces pieceSimple) (activeListPaths_admissible pieces pieceSimple pieceLegal) hn hp dense long
  · simpa only [Fintype.card_coe, pieces, incidenceColors_activeVertices_card] using vertices
  · simpa only [Fintype.card_coe, pieces, incidenceColors_activeIndices_card] using families
  · intro j
    rw [activeListPaths_length _ pieceSimple]
    exact lengthCap j.val
  · intro v
    apply (activeListPaths_degree_le pieces v).trans
    simpa only [pieces, partitionListIncidencesByColor_degree] using degreeCap (ofLex v.val).1 (ofLex v.val).2
  · rw [activeListPaths_mass pieces pieceSimple]
    exact (partitionListIncidencesByColor_mass paths color simple).trans total

end OnlineReachabilityPreservers
