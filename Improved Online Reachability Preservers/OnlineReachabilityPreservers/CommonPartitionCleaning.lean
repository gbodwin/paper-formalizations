import OnlineReachabilityPreservers.VertexPartitionCleaning

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I A B : Type*} [LinearOrder V] [LinearOrder I] [LinearOrder A] [LinearOrder B]

/-- Give each occurrence a vertex copy shared by paths in the same part. -/
def partitionListVertices (paths : I → List V) (part : I → A) (i : I) : List (V ×ₗ A) :=
  (paths i).map (fun v => toLex (v,part i))

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] in
theorem partitionListVertices_simple (paths : I → List V) (part : I → A)
    (simple : ∀ i, (paths i).Nodup) (i : I) : (partitionListVertices paths part i).Nodup :=
  (simple i).map (fun _ _ h => congrArg (fun x => (ofLex x).1) h)

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] in
private theorem partitionListVertices_project (paths : I → List V) (part : I → A) (i : I) :
    (partitionListVertices paths part i).map (fun w => (ofLex w).1) = paths i := by
  simp [partitionListVertices, List.map_map, Function.comp_def]

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] in
private theorem partitionListVertices_mem {paths : I → List V} {part : I → A} {i : I}
    {w : V ×ₗ A} : w ∈ partitionListVertices paths part i ↔
      (ofLex w).1 ∈ paths i ∧ (ofLex w).2 = part i := by
  constructor
  · intro h
    obtain ⟨v,inside,rfl⟩ := List.mem_map.mp h
    exact ⟨inside,rfl⟩
  · rintro ⟨inside,tag⟩
    exact List.mem_map.mpr ⟨(ofLex w).1,inside,ofLex.injective (Prod.ext rfl tag.symm)⟩

/-- All bridge corners use the same part, so the original vertices remain
distinct when the tags are removed. All path indices keep their order. -/
theorem partitionListVertices_admissible (paths : I → List V) (part : I → A)
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (partitionListVertices paths part) := by
  let copies := partitionListVertices paths part
  let project := fun w : V ×ₗ A => (ofLex w).1
  let tag := fun w : V ×ₗ A => (ofLex w).2
  have samePart {i : I} {w : V ×ₗ A} (h : w ∈ copies i) : tag w = part i :=
    (partitionListVertices_mem.mp h).2
  have projectEq : (fun i => (copies i).map project) = paths :=
    funext (partitionListVertices_project paths part)
  have step {i : I} {x y : V ×ₗ A} (h : ListBefore copies i x y) :
      ListBefore paths i (project x) (project y) := by
    have simpleProjected : ((copies i).map project).Nodup := by
      rw [congrFun projectEq i]
      exact simple i
    have projected := listBefore_map project simpleProjected h
    rw [projectEq] at projected
    exact projected
  have projectBridge {s : ℕ} (b : Bridge (ListBefore copies) s) :
      ∃ old : Bridge (ListBefore paths) s, old.river = b.river ∧ old.arc = b.arc := by
    have sameCorner (i : Fin (s+2)) : tag (b.vertex 0) = tag (b.vertex i) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        exact ih.trans ((samePart (b.arcStep i).1).trans (samePart (b.arcStep i).2.1).symm)
    let old : Bridge (ListBefore paths) s :=
      ⟨project ∘ b.vertex, b.arc, b.river, fun i j equal => b.distinctVertices
        (ofLex.injective (Prod.ext equal ((sameCorner i).symm.trans (sameCorner j)))),
        b.distinctArcs, b.river_ne_arc,step b.riverStep, fun i => step (b.arcStep i)⟩
    exact ⟨old,rfl,rfl⟩
  cases half
  · intro s hs
    exact ⟨fun b => (allowed hs).false (projectBridge b).choose⟩
  · intro s hs b earlier
    obtain ⟨old,river,arcs⟩ := projectBridge b
    apply allowed hs old
    rwa [river,arcs]

variable [Fintype I]

omit [LinearOrder I] in
/-- Each vertex copy has exactly the occurrences of its original vertex in the
designated part of the paths. -/
theorem partitionListVertices_degree (paths : I → List V) (part : I → A) (w : V ×ₗ A) :
    occurrences (fun i => (partitionListVertices paths part i).toFinset) w =
      (occurrences (fun i => (paths i).toFinset) (ofLex w).1).filter
        (fun i => part i = (ofLex w).2) := by
  ext i
  simp only [mem_occurrences, List.mem_toFinset, mem_filter, partitionListVertices_mem, eq_comm]

/-- Apply the two shared partitions simultaneously. Each copy is tagged
by the part of its path, and each path piece uses just one vertex part. -/
def partitionListIncidences (paths : I → List V) (pathPart : I → A) (vertexPart : V → B) :
    I ×ₗ B → List (V ×ₗ A) :=
  partitionListPaths (partitionListVertices paths pathPart) (fun v => vertexPart (ofLex v).1)

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] [Fintype I] in
theorem partitionListIncidences_simple (paths : I → List V) (pathPart : I → A) (vertexPart : V → B)
    (simple : ∀ i, (paths i).Nodup) (j : I ×ₗ B) :
    (partitionListIncidences paths pathPart vertexPart j).Nodup :=
  List.filter_sublist.nodup (partitionListVertices_simple paths pathPart simple (ofLex j).1)

omit [Fintype I] in
/-- Both exclusions survive both shared partitions at every cutoff. -/
theorem partitionListIncidences_admissible (paths : I → List V) (pathPart : I → A) (vertexPart : V → B)
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (partitionListIncidences paths pathPart vertexPart) :=
  partitionListPaths_admissible _ _ (partitionListVertices_simple paths pathPart simple)
    (partitionListVertices_admissible paths pathPart simple allowed)

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] [Fintype I] in
theorem partitionListIncidences_length (paths : I → List V) (pathPart : I → A) (vertexPart : V → B)
    (j : I ×ₗ B) :
    (partitionListIncidences paths pathPart vertexPart j).length =
      (partitionListPaths paths vertexPart j).length := by
  simp only [partitionListIncidences, partitionListPaths, partitionListVertices, List.filter_map,
    Function.comp_def, List.length_map]
  rfl

omit [LinearOrder I] in
theorem partitionListIncidences_degree [Fintype B] (paths : I → List V) (pathPart : I → A)
    (vertexPart : V → B) (w : V ×ₗ A) :
    (occurrences (fun i => (partitionListIncidences paths pathPart vertexPart i).toFinset) w).card =
      ((occurrences (fun i => (paths i).toFinset) (ofLex w).1).filter
        (fun i => pathPart i = (ofLex w).2)).card := by
  rw [partitionListIncidences, partitionListPaths_degree, partitionListVertices_degree]

omit [LinearOrder I] [LinearOrder A] in
/-- Each original incidence contributes one incidence to the block system. -/
theorem partitionListIncidences_mass [Fintype B] (paths : I → List V) (pathPart : I → A) (vertexPart : V → B)
    (simple : ∀ i, (paths i).Nodup) :
    (∑ j, (partitionListIncidences paths pathPart vertexPart j).length) = ∑ i, (paths i).length := by
  simp only [partitionListIncidences_length]
  exact partitionListPaths_mass paths vertexPart simple

section Support

variable {W J : Type*} [LinearOrder W] [LinearOrder J] [Fintype J]

/-- Only vertices occurring on a path are needed for the cleaning budgets. -/
def activeListVertices (paths : J → List W) : Finset W :=
  univ.biUnion (fun j => (paths j).toFinset)

/-- Only nonempty paths are needed for the cleaning budgets. -/
def activeListIndices (paths : J → List W) : Finset J :=
  univ.filter (fun j => paths j ≠ [])

omit [LinearOrder J] in
private theorem activeListVertices_subset (paths : J → List W) (j : J) :
    (paths j).toFinset ⊆ activeListVertices paths := fun _ h => mem_biUnion.mpr ⟨j,mem_univ _,h⟩

/-- Discard unused vertex copies and empty path pieces. -/
def activeListPaths (paths : J → List W) (j : activeListIndices paths) :
    List (activeListVertices paths) :=
  restrictListPaths paths (activeListVertices paths) (activeListIndices paths) j

omit [LinearOrder J] in
theorem activeListPaths_simple (paths : J → List W) (simple : ∀ j, (paths j).Nodup)
    (j : activeListIndices paths) : (activeListPaths paths j).Nodup :=
  restrictListPath_nodup (simple j.val) _

theorem activeListPaths_admissible (paths : J → List W) (simple : ∀ j, (paths j).Nodup)
    {half : Bool} {k : ℕ} (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (activeListPaths paths) := by
  cases half
  · exact restrictListPaths_fullFree simple allowed _ _
  · exact restrictListPaths_halfFree simple allowed _ _

omit [LinearOrder J] in
theorem activeListPaths_length (paths : J → List W) (simple : ∀ j, (paths j).Nodup)
    (j : activeListIndices paths) : (activeListPaths paths j).length = (paths j.val).length := by
  change (restrictListPath (paths j.val) (activeListVertices paths)).length = _
  rw [restrictListPath_length (simple j.val),
    inter_eq_left.mpr (activeListVertices_subset paths j.val), List.toFinset_card_of_nodup (simple j.val)]

theorem activeListPaths_degree_le (paths : J → List W) (w : activeListVertices paths) :
    (occurrences (fun j => (activeListPaths paths j).toFinset) w).card ≤
      (occurrences (fun j => (paths j).toFinset) w.val).card := by
  have projected (j : activeListIndices paths) :=
    restrictListPaths_toFinset paths (activeListVertices paths) (activeListIndices paths) j
  simp only [activeListPaths, projected]
  exact rectanglePaths_degree_le (fun j => (paths j).toFinset) _ _ _

omit [LinearOrder J] in
/-- Support restriction preserves every incidence. -/
theorem activeListPaths_mass (paths : J → List W) (simple : ∀ j, (paths j).Nodup) :
    (∑ j : activeListIndices paths, (activeListPaths paths j).length) =
      ∑ j, (paths j).length := by
  simp only [activeListPaths_length paths simple]
  rw [← Finset.sum_subtype (activeListIndices paths) (fun _ => Iff.rfl) (fun j => (paths j).length)]
  apply sum_subset (subset_univ _)
  intro j _ outside
  have empty : paths j = [] := by
    by_contra nonempty
    exact outside (mem_filter.mpr ⟨mem_univ _,nonempty⟩)
  simp [empty]

end Support

omit [LinearOrder V] [LinearOrder I] [LinearOrder A] [Fintype I] in
private theorem partitionListIncidences_mem {paths : I → List V} {pathPart : I → A}
    {vertexPart : V → B} {j : I ×ₗ B} {w : V ×ₗ A} :
    w ∈ partitionListIncidences paths pathPart vertexPart j ↔
      (ofLex w).1 ∈ paths (ofLex j).1 ∧
      (ofLex w).2 = pathPart (ofLex j).1 ∧ vertexPart (ofLex w).1 = (ofLex j).2 := by
  simp only [partitionListIncidences, partitionListPaths, List.mem_filter, decide_eq_true_eq,
    partitionListVertices_mem, and_assoc]

omit [LinearOrder I] in
/-- Count only vertex copies actually used. Each original vertex
contributes the number of path parts in which it occurs. -/
theorem partition_activeVertices_card [Fintype V] [Fintype B] (paths : I → List V)
    (pathPart : I → A) (vertexPart : V → B) :
    (activeListVertices (partitionListIncidences paths pathPart vertexPart)).card =
      ∑ v, ((occurrences (fun i => (paths i).toFinset) v).image pathPart).card := by
  let vertices := activeListVertices (partitionListIncidences paths pathPart vertexPart)
  let first := fun w : V ×ₗ A => (ofLex w).1
  let second := fun w : V ×ₗ A => (ofLex w).2
  have support (w : V ×ₗ A) :
      w ∈ vertices ↔ ∃ i, first w ∈ paths i ∧ second w = pathPart i := by
    change w ∈ activeListVertices _ ↔ _
    simp only [activeListVertices, mem_biUnion, mem_univ, true_and, List.mem_toFinset,
      partitionListIncidences_mem]
    constructor
    · rintro ⟨j,inside,tag,_⟩
      exact ⟨(ofLex j).1,inside,tag⟩
    · rintro ⟨i,inside,tag⟩
      exact ⟨toLex (i,vertexPart (first w)),inside,tag,rfl⟩
  rw [card_eq_sum_card_fiberwise (f := first) (t := (univ : Finset V)) (by simp)]
  apply sum_congr rfl
  intro v _
  let copy : A ↪ V ×ₗ A :=
    ⟨fun a => toLex (v,a), fun _ _ eq => congrArg second eq⟩
  have fiber : vertices.filter (fun w => first w = v) =
      ((occurrences (fun i => (paths i).toFinset) v).image pathPart).map copy := by
    ext w
    simp only [mem_filter, support, mem_map, mem_image, mem_occurrences, List.mem_toFinset]
    constructor
    · rintro ⟨⟨i,inside,tag⟩,base⟩
      exact ⟨pathPart i,⟨i,base ▸ inside,rfl⟩,
        ofLex.injective (Prod.ext base.symm tag.symm)⟩
    · rintro ⟨a,⟨i,inside,rfl⟩,rfl⟩
      exact ⟨⟨i,inside,rfl⟩,rfl⟩
  change (vertices.filter (fun w => first w = v)).card = _
  rw [fiber,card_map]

omit [LinearOrder A] in
/-- Each original path contributes one occupied piece per vertex
part that intersects it. -/
theorem partition_activeIndices_card [Fintype B] (paths : I → List V)
    (pathPart : I → A) (vertexPart : V → B) :
    (activeListIndices (partitionListIncidences paths pathPart vertexPart)).card =
       ∑ i, ((paths i).toFinset.image vertexPart).card := by
  let pieces := activeListIndices (partitionListIncidences paths pathPart vertexPart)
  let first := fun j : I ×ₗ B => (ofLex j).1
  let second := fun j : I ×ₗ B => (ofLex j).2
  have occupied (j : I ×ₗ B) : j ∈ pieces ↔ ∃ v, v ∈ paths (first j) ∧ vertexPart v = second j := by
    change j ∈ activeListIndices _ ↔ _
    simp only [activeListIndices, mem_filter, mem_univ, true_and]
    constructor
    · intro nonempty
      obtain ⟨w,inside⟩ := List.exists_mem_of_ne_nil _ nonempty
      obtain ⟨mem,_,part⟩ := partitionListIncidences_mem.mp inside
      exact ⟨(ofLex w).1,mem,part⟩
    · rintro ⟨v,inside,part⟩ empty
      have some : toLex (v,pathPart (first j)) ∈ partitionListIncidences paths pathPart vertexPart j :=
        partitionListIncidences_mem.mpr ⟨inside,rfl,part⟩
      rw [empty] at some
      exact List.not_mem_nil some
  rw [card_eq_sum_card_fiberwise (f := first) (t := (univ : Finset I)) (by simp)]
  apply sum_congr rfl
  intro i _
  let copy : B ↪ I ×ₗ B :=
    ⟨fun b => toLex (i,b),fun _ _ eq => congrArg second eq⟩
  have fiber : pieces.filter (fun j => first j = i) = ((paths i).toFinset.image vertexPart).map copy := by
    ext j
    simp only [mem_filter, occupied, mem_map, mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨⟨v,inside,tag⟩,base⟩
      exact ⟨vertexPart v,⟨v,base ▸ inside,rfl⟩,ofLex.injective (Prod.ext base.symm tag)⟩
    · rintro ⟨part,⟨v,inside,rfl⟩,rfl⟩
      exact ⟨⟨v,inside,rfl⟩,rfl⟩
  change (pieces.filter (fun j => first j = i)).card = _
  rw [fiber,card_map]

/-- A common partition on each side gives a frozen cleaning witness when
every occupied row and column meets its cap and the occupied supports fit
within four thirds of the original budgets. Both bridge modes work at
every cutoff. -/
theorem regularization_list_frozen_by_partitions [Fintype V] [Fintype B]
    {half : Bool} {k n p M : ℕ} (paths : I → List V) (pathPart : I → A) (vertexPart : V → B)
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : 3*(∑ v, ((occurrences (fun i => (paths i).toFinset) v).image pathPart).card) ≤ 4*n)
    (families : 3*(∑ i, ((paths i).toFinset.image vertexPart).card) ≤ 4*p)
    (lengthCap : ∀ j, (partitionListPaths paths vertexPart j).length ≤ 4*M/p)
    (degreeCap : ∀ v a, ((occurrences (fun i => (paths i).toFinset) v).filter
      (fun i => pathPart i = a)).card ≤ 4*M/n)
    (mass : (∑ i, (paths i).length) = M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let pieces := partitionListIncidences paths pathPart vertexPart
  have pieceSimple : ∀ j, (pieces j).Nodup := partitionListIncidences_simple paths pathPart vertexPart simple
  have pieceLegal : localOrderAdmissible half k pieces :=
    partitionListIncidences_admissible paths pathPart vertexPart simple allowed
  apply regularization_list_frozen_after_caps_with_room (activeListPaths pieces)
    (activeListPaths_simple pieces pieceSimple) (activeListPaths_admissible pieces pieceSimple pieceLegal)
    hn hp dense long
  · simpa only [Fintype.card_coe, pieces, partition_activeVertices_card] using vertices
  · simpa only [Fintype.card_coe, pieces, partition_activeIndices_card] using families
  · intro j
    rw [activeListPaths_length _ pieceSimple]
    exact (partitionListIncidences_length paths pathPart vertexPart j.val).trans_le (lengthCap j.val)
  · intro v
    apply (activeListPaths_degree_le pieces v).trans
    simpa only [pieces, partitionListIncidences_degree] using degreeCap (ofLex v.val).1 (ofLex v.val).2
  · rw [activeListPaths_mass pieces pieceSimple]
    exact (partitionListIncidences_mass paths pathPart vertexPart simple).trans mass

end OnlineReachabilityPreservers
