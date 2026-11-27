import OnlineReachabilityPreservers.ShortReturnPiecePacking

/-! The connected short-return groups are the smallest feasible pieces. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The component of a center, restricted to the elements being packed. -/
def linkedGroupComponent {V : Type*} [LinearOrder V] [Fintype V]
    (members : Finset V) (G : Arcs V) (center : V) : Finset V :=
  members.filter fun vertex => componentLabel G vertex = componentLabel G center

section LinkedGroupComponents

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Distinct strongly connected components restricted to the packed elements. -/
def linkedGroupComponents (members : Finset V) (G : Arcs V) : Finset (Finset V) :=
  members.image (linkedGroupComponent members G)

theorem linkedGroupComponents_cover (members : Finset V) (G : Arcs V) :
    (linkedGroupComponents members G).biUnion id = members := by
  ext x
  constructor
  · intro on
    obtain ⟨group, among, within⟩ := mem_biUnion.mp on
    obtain ⟨center, _, rfl⟩ := mem_image.mp among
    exact (mem_filter.mp within).1
  · intro on
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ on, mem_filter.mpr ⟨on, rfl⟩⟩

theorem linkedGroupComponents_apart (members : Finset V) (G : Arcs V) :
    (↑(linkedGroupComponents members G) : Set (Finset V)).PairwiseDisjoint id := by
  intro a onA b onB apart
  obtain ⟨x, _, rfl⟩ := mem_image.mp onA
  obtain ⟨y, _, rfl⟩ := mem_image.mp onB
  refine disjoint_left.mpr fun z inX inY => apart ?_
  have equal : componentLabel G x = componentLabel G y :=
    (mem_filter.mp inX).2.symm.trans (mem_filter.mp inY).2
  ext v
  simp only [linkedGroupComponent, mem_filter, equal]


/-- A graph projection injective on the selected vertices bounds their
component by the component of the projected center. -/
theorem linkedGroupComponent_card_le_project {W : Type*} [LinearOrder W] [Fintype W]
    {source : Finset W} {target : Finset V} {G : Arcs W} {H : Arcs V}
    (project : W → V) (members : ∀ {x}, x ∈ source → project x ∈ target)
    (injective : Set.InjOn project (source : Set W))
    (edges : ∀ {x y}, Edge G x y → Edge H (project x) (project y)) (center : W) :
    (linkedGroupComponent source G center).card ≤
      (linkedGroupComponent target H (project center)).card := by
  have reachable {x y} (path : Reach G x y) : Reach H (project x) (project y) := by
    induction path with
    | refl => exact .refl
    | tail _ edge previous => exact previous.tail (edges edge)
  apply card_le_card_of_injOn project
  · intro x on
    obtain ⟨listed, same⟩ := mem_filter.mp on
    have connected := componentLabel_eq.mp same
    exact mem_filter.mpr ⟨members listed, componentLabel_eq.mpr
      ⟨reachable connected.1, reachable connected.2⟩⟩
  · intro x left y right same
    exact injective (mem_filter.mp left).1 (mem_filter.mp right).1 same

end LinkedGroupComponents

/-- For a graph that symmetrizes the required links, a capped partition
exists exactly when each component of the packed elements fits. -/
theorem cappedPathPartition_iff_component_room {V : Type*} [LinearOrder V] [Fintype V]
    (members : Finset V) (linked : V → V → Prop) (G : Arcs V) (width : ℕ)
    (edges : ∀ ⦃x y⦄, Edge G x y ↔ linked x y ∨ linked y x)
    (inside : ∀ ⦃x y⦄, linked x y → x ∈ members ∧ y ∈ members) :
    (∃ groups, CappedPathPartition members linked width groups) ↔
      ∀ x ∈ members, (linkedGroupComponent members G x).card ≤ width := by
  let C := linkedGroupComponent members G
  constructor
  · rintro ⟨groups, partition⟩ x on
    have covered : x ∈ groups.biUnion id := partition.cover.symm ▸ on
    obtain ⟨group, hasGroup, inGroup⟩ := mem_biUnion.mp covered
    have step ⦃a b⦄ (edge : Edge G a b) (previous : a ∈ group) : b ∈ group := by
      have together : ∃ h ∈ groups, a ∈ h ∧ b ∈ h := by
        rcases edges.mp edge with forward | reverse
        · exact partition.together forward
        · obtain ⟨h, among, right, left⟩ := partition.together reverse
          exact ⟨h, among, left, right⟩
      obtain ⟨h, among, left, right⟩ := together
      have same : h = group := by
        by_contra! different
        exact disjoint_left.mp (partition.apart among hasGroup different) left previous
      exact same ▸ right
    have all : C x ⊆ group := by
      intro y member
      have reachable := (componentLabel_eq.mp (mem_filter.mp member).2).2
      clear member
      induction reachable with
      | refl => exact inGroup
      | tail _ edge ih => exact step edge ih
    exact (card_le_card all).trans (partition.fits group hasGroup)
  · intro room
    have present ⦃x⦄ (on : x ∈ members) : x ∈ C x := mem_filter.mpr ⟨on, rfl⟩
    refine ⟨linkedGroupComponents members G, ⟨linkedGroupComponents_cover members G,
      linkedGroupComponents_apart members G, ?_, ?_, ?_⟩⟩
    · intro group among
      obtain ⟨x, on, rfl⟩ := mem_image.mp among
      exact ⟨x, present on⟩
    · intro group among
      obtain ⟨x, on, rfl⟩ := mem_image.mp among
      exact room x on
    · intro x y relation
      obtain ⟨onX, onY⟩ := inside relation
      have connected : SameComponent G y x :=
        ⟨.single (edges.mpr (Or.inr relation)), .single (edges.mpr (Or.inl relation))⟩
      exact ⟨C x, mem_image_of_mem C onX, present onX,
        mem_filter.mpr ⟨onY, componentLabel_eq.mpr connected⟩⟩

section Components

variable {I V : Type*} [Fintype I] [LinearOrder V] [Fintype V]

/-- Join the endpoints of a row comparison in both directions when
there is a short backward return in the given rows. -/
def shortReturnRowGraph (rows : I → List V) (cutoff : ℕ) (i : I) : Arcs V := by
  letI (x y : V) : Decidable (Before rows i x y) := by unfold SourceAudit.BeforeIn; infer_instance
  let G := listPiecePrecedenceGraph rows
  exact univ.filter fun e =>
    (Before rows i e.1 e.2 ∧ e.2 ∈ reachIn G e.1 (cutoff - 3)) ∨
    (Before rows i e.2 e.1 ∧ e.1 ∈ reachIn G e.2 (cutoff - 3))

theorem shortReturnRowGraph_edge {rows : I → List V} {cutoff : ℕ} {i : I} {x y : V} :
    Edge (shortReturnRowGraph rows cutoff i) x y ↔
      (Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x (cutoff - 3)) ∨
      (Before rows i y x ∧ x ∈ reachIn (listPiecePrecedenceGraph rows) y (cutoff - 3)) := by
  simp only [shortReturnRowGraph, Edge, mem_filter, mem_univ, true_and]

/-- The connected group of an occurrence, restricted to its own row. -/
def shortReturnRowComponent (rows : I → List V) (cutoff : ℕ) (i : I) (x : V) : Finset V :=
  linkedGroupComponent (rows i).toFinset (shortReturnRowGraph rows cutoff i) x

/-- There is a partition into width-bounded pieces respecting every
short-return pair exactly when each connected group fits the width. -/
theorem hasCappedShortReturnPartition_iff_component_room
    (rows : I → List V) (width cutoff : ℕ) :
    HasCappedShortReturnPartition rows width cutoff ↔
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows cutoff i x).card ≤ width := by
  have test (i : I) := cappedPathPartition_iff_component_room
    (rows i).toFinset (fun x y => Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x (cutoff-3))
    (shortReturnRowGraph rows cutoff i) width (fun {_ _} => shortReturnRowGraph_edge)
    (fun {_ _} witness => ⟨List.mem_toFinset.mpr witness.1.1, List.mem_toFinset.mpr witness.1.2.1⟩)
  constructor
  · intro grouped i x on
    exact (test i).mp (grouped i) x (List.mem_toFinset.mpr on)
  · intro room i
    exact (test i).mpr (fun x on => room i x (List.mem_toFinset.mp on))

/-- Under an exact row projection to simple paths, every short-return
component has size at most the component of its projected center. -/
theorem shortReturnRowComponent_card_le_project {W : Type*} [LinearOrder W] [Fintype W]
    {rows : I → List V} {copies : I → List W} (project : W → V)
    (simple : ∀ i, (rows i).Nodup) (projects : ∀ i, (copies i).map project = rows i)
    (cutoff : ℕ) (i : I) (x : W) :
    (shortReturnRowComponent copies cutoff i x).card ≤
      (shortReturnRowComponent rows cutoff i (project x)).card := by
  have step ⦃j : I⦄ ⦃a b : W⦄ (before : Before copies j a b) :
      Before rows j (project a) (project b) := by
    have comparison := listBefore_map project ((projects j).symm ▸ simple j) before
    have same : (fun j => (copies j).map project) = rows := funext projects
    rwa [same] at comparison
  have comparisonEdge ⦃a b : W⦄ (edge : Edge (listPiecePrecedenceGraph copies) a b) :
      Edge (listPiecePrecedenceGraph rows) (project a) (project b) := by
    obtain ⟨j, comparison⟩ := listPiecePrecedenceGraph_edge.mp edge
    exact listPiecePrecedenceGraph_edge.mpr ⟨j, step comparison⟩
  have rowEdge ⦃a b : W⦄ (edge : Edge (shortReturnRowGraph copies cutoff i) a b) :
      Edge (shortReturnRowGraph rows cutoff i) (project a) (project b) := by
    have returnProjects ⦃a b : W⦄ (back : b ∈ reachIn (listPiecePrecedenceGraph copies) a (cutoff - 3)) :
        project b ∈ reachIn (listPiecePrecedenceGraph rows) (project a) (cutoff - 3) :=
      project_reachIn project (fun {_ _} edge => comparisonEdge edge) _ back
    rcases shortReturnRowGraph_edge.mp edge with forward | reverse
    · exact shortReturnRowGraph_edge.mpr (Or.inl ⟨step forward.1, returnProjects forward.2⟩)
    · exact shortReturnRowGraph_edge.mpr (Or.inr ⟨step reverse.1, returnProjects reverse.2⟩)
  refine linkedGroupComponent_card_le_project project ?_ ?_ (fun {_ _} edge => rowEdge edge) x
  · intro y on
    have appears := List.mem_map_of_mem (f := project) (List.mem_toFinset.mp on)
    rw [projects i] at appears
    exact List.mem_toFinset.mpr appears
  · intro a onA b onB equal
    by_contra! apart
    rcases listBefore_total (List.mem_toFinset.mp onA) (List.mem_toFinset.mp onB) apart with forward | reverse
    · exact listBefore_ne (step forward) equal
    · exact listBefore_ne (step reverse) equal.symm

end Components

/-- The connected groups give the exact path-partition premise for the
original-width frozen quarter-mass witness. -/
theorem regularization_list_frozen_of_short_return_component_room {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (room : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (shortReturnRowComponent copies k i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  exact regularization_list_frozen_of_capped_short_return_partitions paths simple hn hp dense long copyLegal
    ((hasCappedShortReturnPartition_iff_component_room _ _ _).mpr room)

section LinkedGroupSelection

variable {V : Type*} [LinearOrder V] [Fintype V]

private def takeGroup (width : ℕ) (items : Finset V) : Finset V :=
  ((items.sort (· ≤ ·)).take width).toFinset

omit [Fintype V] in
private theorem takeGroup_subset (width : ℕ) (items : Finset V) : takeGroup width items ⊆ items := by
  intro v on
  exact (mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp on))

omit [Fintype V] in
private theorem takeGroup_card (width : ℕ) (items : Finset V) :
    (takeGroup width items).card = min width items.card := by
  unfold takeGroup
  have simple : (List.take width (items.sort (· ≤ ·))).Nodup := (sort_nodup _ _).take
  rw [List.toFinset_card_of_nodup simple, List.length_take, length_sort]

/-- Retain all elements in a component that fits and a width-bounded
subset in each oversized component. -/
def selectLinkedGroups (members : Finset V) (G : Arcs V) (width : ℕ) : Finset V :=
  (linkedGroupComponents members G).biUnion (takeGroup width)

theorem selectLinkedGroups_subset (members : Finset V) (G : Arcs V) (width : ℕ) :
    selectLinkedGroups members G width ⊆ members := by
  intro v on
  obtain ⟨group, among, onGroup⟩ := mem_biUnion.mp on
  rw [← linkedGroupComponents_cover members G]
  exact mem_biUnion.mpr ⟨group, among, takeGroup_subset width group onGroup⟩

/-- The intersection with any original component has exactly the
smaller of its size and the width. -/
theorem selectLinkedGroups_component_card (members : Finset V) (G : Arcs V) (width : ℕ)
    {x : V} (on : x ∈ members) :
    (selectLinkedGroups members G width ∩ linkedGroupComponent members G x).card =
      min width (linkedGroupComponent members G x).card := by
  let group := linkedGroupComponent members G x
  have among : group ∈ linkedGroupComponents members G := mem_image_of_mem _ on
  have onlyHere : selectLinkedGroups members G width ∩ group = takeGroup width group := by
    ext v
    constructor
    · intro seen
      obtain ⟨selected, inGroup⟩ := mem_inter.mp seen
      obtain ⟨candidate, amongCandidates, member⟩ := mem_biUnion.mp selected
      have equal : candidate = group := by
        by_contra! different
        exact disjoint_left.mp (linkedGroupComponents_apart members G amongCandidates among different)
          (takeGroup_subset width candidate member) inGroup
      exact equal ▸ member
    · intro seen
      exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨group, among, seen⟩, takeGroup_subset width group seen⟩
  rw [onlyHere, takeGroup_card]

/-- The loss is exactly the sum of the excess sizes of the distinct
components. -/
theorem selectLinkedGroups_card_add_excess (members : Finset V) (G : Arcs V) (width : ℕ) :
    (selectLinkedGroups members G width).card +
      (∑ part ∈ linkedGroupComponents members G, (part.card - width)) = members.card := by
  let groups := linkedGroupComponents members G
  have apart : (↑groups : Set (Finset V)).PairwiseDisjoint (takeGroup width) :=
    fun a onA b onB different => (linkedGroupComponents_apart members G onA onB different).mono
      (takeGroup_subset width a) (takeGroup_subset width b)
  have kept : (selectLinkedGroups members G width).card = ∑ g ∈ groups, (takeGroup width g).card :=
    card_biUnion apart
  have total : members.card = ∑ g ∈ groups, g.card :=
    (congrArg card (linkedGroupComponents_cover members G)).symm.trans
      (card_biUnion (linkedGroupComponents_apart members G))
  rw [kept, total]
  change (∑ g ∈ groups, (takeGroup width g).card) + (∑ g ∈ groups, (g.card - width)) = _
  calc
    _ = ∑ g ∈ groups, ((takeGroup width g).card + (g.card - width)) :=
      (sum_add_distrib (s := groups) (f := fun g => (takeGroup width g).card)
        (g := fun g => g.card - width)).symm
    _ = _ := by
      apply sum_congr rfl
      intro group _
      rw [takeGroup_card]
      omega

end LinkedGroupSelection

end OnlineReachabilityPreservers
