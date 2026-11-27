import OnlineReachabilityPreservers.ShortReturnPiecePacking

/-! The connected short-return groups are the smallest feasible pieces. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

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
  (rows i).toFinset.filter fun y =>
    componentLabel (shortReturnRowGraph rows cutoff i) y =
      componentLabel (shortReturnRowGraph rows cutoff i) x

private theorem rowComponent_partition {rows : I → List V} {width cutoff : ℕ} (i : I)
    (room : ∀ x ∈ rows i, (shortReturnRowComponent rows cutoff i x).card ≤ width) :
    CappedPathPartition (rows i).toFinset
      (fun x y => Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x (cutoff - 3))
      width ((rows i).toFinset.image (shortReturnRowComponent rows cutoff i)) := by
  let C := shortReturnRowComponent rows cutoff i
  let groups := (rows i).toFinset.image C
  have present {x : V} (on : x ∈ rows i) : x ∈ C x := by simp [C, shortReturnRowComponent, on]
  have label {x y : V} (on : y ∈ C x) :
      componentLabel (shortReturnRowGraph rows cutoff i) y =
        componentLabel (shortReturnRowGraph rows cutoff i) x := (mem_filter.mp on).2
  have same {x y : V} (eq : componentLabel (shortReturnRowGraph rows cutoff i) x =
      componentLabel (shortReturnRowGraph rows cutoff i) y) : C x = C y := by
    ext v
    simp only [C, shortReturnRowComponent, mem_filter, List.mem_toFinset, eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro on
      obtain ⟨group, among, within⟩ := mem_biUnion.mp on
      obtain ⟨center, _, rfl⟩ := mem_image.mp among
      exact (mem_filter.mp within).1
    · intro on
      exact mem_biUnion.mpr ⟨C x, mem_image_of_mem C on, present (List.mem_toFinset.mp on)⟩
  · intro a onA b onB apart
    obtain ⟨x, _, rfl⟩ := mem_image.mp onA
    obtain ⟨y, _, rfl⟩ := mem_image.mp onB
    exact disjoint_left.mpr fun _ inX inY => apart (same ((label inX).symm.trans (label inY)))
  · intro group among
    obtain ⟨x, on, rfl⟩ := mem_image.mp among
    exact ⟨x, present (List.mem_toFinset.mp on)⟩
  · intro group among
    obtain ⟨x, on, rfl⟩ := mem_image.mp among
    exact room x (List.mem_toFinset.mp on)
  · intro x y linked
    have xy := shortReturnRowGraph_edge.mpr (Or.inl linked)
    have yx := shortReturnRowGraph_edge.mpr (Or.inr linked)
    have sameComponent : SameComponent (shortReturnRowGraph rows cutoff i) y x :=
      ⟨.single yx, .single xy⟩
    have xOn : x ∈ rows i := linked.1.1
    have yOn : y ∈ rows i := linked.1.2.1
    exact ⟨C x, mem_image_of_mem C (List.mem_toFinset.mpr xOn), present xOn,
      mem_filter.mpr ⟨List.mem_toFinset.mpr yOn, componentLabel_eq.mpr sameComponent⟩⟩

private theorem rowComponent_fits_of_partition {rows : I → List V} {width cutoff : ℕ}
    (i : I) {groups : Finset (Finset V)}
    (partition : CappedPathPartition (rows i).toFinset
      (fun x y => Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x (cutoff - 3))
      width groups) (x : V) (on : x ∈ rows i) :
    (shortReturnRowComponent rows cutoff i x).card ≤ width := by
  have covered : x ∈ groups.biUnion id := partition.cover.symm ▸ List.mem_toFinset.mpr on
  obtain ⟨group, hasGroup, inGroup⟩ := mem_biUnion.mp covered
  have step {a b : V} (edge : Edge (shortReturnRowGraph rows cutoff i) a b)
      (previous : a ∈ group) : b ∈ group := by
    have together : ∃ h ∈ groups, a ∈ h ∧ b ∈ h := by
      rcases shortReturnRowGraph_edge.mp edge with forward | reverse
      · exact partition.together forward
      · obtain ⟨h, among, right, left⟩ := partition.together reverse
        exact ⟨h, among, left, right⟩
    obtain ⟨h, among, left, right⟩ := together
    have eq : h = group := by
      by_contra! different
      exact disjoint_left.mp (partition.apart among hasGroup different) left previous
    exact eq ▸ right
  have all : shortReturnRowComponent rows cutoff i x ⊆ group := by
    intro y member
    have reachable := (componentLabel_eq.mp (mem_filter.mp member).2).2
    clear member
    induction reachable with
    | refl => exact inGroup
    | tail _ edge ih => exact step edge ih
  exact (card_le_card all).trans (partition.fits group hasGroup)

/-- There is a partition into width-bounded pieces respecting every
short-return pair exactly when each connected group fits the width. -/
theorem hasCappedShortReturnPartition_iff_component_room
    (rows : I → List V) (width cutoff : ℕ) :
    HasCappedShortReturnPartition rows width cutoff ↔
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows cutoff i x).card ≤ width := by
  constructor
  · intro partition i x on
    obtain ⟨groups, valid⟩ := partition i
    exact rowComponent_fits_of_partition i valid x on
  · intro room i
    exact ⟨_, rowComponent_partition i (room i)⟩

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

end OnlineReachabilityPreservers
