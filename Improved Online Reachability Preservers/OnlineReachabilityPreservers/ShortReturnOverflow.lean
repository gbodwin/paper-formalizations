import OnlineReachabilityPreservers.ShortReturnVertexPacking

/-! Delete incidences in oversized return components before packing. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem linkedGroupComponent_mono {V : Type*} [LinearOrder V] [Fintype V]
    {smallMembers largeMembers : Finset V} {smallGraph largeGraph : Arcs V}
    (members : smallMembers ⊆ largeMembers) (arcs : smallGraph ⊆ largeGraph) (x : V) :
    linkedGroupComponent smallMembers smallGraph x ⊆ linkedGroupComponent largeMembers largeGraph x := by
  intro y on
  obtain ⟨inSmall, equal⟩ := mem_filter.mp on
  have connected := componentLabel_eq.mp equal
  exact mem_filter.mpr ⟨members inSmall,
    componentLabel_eq.mpr ⟨reach_mono arcs connected.1, reach_mono arcs connected.2⟩⟩

section Sublist

variable {I V : Type*} [Fintype I] [LinearOrder V] [Fintype V]
variable {rows kept : I → List V}

private theorem listPiecePrecedenceGraph_subset_of_sublist
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) :
    listPiecePrecedenceGraph kept ⊆ listPiecePrecedenceGraph rows := by
  rintro ⟨x, y⟩ on
  obtain ⟨i, step⟩ := listPiecePrecedenceGraph_edge.mp on
  exact listPiecePrecedenceGraph_edge.mpr ⟨i, listBefore_of_sublist (simple i) (sub i) step⟩

private theorem reachIn_listPiecePrecedenceGraph_of_sublist
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i))
    {x y : V} {depth : ℕ} (member : x ∈ reachIn (listPiecePrecedenceGraph kept) y depth) :
    x ∈ reachIn (listPiecePrecedenceGraph rows) y depth :=
  project_reachIn id (fun {_ _} arc => listPiecePrecedenceGraph_subset_of_sublist simple sub arc) _ member

/-- Sublist restriction cannot enlarge a short-return group on a row. -/
theorem shortReturnRowComponent_subset_of_sublist
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i))
    (cutoff : ℕ) (i : I) (x : V) :
    shortReturnRowComponent kept cutoff i x ⊆ shortReturnRowComponent rows cutoff i x := by
  have member : (kept i).toFinset ⊆ (rows i).toFinset :=
    fun _ on => List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp on))
  refine linkedGroupComponent_mono member ?_ x
  have lifts ⦃a b : V⦄ (linked : Before kept i a b ∧
      b ∈ reachIn (listPiecePrecedenceGraph kept) a (cutoff - 3)) :
      Before rows i a b ∧ b ∈ reachIn (listPiecePrecedenceGraph rows) a (cutoff - 3) :=
    ⟨listBefore_of_sublist (simple i) (sub i) linked.1,
      reachIn_listPiecePrecedenceGraph_of_sublist simple sub linked.2⟩
  rintro ⟨a, b⟩ on
  exact shortReturnRowGraph_edge.mpr ((shortReturnRowGraph_edge.mp on).imp (fun h => lifts h) (fun h => lifts h))

variable [LinearOrder I]

/-- Sublist restriction cannot enlarge a short-return group of
incident rows at a vertex. -/
theorem shortReturnCopyRowComponent_subset_of_sublist
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i))
    (cutoff : ℕ) (vertex : V) (i : I) :
    shortReturnCopyRowComponent kept cutoff vertex i ⊆ shortReturnCopyRowComponent rows cutoff vertex i := by
  let oldMarks (j : I) := (rows j).toFinset
  let newMarks (j : I) := (kept j).toFinset
  have member : occurrences newMarks vertex ⊆ occurrences oldMarks vertex := by
    intro j on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub j).subset
      (List.mem_toFinset.mp ((mem_occurrences (marks := newMarks)).mp on))))
  refine linkedGroupComponent_mono member ?_ i
  have lifts ⦃a b : I⦄ (linked : ShortReturnCopyRowPair kept cutoff vertex a b) :
      ShortReturnCopyRowPair rows cutoff vertex a b := by
    obtain ⟨apart, x, y, first, last, back⟩ := linked
    exact ⟨apart, x, y, listBefore_of_sublist (simple a) (sub a) first,
      listBefore_of_sublist (simple b) (sub b) last,
      reachIn_listPiecePrecedenceGraph_of_sublist simple sub back⟩
  rintro ⟨a, b⟩ on
  exact shortReturnCopyRowGraph_edge.mpr ((shortReturnCopyRowGraph_edge.mp on).imp (fun h => lifts h) (fun h => lifts h))

end Sublist

private def shortReturnIncidenceFits {n p : ℕ} (rows : Fin p → List (Fin n)) (D L cutoff : ℕ)
    (i : Fin p) (v : Fin n) : Bool :=
  decide ((shortReturnCopyRowComponent rows cutoff v i).card ≤ D ∧
    (shortReturnRowComponent rows cutoff i v).card ≤ L)

/-- Keep every incidence whose two original components fit their widths. -/
def pruneOversizedShortReturnComponents {n p : ℕ} (rows : Fin p → List (Fin n)) (D L cutoff : ℕ)
    (i : Fin p) : List (Fin n) :=
  (rows i).filter (shortReturnIncidenceFits rows D L cutoff i)

/-- Count the removed incidences once, including those with two
oversized components. -/
def shortReturnComponentOverflowMass {n p : ℕ} (rows : Fin p → List (Fin n)) (D L cutoff : ℕ) : ℕ :=
  ∑ i, ((rows i).filter (fun v => !(shortReturnIncidenceFits rows D L cutoff i v))).length

theorem pruneOversizedShortReturnComponents_sublist {n p : ℕ} (rows : Fin p → List (Fin n))
    (D L cutoff : ℕ) (i : Fin p) : (pruneOversizedShortReturnComponents rows D L cutoff i).Sublist (rows i) :=
  List.filter_sublist

theorem pruneOversizedShortReturnComponents_mass {n p : ℕ} (rows : Fin p → List (Fin n)) (D L cutoff : ℕ) :
    (∑ i, (pruneOversizedShortReturnComponents rows D L cutoff i).length) +
      shortReturnComponentOverflowMass rows D L cutoff = ∑ i, (rows i).length := by
  unfold shortReturnComponentOverflowMass pruneOversizedShortReturnComponents
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => (List.length_eq_length_filter_add _).symm)

/-- Removing the oversized incidences ensures both component-width
bounds on the restricted family. -/
theorem pruneOversizedShortReturnComponents_room {n p : ℕ} (rows : Fin p → List (Fin n))
    (simple : ∀ i, (rows i).Nodup) (D L cutoff : ℕ) :
    let kept := pruneOversizedShortReturnComponents rows D L cutoff
    (∀ v i, v ∈ kept i → (shortReturnCopyRowComponent kept cutoff v i).card ≤ D) ∧
      (∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept cutoff i v).card ≤ L) := by
  let kept := pruneOversizedShortReturnComponents rows D L cutoff
  have sub := pruneOversizedShortReturnComponents_sublist rows D L cutoff
  have fitting {i : Fin p} {v : Fin n} (on : v ∈ kept i) :
      (shortReturnCopyRowComponent rows cutoff v i).card ≤ D ∧
      (shortReturnRowComponent rows cutoff i v).card ≤ L := by
    exact of_decide_eq_true (List.mem_filter.mp on).2
  exact ⟨fun v i on => (card_le_card (shortReturnCopyRowComponent_subset_of_sublist simple sub cutoff v i)).trans (fitting on).1,
    fun i v on => (card_le_card (shortReturnRowComponent_subset_of_sublist simple sub cutoff i v)).trans (fitting on).2⟩

end OnlineReachabilityPreservers
