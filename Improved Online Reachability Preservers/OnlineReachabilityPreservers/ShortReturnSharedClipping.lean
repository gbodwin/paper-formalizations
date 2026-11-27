import OnlineReachabilityPreservers.SharedCapacityClipping
import OnlineReachabilityPreservers.ShortReturnComponentClipping

/-! Apply shared deletions to the original short-return components. -/

namespace OnlineReachabilityPreservers

open Finset

variable {I V : Type*} [LinearOrder I] [LinearOrder V] [Fintype I] [Fintype V]

/-- Label an incidence by its original vertex and degree component. -/
def shortReturnDegreeClass (rows : I → List V) (cutoff : ℕ) (incidence : I × V) : V × I :=
  (incidence.2, componentLabel (shortReturnCopyRowGraph rows cutoff incidence.2) incidence.1)

/-- Label an incidence by its original row and path component. -/
def shortReturnPathClass (rows : I → List V) (cutoff : ℕ) (incidence : I × V) : I × V :=
  (incidence.1, componentLabel (shortReturnRowGraph rows cutoff incidence.1) incidence.2)

private theorem component_fiber_excess {A : Type*} [LinearOrder A] [Fintype A]
    (members : Finset A) (G : Arcs A) (width : ℕ) :
    FiberClipping.totalExcess members (componentLabel G) width =
      ∑ g ∈ linkedGroupComponents members G, (g.card-width) := by
  let label := componentLabel G
  let fiber (c : A) := members.filter fun x => label x = c
  have same : (members.image label).image fiber = linkedGroupComponents members G := by
    rw [image_image]
    rfl
  have distinct : Set.InjOn fiber (members.image label : Set A) := by
    intro a inA b _ equal
    obtain ⟨x, on, labelX⟩ := mem_image.mp inA
    have own : x ∈ fiber a := mem_filter.mpr ⟨on, labelX⟩
    have inB : x ∈ fiber b := equal ▸ own
    have labelB : label x = b := (mem_filter.mp inB).2
    exact labelX.symm.trans labelB
  calc
    _ = ∑ c ∈ members.image label, ((fiber c).card-width) := by
      symm
      apply sum_subset (subset_univ _)
      intro c _ absent
      have empty : fiber c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x on
        obtain ⟨present, atLabel⟩ := mem_filter.mp on
        exact absent (mem_image.mpr ⟨x, present, atLabel⟩)
      simp [empty]
    _ = ∑ g ∈ (members.image label).image fiber, (g.card-width) :=
      (sum_image (f := fun g : Finset A => g.card-width)
        (fun _ ha _ hb eq => distinct ha hb eq)).symm
    _ = _ := by rw [same]

private theorem mem_degree_class {rows kept : I → List V} {cutoff : ℕ} {v : V} {c : I}
    {e : I × V} :
    e ∈ (pieceIncidences kept univ).filter (fun a => shortReturnDegreeClass rows cutoff a = (v,c)) ↔
      e.2 = v ∧ v ∈ kept e.1 ∧ componentLabel (shortReturnCopyRowGraph rows cutoff v) e.1 = c := by
  obtain ⟨i, w⟩ := e
  simp only [mem_filter, mem_pieceIncidences, mem_univ, true_and, shortReturnDegreeClass, Prod.mk.injEq]
  constructor
  · rintro ⟨on, rfl, same⟩
    exact ⟨rfl, on, same⟩
  · rintro ⟨rfl, on, same⟩
    exact ⟨on, rfl, same⟩

private theorem mem_path_class {rows kept : I → List V} {cutoff : ℕ} {i : I} {c : V}
    {e : I × V} :
    e ∈ (pieceIncidences kept univ).filter (fun a => shortReturnPathClass rows cutoff a = (i,c)) ↔
      e.1 = i ∧ e.2 ∈ kept i ∧ componentLabel (shortReturnRowGraph rows cutoff i) e.2 = c := by
  obtain ⟨j, v⟩ := e
  simp only [mem_filter, mem_pieceIncidences, mem_univ, true_and, shortReturnPathClass, Prod.mk.injEq]
  constructor
  · rintro ⟨on, rfl, same⟩
    exact ⟨rfl, on, same⟩
  · rintro ⟨rfl, on, same⟩
    exact ⟨on, rfl, same⟩

theorem shortReturnDegreeClass_card (rows kept : I → List V) (cutoff : ℕ) (v : V) (c : I) :
    ((pieceIncidences kept univ).filter (fun a => shortReturnDegreeClass rows cutoff a = (v,c))).card =
      ((occurrences (fun i => (kept i).toFinset) v).filter
        fun i => componentLabel (shortReturnCopyRowGraph rows cutoff v) i = c).card := by
  apply card_bij (fun e _ => e.1)
  · intro e on
    obtain ⟨_, present, same⟩ := mem_degree_class.mp on
    exact mem_filter.mpr ⟨mem_occurrences.mpr (List.mem_toFinset.mpr present), same⟩
  · intro a onA b onB same
    exact Prod.ext same ((mem_degree_class.mp onA).1.trans (mem_degree_class.mp onB).1.symm)
  · intro i on
    obtain ⟨present, same⟩ := mem_filter.mp on
    exact ⟨(i,v), mem_degree_class.mpr
      ⟨rfl, List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (kept j).toFinset)).mp present), same⟩, rfl⟩

theorem shortReturnPathClass_card (rows kept : I → List V) (cutoff : ℕ) (i : I) (c : V) :
    ((pieceIncidences kept univ).filter (fun a => shortReturnPathClass rows cutoff a = (i,c))).card =
      ((kept i).toFinset.filter fun v => componentLabel (shortReturnRowGraph rows cutoff i) v = c).card := by
  apply card_bij (fun e _ => e.2)
  · intro e on
    obtain ⟨_, present, same⟩ := mem_path_class.mp on
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr present, same⟩
  · intro a onA b onB same
    exact Prod.ext ((mem_path_class.mp onA).1.trans (mem_path_class.mp onB).1.symm) same
  · intro v on
    obtain ⟨present, same⟩ := mem_filter.mp on
    exact ⟨(i,v), mem_path_class.mpr ⟨rfl, List.mem_toFinset.mp present, same⟩, rfl⟩

/-- The degree-class overflow is exactly the sum of the original degree
component excesses. -/
theorem shortReturnDegreeClass_totalExcess (rows : I → List V) (width cutoff : ℕ) :
    FiberClipping.totalExcess (pieceIncidences rows univ) (shortReturnDegreeClass rows cutoff) width =
      shortReturnDegreeExcessMass rows width cutoff := by
  rw [FiberClipping.totalExcess, Fintype.sum_prod_type]
  unfold shortReturnDegreeExcessMass
  apply sum_congr rfl
  intro v _
  simp only [FiberClipping.excess, shortReturnDegreeClass_card]
  exact component_fiber_excess (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v) width

/-- The path-class overflow is exactly the sum of the original path
component excesses. -/
theorem shortReturnPathClass_totalExcess (rows : I → List V) (width cutoff : ℕ) :
    FiberClipping.totalExcess (pieceIncidences rows univ) (shortReturnPathClass rows cutoff) width =
      shortReturnPathExcessMass rows width cutoff := by
  rw [FiberClipping.totalExcess, Fintype.sum_prod_type]
  unfold shortReturnPathExcessMass
  apply sum_congr rfl
  intro i _
  simp only [FiberClipping.excess, shortReturnPathClass_card]
  exact component_fiber_excess (rows i).toFinset (shortReturnRowGraph rows cutoff i) width

/-- A shared set is drawn from the original incidences and uses at most
the original excess in every degree class and every path class. -/
def ShortReturnSharedDeletion (rows : I → List V) (D L cutoff : ℕ) (shared : Finset (I × V)) : Prop :=
  let items := pieceIncidences rows univ
  let degree := shortReturnDegreeClass rows cutoff
  let path := shortReturnPathClass rows cutoff
  shared ⊆ items ∧
    (∀ c, (shared.filter fun a => degree a = c).card ≤ FiberClipping.excess items degree D c) ∧
    (∀ c, (shared.filter fun a => path a = c).card ≤ FiberClipping.excess items path L c)

theorem pieceIncidences_erase (rows : I → List V) (deleted : Finset (I × V)) :
    pieceIncidences (erasePieceIncidences rows deleted) univ = pieceIncidences rows univ \ deleted := by
  ext a
  simp [mem_pieceIncidences, mem_erasePieceIncidences]

private theorem short_return_component_room_of_class_caps
    (rows kept : I → List V) (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i))
    (D L cutoff : ℕ)
    (fitsDegree : ∀ c, ((pieceIncidences kept univ).filter (fun a => shortReturnDegreeClass rows cutoff a = c)).card ≤ D)
    (fitsPath : ∀ c, ((pieceIncidences kept univ).filter (fun a => shortReturnPathClass rows cutoff a = c)).card ≤ L) :
    (∀ v i, (shortReturnCopyRowComponent kept cutoff v i).card ≤ D) ∧
      (∀ i v, (shortReturnRowComponent kept cutoff i v).card ≤ L) := by
  constructor
  · intro v i
    let label := componentLabel (shortReturnCopyRowGraph rows cutoff v)
    have limit := fitsDegree (v, label i)
    rw [shortReturnDegreeClass_card] at limit
    refine (card_le_card ?_).trans limit
    intro j on
    have earlier := shortReturnCopyRowComponent_subset_of_sublist simple sub cutoff v i on
    exact mem_filter.mpr ⟨(mem_filter.mp on).1, (mem_filter.mp earlier).2⟩
  · intro i v
    let label := componentLabel (shortReturnRowGraph rows cutoff i)
    have limit := fitsPath (i, label v)
    rw [shortReturnPathClass_card] at limit
    refine (card_le_card ?_).trans limit
    intro w on
    have earlier := shortReturnRowComponent_subset_of_sublist simple sub cutoff i v on
    exact mem_filter.mpr ⟨(mem_filter.mp on).1, (mem_filter.mp earlier).2⟩

/-- A shared deletion set reduces the combined cost of fitting the
original degree and path components. If the resulting budget is at
most one third of the original mass, frozen cleaning keeps at least
one eighteenth at the same cutoff and original caps. -/
theorem regularization_list_frozen_of_shared_short_return_deletions {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (shared : Finset (Fin p × Fin n))
    (fits : let M := ∑ i, (rows i).length; ShortReturnSharedDeletion rows (4*M/n) (4*M/p) k shared)
    (paid : let M := ∑ i, (rows i).length
      shortReturnDegreeExcessMass rows (4*M/n) k + shortReturnPathExcessMass rows (4*M/p) k ≤
        M/3 + shared.card) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let vertices := shortReturnDegreeClass rows k
  let paths := shortReturnPathClass rows k
  let incidences := pieceIncidences rows univ
  have payBoth : FiberClipping.totalExcess incidences vertices D +
      FiberClipping.totalExcess incidences paths L ≤ M/3 + shared.card := by
    rw [shortReturnDegreeClass_totalExcess, shortReturnPathClass_totalExcess]
    exact paid
  obtain ⟨inside, fitV, fitI⟩ := fits
  obtain ⟨deleted, subDeleted, cost, capsV, capsI⟩ :=
    (FiberClipping.exists_capped_deletion_iff incidences vertices paths D L (M/3)).mpr
      ⟨shared, inside, payBoth, fitV, fitI⟩
  let kept := erasePieceIncidences rows deleted
  have sub := erasePieceIncidences_sublist rows deleted
  have keepSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keepIncidence : pieceIncidences kept univ = incidences \ deleted :=
    pieceIncidences_erase rows deleted
  have total : (∑ i, (kept i).length) + deleted.card = M := by
    rw [← pieceIncidences_card keepSimple univ, keepIncidence,
      card_sdiff_add_card_eq_card subDeleted]
    exact pieceIncidences_card simple univ
  have room := short_return_component_room_of_class_caps rows kept simple sub D L k
    (fun c => keepIncidence.symm ▸ capsV c) (fun c => keepIncidence.symm ▸ capsI c)
  exact regularization_list_frozen_of_short_return_restriction rows simple free hn hp dense long kept sub
    (fun v i _ => room.1 v i) (fun i v _ => room.2 i v) (by omega)

/-- The shared deletion certificate also gives a distinct nonempty
witness for feasible literal input at cutoff at least two. -/
theorem regularization_list_frozen_distinct_of_shared_short_return_deletions {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (shared : Finset (Fin p × Fin n))
    (fits : let M := ∑ i, (rows i).length; ShortReturnSharedDeletion rows (4*M/n) (4*M/p) k shared)
    (paid : let M := ∑ i, (rows i).length
      shortReturnDegreeExcessMass rows (4*M/n) k + shortReturnPathExcessMass rows (4*M/p) k ≤
        M/3 + shared.card) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      localOrderAdmissible half k clean ∧ M ≤ 18*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (retention := 18) rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  exact fun long => regularization_list_frozen_of_shared_short_return_deletions
    rows simple free hn hp dense long shared fits paid

end OnlineReachabilityPreservers
