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

open scoped Sigma.Lex

/-- A simple restriction retaining at least two thirds of the mass
and meeting both original-width component tests gives a frozen witness
with the original caps and mass at least one eighteenth. -/
theorem regularization_list_frozen_of_short_return_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ v i, v ∈ kept i → (shortReturnCopyRowComponent kept k v i).card ≤ 4*M/n)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept k i v).card ≤ 4*M/p)
    (roomMass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let K := ∑ i, (kept i).length
  have upper : K ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  have simpleKept (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have freeKept : localOrderAdmissible half k kept := localOrderAdmissible_of_sublist simple sub free
  have connectedGroups : HasCappedShortReturnCopyPartition kept D k :=
    (hasCappedShortReturnCopyPartition_iff_component_room _ _ _).mpr degreeRoom
  obtain ⟨sizes, copies, copiesSimple, copiesFree, projected, degree, light, copiedRoom⟩ :=
    copies_of_short_return_groups simpleKept freeKept connectedGroups pathRoom
  let W := Σₗ v : Fin n, Fin (sizes v)
  have copyMass : (∑ i, (copies i).length) = K := by
    apply sum_congr rfl
    intro i _
    have eq : (copies i).map (fun v : W => v.fst) = kept i := projected i
    simpa only [List.length_map] using congrArg List.length eq
  refine regularization_list_frozen_after_grouped_width_splits_of_mass copies copiesSimple copiesFree
    hn hp dense long (copyMass.trans_le upper) degree light copiedRoom ?_
  dsimp only
  rw [copyMass]
  intro retained lostV lostI paid lossV lossI
  have charge {q lost : ℕ} (positive : 0 < q)
      (bound : 4*(((4*M/q)/2 + 1)*q)*lost ≤ K^2) : 8*M*lost ≤ K^2 :=
    (show 8*M*lost = 4*(2*M)*lost by ring).le.trans
      ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (half_average_width_capacity positive))).trans bound)
  have both : 8*M*(lostV+lostI) ≤ 2*K^2 := by
    rw [Nat.mul_add, two_mul (K^2)]
    exact add_le_add (charge hn lossV) (charge hp lossI)
  have sumLoss : 4*M*(lostV+lostI) ≤ K^2 := by
    rw [show 8*M*(lostV+lostI) = 2*(4*M*(lostV+lostI)) by ring] at both
    omega
  have paidNat : 4*M*K ≤ 4*M*retained + K^2 := calc
    _ ≤ 4*M*(retained+(lostV+lostI)) := Nat.mul_le_mul_left _ paid
    _ = 4*M*retained+4*M*(lostV+lostI) := by ring
    _ ≤ _ := Nat.add_le_add_left sumLoss _
  have paidInt : 4*(M:ℤ)*K ≤ 4*(M:ℤ)*retained + (K:ℤ)^2 := by exact_mod_cast paidNat
  have lo : 2*(M:ℤ) ≤ 3*(K:ℤ) := by exact_mod_cast roomMass
  have hi : (K:ℤ) ≤ M := by exact_mod_cast upper
  have factor : 0 ≤ (3*(K:ℤ)-2*M)*(10*(M:ℤ)-3*K) :=
    mul_nonneg (by omega) (by omega)
  have sufficient : (20*M)*M ≤ (36*retained)*M := by
    exact_mod_cast (show (20*(M:ℤ))*M ≤ (36*(retained:ℤ))*M by nlinarith only [factor, paidInt])
  exact (Nat.mul_le_mul_right_iff (hn.trans_le dense)).mp sufficient

/-- At the original widths, deleting at most one third of the incidences
in oversized components still leaves a frozen witness of mass at least
one eighteenth of the original mass. -/
theorem regularization_list_frozen_of_small_short_return_overflow {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (overflow : let M := ∑ i, (rows i).length
      3*shortReturnComponentOverflowMass rows (4*M/n) (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let kept := pruneOversizedShortReturnComponents rows D L k
  have total : (∑ i, (kept i).length) + shortReturnComponentOverflowMass rows D L k = M :=
    pruneOversizedShortReturnComponents_mass rows D L k
  have room := pruneOversizedShortReturnComponents_room rows simple D L k
  change 3*shortReturnComponentOverflowMass rows D L k ≤ M at overflow
  exact regularization_list_frozen_of_short_return_restriction rows simple free hn hp dense long kept
    (pruneOversizedShortReturnComponents_sublist rows D L k) room.1 room.2 (by omega)

end OnlineReachabilityPreservers
