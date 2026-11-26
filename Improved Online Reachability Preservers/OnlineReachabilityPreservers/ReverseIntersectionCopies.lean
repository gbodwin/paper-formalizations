import OnlineReachabilityPreservers.CommonPartitionCleaning

/-! Separate reverse intersections by coloring the occurrences of each vertex. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

section ReversePartners

variable {V : Type*} [DecidableEq V] {p : ℕ}

/-- At a shared vertex, direct an edge from the earlier row to a later
row if they reverse the order of that vertex and an earlier vertex of the
earlier row. -/
def LaterReversePartner (paths : Fin p → List V) (v : V) (a b : Fin p) : Prop :=
  a < b ∧ ∃ u, Before paths a u v ∧ Before paths b v u

/-- In a half-three-free family, an occurrence has at most one outgoing
reverse partner. -/
theorem laterReversePartner_unique {paths : Fin p → List V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {v : V} {a b c : Fin p} (ab : LaterReversePartner paths v a b)
    (ac : LaterReversePartner paths v a c) : b = c := by
  obtain ⟨ab, x, ax, bx⟩ := ab
  obtain ⟨ac, y, ay, cy⟩ := ac
  by_contra distinct
  by_cases same : x = y
  · subst y
    exact no_parallel_list_steps free (by omega) distinct bx cy
  rcases listBefore_total ax.1 ay.1 same with xy | yx
  · exact free three (threeListBridge ab.ne' (fun eq => distinct eq.symm) ac.ne' bx xy cy) ac
  · exact free three (threeListBridge ac.ne' distinct ab.ne' cy yx bx) ab

/-- Color each occurrence opposite its unique outgoing partner, if one
exists. Every chosen successor has a larger arrival index. -/
noncomputable def reversePartnerColor (paths : Fin p → List V) (v : V) (a : Fin p) : Bool := by
  classical
  exact if next : ∃ b, LaterReversePartner paths v a b then
    !(reversePartnerColor paths v (Classical.choose next))
  else false
termination_by p - a.val
decreasing_by
  have larger := (Classical.choose_spec next).1
  omega

theorem reversePartnerColor_ne {paths : Fin p → List V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {v : V} {a b : Fin p} (incident : LaterReversePartner paths v a b) :
    reversePartnerColor paths v a ≠ reversePartnerColor paths v b := by
  classical
  rw [reversePartnerColor]
  let next : ∃ j, LaterReversePartner paths v a j := ⟨b, incident⟩
  rw [dite_eq_left next, laterReversePartner_unique free three (Classical.choose_spec next) incident]
  cases reversePartnerColor paths v b <;> decide

/-- Give each occurrence its vertex's local color, retaining all rows and
the entire order within each row. -/
noncomputable def splitReverseIntersections (paths : Fin p → List V) (i : Fin p) :
    List (V ×ₗ Bool) :=
  (paths i).map fun v => toLex (v, reversePartnerColor paths v i)

theorem splitReverseIntersections_length (paths : Fin p → List V) (i : Fin p) :
    (splitReverseIntersections paths i).length = (paths i).length := List.length_map _

theorem splitReverseIntersections_project (paths : Fin p → List V) (i : Fin p) :
    (splitReverseIntersections paths i).map (fun v => (ofLex v).1) = paths i := by
  simp [splitReverseIntersections, List.map_map, Function.comp_def]

theorem splitReverseIntersections_simple {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (i : Fin p) : (splitReverseIntersections paths i).Nodup :=
  (simple i).map (fun _ _ eq => congrArg (fun v => (ofLex v).1) eq)

theorem splitReverseIntersections_mem {paths : Fin p → List V} {i : Fin p} {w : V ×ₗ Bool} :
    w ∈ splitReverseIntersections paths i ↔ (ofLex w).1 ∈ paths i ∧ reversePartnerColor paths (ofLex w).1 i = (ofLex w).2 := by
  constructor
  · intro member
    obtain ⟨v, onPath, rfl⟩ := List.mem_map.mp member
    exact ⟨onPath, rfl⟩
  · rintro ⟨onPath, color⟩
    exact List.mem_map.mpr ⟨(ofLex w).1, onPath, ofLex.injective (Prod.ext rfl color)⟩

theorem splitReverseIntersections_before {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) {i : Fin p} {x y : V ×ₗ Bool}
    (step : Before (splitReverseIntersections paths) i x y) : Before paths i (ofLex x).1 (ofLex y).1 := by
  have projected := listBefore_map (fun v => (ofLex v).1) ((splitReverseIntersections_project paths i).symm ▸ simple i) step
  simpa only [splitReverseIntersections_project] using projected

theorem splitReverseIntersections_fullFree {paths : Fin p → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) :
    BridgeFree (Before (splitReverseIntersections paths)) k :=
  free.split_list_vertices_any (fun v => (ofLex v).1) (splitReverseIntersections_before simple)

theorem splitReverseIntersections_halfFree {paths : Fin p → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (small : k ≤ 4) :
    HalfBridgeFree (Before (splitReverseIntersections paths)) k :=
  free.split_list_vertices_short small (fun v => (ofLex v).1) (splitReverseIntersections_before simple)

private theorem splitReverseIntersections_one_common_of_lt {paths : Fin p → List V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {a b : Fin p} (ab : a < b) {x y : V ×ₗ Bool}
    (xa : x ∈ splitReverseIntersections paths a) (xb : x ∈ splitReverseIntersections paths b)
    (ya : y ∈ splitReverseIntersections paths a) (yb : y ∈ splitReverseIntersections paths b) : x = y := by
  obtain ⟨xa, xca⟩ := splitReverseIntersections_mem.mp xa
  obtain ⟨xb, xcb⟩ := splitReverseIntersections_mem.mp xb
  obtain ⟨ya, yca⟩ := splitReverseIntersections_mem.mp ya
  obtain ⟨yb, ycb⟩ := splitReverseIntersections_mem.mp yb
  by_cases same : (ofLex x).1 = (ofLex y).1
  · exact ofLex.injective (Prod.ext same (xca.symm.trans (same ▸ yca)))
  have parallel {u w : V} (left : Before paths a u w) (right : Before paths b u w) : False :=
    no_parallel_list_steps free (by omega) ab.ne left right
  rcases listBefore_total xa ya same with ay | ax <;>
    rcases listBefore_total xb yb same with byx | bxy
  · exact (parallel ay byx).elim
  · exact (reversePartnerColor_ne free three ⟨ab, (ofLex x).1, ay, bxy⟩ (yca.trans ycb.symm)).elim
  · exact (reversePartnerColor_ne free three ⟨ab, (ofLex y).1, ax, byx⟩ (xca.trans xcb.symm)).elim
  · exact (parallel ax bxy).elim

/-- Distinct rows meet in at most one colored vertex. For a reversed
pair, the later common vertex of the earlier row has different colors. -/
theorem splitReverseIntersections_unique {paths : Fin p → List V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {a b : Fin p} (distinct : a ≠ b) {x y : V ×ₗ Bool}
    (xa : x ∈ splitReverseIntersections paths a) (xb : x ∈ splitReverseIntersections paths b)
    (ya : y ∈ splitReverseIntersections paths a) (yb : y ∈ splitReverseIntersections paths b) : x = y := by
  rcases lt_or_gt_of_ne distinct with earlier | later
  · exact splitReverseIntersections_one_common_of_lt free three earlier xa xb ya yb
  · exact splitReverseIntersections_one_common_of_lt free three later xb xa yb ya

/-- Keep the selected color at each original vertex, with no vertex or row
copies. Choices at different vertices may be made independently. -/
noncomputable def selectReversePartnerClass (paths : Fin p → List V) (choice : V → Bool)
    (i : Fin p) : List V :=
  (paths i).filter fun v => reversePartnerColor paths v i == choice v

theorem selectReversePartnerClass_sublist (paths : Fin p → List V) (choice : V → Bool) (i : Fin p) :
    (selectReversePartnerClass paths choice i).Sublist (paths i) :=
  List.filter_sublist

theorem selectReversePartnerClass_length_add (paths : Fin p → List V) (choice : V → Bool)
    (i : Fin p) :
    (selectReversePartnerClass paths choice i).length +
      (selectReversePartnerClass paths (fun v => !(choice v)) i).length = (paths i).length := by
  unfold selectReversePartnerClass
  have complement : (fun v => reversePartnerColor paths v i == !(choice v)) =
      (fun v => !(reversePartnerColor paths v i == choice v)) := by
    funext v
    cases reversePartnerColor paths v i <;> cases choice v <;> decide
  rw [complement]
  exact (List.length_eq_length_filter_add _).symm

private theorem selected_color_mem_copies {paths : Fin p → List V} {choice : V → Bool}
    {i : Fin p} {v : V} (member : v ∈ selectReversePartnerClass paths choice i) :
    toLex (v, choice v) ∈ splitReverseIntersections paths i := by
  obtain ⟨member, color⟩ := List.mem_filter.mp member
  exact splitReverseIntersections_mem.mpr ⟨member, eq_of_beq color⟩

/-- Each choice produces a family with unique intersections. The
complementary choice partitions the original incidences with it. -/
theorem selectReversePartnerClass_unique {paths : Fin p → List V} {k : ℕ}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) (choice : V → Bool)
    {a b : Fin p} (distinct : a ≠ b) {x y : V}
    (xa : x ∈ selectReversePartnerClass paths choice a) (xb : x ∈ selectReversePartnerClass paths choice b)
    (ya : y ∈ selectReversePartnerClass paths choice a) (yb : y ∈ selectReversePartnerClass paths choice b) :
    x = y :=
  congrArg (fun v => (ofLex v).1) (splitReverseIntersections_unique free three distinct
    (selected_color_mem_copies xa) (selected_color_mem_copies xb)
    (selected_color_mem_copies ya) (selected_color_mem_copies yb))

theorem selectReversePartnerClass_halfFree {paths : Fin p → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (choice : V → Bool) :
    HalfBridgeFree (Before (selectReversePartnerClass paths choice)) k := by
  intro s small bridge early
  exact free small (bridge.mapPaths id Function.injective_id (fun i _ _ step =>
    listBefore_of_sublist (simple i) (selectReversePartnerClass_sublist paths choice i) step)) early

theorem selectReversePartnerClass_fullFree {paths : Fin p → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (choice : V → Bool) :
    BridgeFree (Before (selectReversePartnerClass paths choice)) k := by
  intro s small
  exact ⟨fun bridge => (free small).false (bridge.mapPaths id Function.injective_id (fun i _ _ step =>
    listBefore_of_sublist (simple i) (selectReversePartnerClass_sublist paths choice i) step))⟩

end ReversePartners

section OccupiedCopies

variable {V : Type*} [LinearOrder V] {p : ℕ}

/-- Only vertices with an outgoing reverse-partner relation can occupy a
second copy. -/
noncomputable def reversePartnerVertices (paths : Fin p → List V) : Finset V := by
  classical
  exact (activeListVertices paths).filter fun v => ∃ a b, LaterReversePartner paths v a b

theorem splitReverseIntersections_support_le (paths : Fin p → List V) :
    (activeListVertices (splitReverseIntersections paths)).card ≤
      (activeListVertices paths).card + (reversePartnerVertices paths).card := by
  let embed (c : Bool) : V ↪ (V ×ₗ Bool) :=
    ⟨fun v => toLex (v, c), fun _ _ eq => congrArg (fun x => (ofLex x).1) eq⟩
  let base := (activeListVertices paths).map (embed false)
  let extra := (reversePartnerVertices paths).map (embed true)
  have contained : activeListVertices (splitReverseIntersections paths) ⊆ base ∪ extra := by
    intro w present
    obtain ⟨i, _, member⟩ := mem_biUnion.mp present
    obtain ⟨v, onPath, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have occupied : v ∈ activeListVertices paths :=
      mem_biUnion.mpr ⟨i, mem_univ _, List.mem_toFinset.mpr onPath⟩
    cases color : reversePartnerColor paths v i with
    | false => exact mem_union_left _ (mem_map.mpr ⟨v, occupied, rfl⟩)
    | true =>
      classical
      have partner : ∃ j, LaterReversePartner paths v i j := by
        by_contra h
        rw [reversePartnerColor, dite_eq_right h] at color
        contradiction
      have involved : v ∈ reversePartnerVertices paths :=
        mem_filter.mpr ⟨occupied, ⟨i, partner⟩⟩
      exact mem_union_right _ (mem_map.mpr ⟨v, involved, rfl⟩)
  calc
    _ ≤ (base ∪ extra).card := card_le_card contained
    _ ≤ base.card + extra.card := card_union_le _ _
    _ = _ := by simp [base, extra]

end OccupiedCopies

/-- First separate reverse intersections by vertex copies, with no loss
of incidences. Then perform the width splits on the family with unique
intersections. A bound on the number of vertices needing a second copy
leaves enough room for restriction and peeling at the original averages. -/
theorem regularization_list_frozen_of_reverse_copy_room {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (room : 3 * ((activeListVertices (splitReverseIntersections paths)).card +
      (∑ i, (paths i).length) / (4 * (∑ i, (paths i).length) / n)) ≤ 4 * n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4 * M / n
  let L := 4 * M / p
  let copies := splitReverseIntersections paths
  let active := activeListPaths copies
  have three : 3 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have halfFree : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have copySimple : ∀ i, (copies i).Nodup := splitReverseIntersections_simple simple
  have copyAllowed : localOrderAdmissible half k copies := by
    cases half
    · exact splitReverseIntersections_fullFree simple allowed
    · have small : k ≤ 4 := by
        rcases cutoff with rfl | ⟨_, impossible⟩
        · exact le_rfl
        · cases impossible
      exact splitReverseIntersections_halfFree simple halfFree small
  have unique : ∀ {a b x y}, a ≠ b → x ∈ active a → x ∈ active b →
      y ∈ active a → y ∈ active b → x = y :=
    restrictListPaths_unique (fun different => splitReverseIntersections_unique halfFree three different) _ _
  have activeSimple : ∀ i, (active i).Nodup := activeListPaths_simple copies copySimple
  have activeMass : (∑ i, (active i).length) = M := by
    rw [activeListPaths_mass copies copySimple]
    simp only [copies, splitReverseIntersections_length, M]
  have activeAllowed : localOrderAdmissible half k active := activeListPaths_admissible copies copySimple copyAllowed
  have afterAllowed : localOrderAdmissible half k (listRegularizedPaths active D L) := by
    rcases cutoff with rfl | ⟨rfl, rfl⟩
    · cases half
      · exact listRegularizedPaths_fullFree activeSimple unique activeAllowed D L
      · exact listRegularizedPaths_halfFree activeSimple unique activeAllowed D L
    · have four : BridgeFree (Before active) 4 := fun _ small => activeAllowed (small.trans (by decide))
      exact regularizedSix_bridge_free activeSimple (fun {_ _ _ _} => unique) four activeAllowed D L
  obtain ⟨Dpos, _, _⟩ := four_average_width hn dense
  obtain ⟨Lpos, pCopies, _⟩ := four_average_width hp long
  have baseP : Fintype.card (activeListIndices copies) ≤ p := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using card_le_univ (activeListIndices copies)
  obtain ⟨rawV, rawP⟩ := regularization_list_counts active activeSimple (D := D) (L := L) Dpos Lpos
  rw [activeMass] at rawV rawP
  have capV : 3 * Fintype.card (ListVertexBlockIndex active D) ≤ 4 * n := by
    simp only [Fintype.card_coe] at rawV
    exact (Nat.mul_le_mul_left 3 rawV).trans room
  have capP : 3 * Fintype.card (ListBlockIndex (splitListVertices active D) L) ≤ 4 * p := by
    change 3 * (M / L) ≤ p at pCopies
    omega
  obtain ⟨mass, length, degree⟩ := regularization_list_mass_caps active activeSimple D L Dpos Lpos
  rw [activeMass] at mass
  exact regularization_list_frozen_after_caps_with_room_of_mass (listRegularizedPaths active D L)
    (listRegularizedPaths_simple active activeSimple D L) afterAllowed hn hp dense long capV capP
    length degree mass.le (by rw [mass])

/-- One sixteenth of the vertex budget suffices for the reverse partners.
The low-mass case uses a separate full-bridge-free witness. -/
theorem regularization_list_frozen_of_sixteenth_reverse_vertices {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 16 * (reversePartnerVertices paths).card ≤ n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases sparse : M ≤ 3 * max n p
  · obtain ⟨n', vn, p', ip, clean, cleanSimple, cleanFree, lower, upper, caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long sparse
    refine ⟨n', vn, p', ip, clean, cleanSimple, ?_, by omega, upper, caps⟩
    cases half
    · exact cleanFree
    · exact cleanFree.halfFree
  · apply regularization_list_frozen_of_reverse_copy_room cutoff paths simple allowed hn hp dense long
    let D := 4 * M / n
    have nMax : n ≤ max n p := le_max_left _ _
    have width : 12 ≤ D := (Nat.le_div_iff_mul_le hn).mpr (by omega)
    have Dpos : 0 < D := by omega
    have floor := Nat.lt_mul_div_succ (4 * M) hn
    change 4 * M < n * (D + 1) at floor
    rw [Nat.mul_succ] at floor
    have minimum : n * 12 ≤ n * D := Nat.mul_le_mul_left n width
    have allowance : 48 * M ≤ 13 * (n * D) := by omega
    have count : 48 * (M / D) ≤ 13 * n := by
      apply (Nat.mul_le_mul_right_iff Dpos).mp
      calc
        _ = 48 * ((M / D) * D) := by ring
        _ ≤ 48 * M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
        _ ≤ 13 * (n * D) := allowance
        _ = _ := by ring
    have occupied : (activeListVertices paths).card ≤ n := by
      simpa only [Fintype.card_fin] using card_le_univ (activeListVertices paths)
    have copies := splitReverseIntersections_support_le paths
    change 3 * ((activeListVertices (splitReverseIntersections paths)).card + M / D) ≤ 4 * n
    omega

end OnlineReachabilityPreservers
