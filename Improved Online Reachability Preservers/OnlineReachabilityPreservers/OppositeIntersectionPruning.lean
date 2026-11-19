import OnlineReachabilityPreservers.CyclicIntersections

/-! Lemma 20 of Bridge Girth in arrival order, with the half-bridge condition. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [DecidableEq V]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Taking a subsequence of a simple path preserves its local comparisons. -/
theorem listBefore_of_sublist {I : Type*} {paths cut : I → List V} {i : I} {u v : V}
    (simple : (paths i).Nodup) (sub : List.Sublist (cut i) (paths i)) (step : ListBefore cut i u v) :
    ListBefore paths i u v := by
  obtain ⟨hu, hv, less⟩ := step
  have ordered : (paths i).Pairwise (fun a b => (paths i).idxOf a < (paths i).idxOf b) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb ab
    simpa only [simple.idxOf_getElem] using ab
  have follows := List.Pairwise.sublist sub ordered
  have au := List.idxOf_lt_length_of_mem hu
  have av := List.idxOf_lt_length_of_mem hv
  have forward := List.pairwise_iff_getElem.mp follows ((cut i).idxOf u) ((cut i).idxOf v) au av less
  rw [List.getElem_idxOf au, List.getElem_idxOf av] at forward
  exact ⟨sub.subset hu, sub.subset hv, forward⟩

/-- Keep a vertex unless an earlier retained path witnesses an opposite
order with a successor in the original current path. -/
noncomputable def removeOppositeIntersections {p : ℕ} (paths : Fin p → List V) (i : Fin p) : List V := by
  classical
  exact (paths i).filter fun v => decide (¬ ∃ j : {j : Fin p // j < i}, ∃ u,
    ListBefore paths i v u ∧
      let prior := removeOppositeIntersections paths j.val
      u ∈ prior ∧ v ∈ prior ∧ prior.idxOf u < prior.idxOf v)
termination_by i.val
decreasing_by all_goals exact (‹{j : Fin p // j < i}›).property

theorem removeOppositeIntersections_mem {p : ℕ} (paths : Fin p → List V) (i : Fin p) (v : V) :
    v ∈ removeOppositeIntersections paths i ↔ v ∈ paths i ∧
      ¬ ∃ j : Fin p, j < i ∧ ∃ u, ListBefore paths i v u ∧
        ListBefore (removeOppositeIntersections paths) j u v := by
  classical
  rw [removeOppositeIntersections, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨inside, no⟩
    exact ⟨inside, fun ⟨j, hj, u, left, right⟩ => no ⟨⟨j, hj⟩, u, left, right⟩⟩
  · rintro ⟨inside, no⟩
    exact ⟨inside, fun ⟨j, u, left, right⟩ => no ⟨j.val, j.property, u, left, right⟩⟩

theorem removeOppositeIntersections_sublist {p : ℕ} (paths : Fin p → List V) (i : Fin p) :
    List.Sublist (removeOppositeIntersections paths i) (paths i) := by
  rw [removeOppositeIntersections]
  exact List.filter_sublist

theorem removeOppositeIntersections_before {p : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) {i : Fin p} {x y : V}
    (step : ListBefore (removeOppositeIntersections paths) i x y) : ListBefore paths i x y :=
  listBefore_of_sublist (simple i) (removeOppositeIntersections_sublist paths i) step

theorem removeOppositeIntersections_halfFree {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) :
    HalfBridgeFree (ListBefore (removeOppositeIntersections paths)) k := by
  intro s hs b earlier
  exact free hs (b.mapPaths id Function.injective_id (fun _ _ _ h => removeOppositeIntersections_before simple h)) earlier

theorem removeOppositeIntersections_fullFree {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) k) :
    BridgeFree (ListBefore (removeOppositeIntersections paths)) k := by
  intro s hs
  exact ⟨fun b => (free hs).false
    (b.mapPaths id Function.injective_id (fun _ _ _ h => removeOppositeIntersections_before simple h))⟩

private theorem removeOppositeIntersections_no_reverse {p : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) {a b : Fin p} (earlier : a < b) {x y : V}
    (one : ListBefore (removeOppositeIntersections paths) a x y)
    (two : ListBefore (removeOppositeIntersections paths) b y x) : False :=
  (removeOppositeIntersections_mem paths b y).mp two.1 |>.2
    ⟨a, earlier, x, removeOppositeIntersections_before simple two, one⟩

/-- After pruning, distinct paths share at most one vertex. -/
theorem removeOppositeIntersections_unique {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (large : 2 ≤ k)
    {a b : Fin p} (ab : a ≠ b) {x y : V}
    (xa : x ∈ removeOppositeIntersections paths a) (xb : x ∈ removeOppositeIntersections paths b)
    (ya : y ∈ removeOppositeIntersections paths a) (yb : y ∈ removeOppositeIntersections paths b) : x = y := by
  have noParallel {u w : V} (one : ListBefore (removeOppositeIntersections paths) a u w)
      (two : ListBefore (removeOppositeIntersections paths) b u w) : False :=
    no_parallel_list_steps (removeOppositeIntersections_halfFree simple free) large ab one two
  have noReverse {x y : V} (one : ListBefore (removeOppositeIntersections paths) a x y)
      (two : ListBefore (removeOppositeIntersections paths) b y x) : False := by
    rcases lt_or_gt_of_ne ab with first | second
    · exact removeOppositeIntersections_no_reverse simple first one two
    · exact removeOppositeIntersections_no_reverse simple second two one
  by_contra different
  rcases listBefore_total xa ya different with one | one <;>
    rcases listBefore_total xb yb different with two | two
  · exact noParallel one two
  · exact noReverse one two
  · exact noReverse one two
  · exact noParallel one two

private theorem omitted_path_marks_once {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (large : 3 ≤ k)
    {a b q : Fin p} (qa : q < a) (qb : q < b) {v u w : V}
    (av : ListBefore paths a v u) (bv : ListBefore paths b v w)
    (qu : ListBefore (removeOppositeIntersections paths) q u v)
    (qw : ListBefore (removeOppositeIntersections paths) q w v) : a = b := by
  by_contra different
  by_cases eq : u = w
  · subst w
    exact no_parallel_list_steps free (by omega) different av bv
  have old_u := (removeOppositeIntersections_before simple qu).1
  have old_w := (removeOppositeIntersections_before simple qw).1
  rcases listBefore_total old_u old_w eq with forward | backward
  · exact free large (threeListBridge qa.ne' (fun equal => different equal.symm) qb.ne' av forward bv) qb
  · exact free large (threeListBridge qb.ne' (show a ≠ b from different) qa.ne' bv backward av) qa

/-- Every vertex keeps at least half of its original incidences. Charge each
omitted occurrence to a retained earlier occurrence at the same vertex. -/
theorem removeOppositeIntersections_degree {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (large : 3 ≤ k)
    (v : V) :
    (occurrences (fun i => (paths i).toFinset) v).card ≤
      2 * (occurrences (fun i => (removeOppositeIntersections paths i).toFinset) v).card := by
  classical
  let original := occurrences (fun i => (paths i).toFinset) v
  let kept := occurrences (fun i => (removeOppositeIntersections paths i).toFinset) v
  let omitted := original \ kept
  have inside : kept ⊆ original := by
    intro i hi
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((removeOppositeIntersections_mem paths i v).mp
      (List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (removeOppositeIntersections paths j).toFinset)).mp hi))).1)
  have found (i : omitted) : ∃ j : Fin p, j < i.val ∧ ∃ u,
      ListBefore paths i.val v u ∧ ListBefore (removeOppositeIntersections paths) j u v := by
    obtain ⟨old, lost⟩ := mem_sdiff.mp i.property
    by_contra no
    apply lost
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((removeOppositeIntersections_mem paths i.val v).mpr
      ⟨List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (paths j).toFinset)).mp old), no⟩))
  let mark (i : omitted) := Classical.choose (found i)
  have valid (i : omitted) : mark i < i.val ∧ ∃ u,
      ListBefore paths i.val v u ∧ ListBefore (removeOppositeIntersections paths) (mark i) u v :=
    Classical.choose_spec (found i)
  have budget : omitted.attach.card ≤ kept.card := by
    apply card_le_card_of_injOn mark
    · intro i _
      obtain ⟨_, u, _, right⟩ := valid i
      exact mem_occurrences.mpr (List.mem_toFinset.mpr right.2.1)
    · intro a _ b _ equal
      apply Subtype.ext
      obtain ⟨qa, u, av, qu⟩ := valid a
      obtain ⟨qb, w, bv, qw⟩ := valid b
      exact omitted_path_marks_once simple free large qa (equal.symm ▸ qb) av bv qu (equal.symm ▸ qw)
  rw [card_attach] at budget
  change original.card ≤ 2 * kept.card
  have count := card_sdiff_add_card_eq_card inside
  change (original \ kept).card ≤ kept.card at budget
  omega

/-- Pruning opposing intersections preserves at least half of the total
incidence mass, with the original path and vertex budgets. -/
theorem removeOppositeIntersections_mass [Fintype V] {p k : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (large : 3 ≤ k) :
    (∑ i, (paths i).length) ≤ 2 * (∑ i, (removeOppositeIntersections paths i).length) := by
  let orig (i : Fin p) := (paths i).toFinset
  let kept (i : Fin p) := (removeOppositeIntersections paths i).toFinset
  have oldLength (i : Fin p) : (orig i).card = (paths i).length := List.toFinset_card_of_nodup (simple i)
  have newLength (i : Fin p) : (kept i).card = (removeOppositeIntersections paths i).length :=
    List.toFinset_card_of_nodup ((removeOppositeIntersections_sublist paths i).nodup (simple i))
  simp only [← oldLength, ← newLength, ← sum_occurrences orig, ← sum_occurrences kept, mul_sum]
  exact sum_le_sum (fun v _ => removeOppositeIntersections_degree simple free large v)

end OnlineReachabilityPreservers
