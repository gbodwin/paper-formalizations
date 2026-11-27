import OnlineReachabilityPreservers.ComponentSplitCleaning
import Mathlib.Data.Fintype.Card

/-! Pack whole groups of endpoints linked by short backward returns. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- A partition into bounded nonempty groups, with each linked pair
contained together in a group. -/
structure CappedPathPartition {V : Type*} [DecidableEq V] (vertices : Finset V)
    (linked : V → V → Prop) (width : ℕ) (groups : Finset (Finset V)) : Prop where
  cover : groups.biUnion id = vertices
  apart : (↑groups : Set (Finset V)).PairwiseDisjoint id
  nonempty : ∀ group ∈ groups, group.Nonempty
  fits : ∀ group ∈ groups, group.card ≤ width
  together : ∀ ⦃x y⦄, linked x y → ∃ group ∈ groups, x ∈ group ∧ y ∈ group

private theorem CappedPathPartition.merge {V : Type*} [DecidableEq V] {vertices : Finset V}
    {linked : V → V → Prop} {width : ℕ} {groups : Finset (Finset V)}
    (partition : CappedPathPartition vertices linked width groups) {a b : Finset V}
    (onA : a ∈ groups) (onB : b ∈ groups) (apart : a ≠ b) (fits : a.card + b.card ≤ width) :
    let merged := insert (a ∪ b) ((groups.erase a).erase b)
    CappedPathPartition vertices linked width merged ∧ merged.card < groups.card := by
  let kept := (groups.erase a).erase b
  let merged := insert (a ∪ b) kept
  have inGroups {g} (on : g ∈ kept) : g ∈ groups ∧ g ≠ a ∧ g ≠ b := by
    have h := mem_erase.mp on
    exact ⟨(mem_erase.mp h.2).2, (mem_erase.mp h.2).1, h.1⟩
  have covers {g} (on : g ∈ groups) : ∃ h ∈ merged, g ⊆ h := by
    by_cases first : g = a
    · exact ⟨a ∪ b, mem_insert_self _ _, first.symm ▸ subset_union_left⟩
    by_cases second : g = b
    · exact ⟨a ∪ b, mem_insert_self _ _, second.symm ▸ subset_union_right⟩
    exact ⟨g, mem_insert_of_mem (mem_erase.mpr ⟨second, mem_erase.mpr ⟨first, on⟩⟩), Subset.refl _⟩
  have separate (g : Finset V) (on : g ∈ kept) : Disjoint (a ∪ b) g := by
    obtain ⟨original, notA, notB⟩ := inGroups on
    exact disjoint_union_left.mpr
      ⟨partition.apart onA original notA.symm, partition.apart onB original notB.symm⟩
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← partition.cover]
      ext x
      simp only [mem_biUnion, id_eq]
      constructor
      · rintro ⟨g, on, inside⟩
        rcases mem_insert.mp on with rfl | old
        · rcases mem_union.mp inside with first | second
          · exact ⟨a, onA, first⟩
          · exact ⟨b, onB, second⟩
        · exact ⟨g, (inGroups old).1, inside⟩
      · rintro ⟨g, on, inside⟩
        obtain ⟨h, newer, included⟩ := covers on
        exact ⟨h, newer, included inside⟩
    · intro g onG h onH different
      rcases mem_insert.mp onG with rfl | earlier
      · exact separate h ((mem_insert.mp onH).resolve_left different.symm)
      · rcases mem_insert.mp onH with rfl | later
        · exact (separate g earlier).symm
        · exact partition.apart (inGroups earlier).1 (inGroups later).1 different
    · intro g on
      rcases mem_insert.mp on with rfl | old
      · obtain ⟨x, inside⟩ := partition.nonempty a onA
        exact ⟨x, mem_union_left _ inside⟩
      · exact partition.nonempty g (inGroups old).1
    · intro g on
      rcases mem_insert.mp on with rfl | old
      · have separate : Disjoint a b := partition.apart onA onB apart
        exact (card_union_of_disjoint separate).trans_le fits
      · exact partition.fits g (inGroups old).1
    · intro x y linked
      obtain ⟨g, on, left, right⟩ := partition.together linked
      obtain ⟨h, keeps, subset⟩ := covers on
      exact ⟨h, keeps, subset left, subset right⟩
  · have bKept : b ∈ groups.erase a := mem_erase.mpr ⟨apart.symm, onB⟩
    have less := card_erase_add_one bKept
    have first := card_erase_lt_of_mem onA
    have smaller : kept.card + 1 < groups.card := by
      change ((groups.erase a).erase b).card + 1 < groups.card
      omega
    exact (card_insert_le _ _).trans_lt smaller

/-- A valid partition of minimum cardinality has combined size
above the width for every two distinct groups. -/
theorem cappedPathPartition_of_pairwise_large {V : Type*} [DecidableEq V] (vertices : Finset V)
    (linked : V → V → Prop) (width : ℕ)
    (existsPartition : ∃ groups, CappedPathPartition vertices linked width groups) :
    ∃ groups, CappedPathPartition vertices linked width groups ∧
      (↑groups : Set (Finset V)).Pairwise (fun a b => width < a.card + b.card) := by
  classical
  have someSize : ∃ size, ∃ groups, CappedPathPartition vertices linked width groups ∧ groups.card = size := by
    obtain ⟨groups, partition⟩ := existsPartition
    exact ⟨groups.card, groups, partition, rfl⟩
  obtain ⟨groups, partition, smallest⟩ := Nat.find_spec someSize
  refine ⟨groups, partition, ?_⟩
  intro a onA b onB apart
  by_contra! fits
  obtain ⟨legal, less⟩ := partition.merge onA onB apart fits
  exact (Nat.find_min' someSize ⟨_, legal, rfl⟩).not_gt (smallest ▸ less)

/-- Each row admits a width-bounded partition whose groups contain both
endpoints of every comparison with a short backward return. -/
def HasCappedShortReturnPartition {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (rows : I → List V) (width cutoff : ℕ) : Prop :=
  ∀ i, ∃ groups, CappedPathPartition (rows i).toFinset
    (fun x y => Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x (cutoff - 3)) width groups

/-- Merge whole protected groups in each row until at most one piece
per parent has length at most half the width. This retains every
incidence and every vertex degree, and preserves the original full or
half bridge exclusion. -/
theorem split_of_cappedShortReturnPartition {V : Type*} [LinearOrder V] [Fintype V]
    {p w cutoff : ℕ} {half : Bool} {rows : Fin p → List V}
    (simple : ∀ i, (rows i).Nodup) (free : localOrderAdmissible half cutoff rows)
    (canGroup : HasCappedShortReturnPartition rows w cutoff) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ localOrderAdmissible half cutoff pieces ∧
      (∀ i, (pieces i).length ≤ w) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ w/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  classical
  let G := listPiecePrecedenceGraph rows
  let linked (i : Fin p) (x y : V) := Before rows i x y ∧ y ∈ reachIn G x (cutoff - 3)
  have existence (i : Fin p) := cappedPathPartition_of_pairwise_large (rows i).toFinset (linked i) w (canGroup i)
  choose groups partition large using existence
  let sizes (i : Fin p) := (groups i).card
  let label (i : Fin p) : Fin (sizes i) ≃ ↥(groups i) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe (groups i))).symm
  let J := Σₗ i : Fin p, Fin (sizes i)
  let group (j : J) := (label j.fst j.snd).val
  let pieces (j : J) := (rows j.fst).filter (fun x => decide (x ∈ group j))
  have onGroup (j : J) : group j ∈ groups j.fst := (label j.fst j.snd).property
  have subset (j : J) : group j ⊆ (rows j.fst).toFinset := by
    intro x on
    rw [← (partition j.fst).cover]
    exact mem_biUnion.mpr ⟨group j, onGroup j, on⟩
  have occurs (j : J) (x : V) : x ∈ pieces j ↔ x ∈ group j := by
    simp only [pieces, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun on => ⟨List.mem_toFinset.mp (subset j on), on⟩⟩
  have remains (j : J) : (pieces j).Sublist (rows j.fst) := List.filter_sublist
  have pieceSimple (j : J) : (pieces j).Nodup := (remains j).nodup (simple j.fst)
  have length (j : J) : (pieces j).length = (group j).card := by
    rw [← List.toFinset_card_of_nodup (pieceSimple j)]
    exact congrArg card (ext fun x => List.mem_toFinset.trans (occurs j x))
  have different {a b : J} (parent : a.fst = b.fst) (apart : a ≠ b) : group a ≠ group b := by
    obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    change i = j at parent
    subst j
    intro eq
    have same : a = b := (label i).injective (Subtype.ext eq)
    exact apart (by rw [same])
  have disjoint ⦃i j : J⦄ ⦃x : V⦄ (apart : i ≠ j) (parent : i.fst = j.fst)
      (left : x ∈ pieces i) (right : x ∈ pieces j) : False :=
    disjoint_left.mp ((partition i.fst).apart (onGroup i) (parent ▸ onGroup j) (different parent apart))
      ((occurs i x).mp left) ((occurs j x).mp right)
  have step ⦃j : J⦄ ⦃x y : V⦄ (on : Before pieces j x y) : Before rows j.fst x y :=
    listBefore_of_sublist (paths := fun i : J => rows i.fst) (cut := pieces) (simple j.fst) (remains j) on
  have projects ⦃j : J⦄ ⦃x y : V⦄ (on : Before pieces j x y) : Edge G (id x) (id y) :=
    listPiecePrecedenceGraph_edge.mpr ⟨j.fst, step on⟩
  have safe : NoShortBackwardReturnAcrossPieces G id rows pieces (fun j : J => j.fst) (cutoff - 3) := by
    intro i j x y apart parent left right forward back
    change i.fst = j.fst at parent
    obtain ⟨g, on, xIn, yIn⟩ := (partition i.fst).together (show linked i.fst x y from ⟨forward, back⟩)
    have sameI : group i = g := by
      by_contra! different
      exact disjoint_left.mp ((partition i.fst).apart (onGroup i) on different) ((occurs i x).mp left) xIn
    have sameJ : group j = g := by
      by_contra! different
      exact disjoint_left.mp ((partition i.fst).apart (parent ▸ onGroup j) on different) ((occurs j y).mp right) yIn
    exact different parent apart (sameI.trans sameJ.symm)
  have legal : localOrderAdmissible half cutoff pieces := by
    cases half
    · exact bridgeFree_of_disjoint_split_of_no_backward_returns G id free (fun j : J => j.fst)
        step projects disjoint safe
    · have mono : Monotone (fun j : J => j.fst) := by
        intro a b order
        rcases Sigma.Lex.le_def.mp order with lt | ⟨eq, _⟩
        · exact lt.le
        · exact eq.le
      exact halfBridgeFree_of_disjoint_split_of_no_backward_returns G id free (fun j : J => j.fst)
        mono step projects disjoint safe
  refine ⟨sizes, pieces, pieceSimple, legal, fun j => (length j).trans_le ((partition j.fst).fits _ (onGroup j)),
    ?_, ?_, ?_⟩
  · change (∑ j : (Σ i : Fin p, Fin (sizes i)), (pieces j).length) = _
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    calc
      _ = ∑ s : Fin (sizes i), (label i s).val.card :=
        sum_congr rfl (fun s _ => length ⟨i, s⟩)
      _ = ∑ g : ↥(groups i), g.val.card :=
        Fintype.sum_equiv (label i) _ _ fun _ => rfl
      _ = ∑ g ∈ groups i, g.card :=
        (sum_subtype (groups i) (fun _ => Iff.rfl) card).symm
      _ = (rows i).length :=
        (card_biUnion (partition i).apart).symm.trans <|
          ((congrArg card (partition i).cover).trans (List.toFinset_card_of_nodup (simple i)))
  · intro x
    let marks := fun i => (pieces i).toFinset
    have present {j : J} (on : j ∈ occurrences marks x) : x ∈ pieces j :=
      List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp on)
    apply card_bij (fun (j : J) _ => j.fst)
    · intro j on
      exact mem_occurrences.mpr (List.mem_toFinset.mpr ((remains j).subset (present on)))
    · intro i onI j onJ parent
      by_contra! apart
      exact disjoint apart parent (present onI) (present onJ)
    · intro i on
      have present : x ∈ (rows i).toFinset := (mem_occurrences (marks := fun j => (rows j).toFinset)).mp on
      rw [← (partition i).cover] at present
      obtain ⟨part, inGroups, onPart⟩ := mem_biUnion.mp present
      let j : J := ⟨i, (label i).symm ⟨part, inGroups⟩⟩
      refine ⟨j, mem_occurrences.mpr (List.mem_toFinset.mpr ((occurs j x).mpr ?_)), rfl⟩
      change x ∈ (label i ((label i).symm ⟨part, inGroups⟩)).val
      simpa only [Equiv.apply_symm_apply, id_eq] using onPart
  · have count : ({i ∈ univ | (pieces i).length ≤ w/2} : Finset J).card ≤
        (univ : Finset (Fin p)).card := by
      apply card_le_card_of_injOn (fun j : J => j.fst) (fun _ _ => mem_univ _)
      intro i onI j onJ parent
      change i.fst = j.fst at parent
      by_contra! apart
      have tooLarge := large i.fst (onGroup i) (parent ▸ onGroup j) (different parent apart)
      have left := (mem_filter.mp onI).2
      have right := (mem_filter.mp onJ).2
      rw [length i] at left
      rw [length j] at right
      omega
    simpa only [card_univ, Fintype.card_fin] using count

end OnlineReachabilityPreservers
