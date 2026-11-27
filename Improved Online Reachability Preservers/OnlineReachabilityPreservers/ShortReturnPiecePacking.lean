import OnlineReachabilityPreservers.FrozenQuadraticTrimming
import OnlineReachabilityPreservers.FullSevenWidthCleaning
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
incidence and every vertex degree. Use the original return radius, or
radius two for full cutoffs through seven. -/
theorem split_of_cappedShortReturnPartition_with_radius {V : Type*} [LinearOrder V] [Fintype V]
    {p w cutoff groupCutoff : ℕ} {half : Bool} {rows : Fin p → List V}
    (simple : ∀ i, (rows i).Nodup) (free : localOrderAdmissible half cutoff rows)
    (canGroup : HasCappedShortReturnPartition rows w groupCutoff)
    (radius : groupCutoff = cutoff ∨ groupCutoff = 5 ∧ half = false ∧ cutoff ≤ 7) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ localOrderAdmissible half cutoff pieces ∧
      (∀ i, (pieces i).length ≤ w) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ w/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  classical
  let G := listPiecePrecedenceGraph rows
  let linked (i : Fin p) (x y : V) := Before rows i x y ∧ y ∈ reachIn G x (groupCutoff - 3)
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
  have safe : NoShortBackwardReturnAcrossPieces G id rows pieces (fun j : J => j.fst) (groupCutoff - 3) := by
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
    rcases radius with same | ⟨atTwo, mode, short⟩
    · have sufficient : NoShortBackwardReturnAcrossPieces G id rows pieces (fun j : J => j.fst) (cutoff - 3) :=
        same ▸ safe
      cases half
      · exact bridgeFree_of_disjoint_split_of_no_backward_returns G id free (fun j : J => j.fst)
          step projects disjoint sufficient
      · have mono : Monotone (fun j : J => j.fst) := by
          intro a b order
          rcases Sigma.Lex.le_def.mp order with lt | ⟨eq, _⟩
          · exact lt.le
          · exact eq.le
        exact halfBridgeFree_of_disjoint_split_of_no_backward_returns G id free (fun j : J => j.fst)
          mono step projects disjoint sufficient
    · have sufficient : NoShortBackwardReturnAcrossPieces G id rows pieces (fun j : J => j.fst) 2 := by
        simpa only [atTwo] using safe
      cases mode
      exact bridgeFree_of_disjoint_split_of_no_two_step_backward_returns G id (fun j : J => j.fst)
        step projects disjoint sufficient free short
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

/-- Packing with the original return radius preserves either bridge exclusion. -/
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
      ({i ∈ univ | (pieces i).length ≤ w/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p :=
  split_of_cappedShortReturnPartition_with_radius simple free canGroup (Or.inl rfl)

/-- An admissible degree split and width-bounded short-return groups
give a frozen witness of mass at least one quarter of the original
mass. Trim the full degree blocks and the path pieces longer than half
the path width before applying the original lower caps. -/
theorem regularization_list_frozen_of_capped_short_return_partitions_with_radius {n p k groupCutoff : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (canGroup : let M := ∑ i, (paths i).length
      HasCappedShortReturnPartition (splitListVertices paths (4*M/n)) (4*M/p) groupCutoff)
    (radius : groupCutoff = k ∨ groupCutoff = 5 ∧ half = false ∧ k ≤ 7) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  let minLength := L/2 + 1
  have mPos : 0 < M := hn.trans_le dense
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < minLength := Nat.succ_pos _
  have capV : 3*M ≤ D*n := by
    have upper := four_average_width_product hn (M := M)
    change 4*M < D*n + n at upper
    omega
  have capI : 2*M ≤ minLength*p := half_average_width_capacity hp
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copyMass : (∑ i, (copies i).length) = M :=
    sum_congr rfl (fun i _ => by simp [copies, splitListVertices])
  obtain ⟨sizes, pieces, pieceSimple, legal, length, mass, degrees, light⟩ :=
    split_of_cappedShortReturnPartition_with_radius copySimple copyLegal canGroup radius
  let J := Σₗ i : Fin p, Fin (sizes i)
  have fullMass : (∑ i, (pieces i).length) = M := mass.trans copyMass
  obtain ⟨filledV, fullV, restV⟩ := splitListVertices_full_block_profile paths dPos
  have degree (v : ListVertexBlockIndex paths D) :
      (occurrences (fun i => (pieces i).toFinset) v).card ≤ D := by
    have equal : (fun i => (copies i).toFinset) = splitVertices (fun i => (paths i).toFinset) D :=
      funext (splitListVertices_toFinset paths D)
    have copied : (occurrences (fun i => (copies i).toFinset) v).card ≤ D := by
      rw [equal]
      exact splitVertices_degree (fun i => (paths i).toFinset) dPos v
    exact (degrees v).trans_le copied
  let heavy := (univ : Finset J).filter fun i => L/2 < (pieces i).length
  have fullI (i : J) (on : i ∈ heavy) : minLength ≤ (pieces i).length := (mem_filter.mp on).2
  have restI : (univ \ heavy).card ≤ p := by
    have equal : (univ : Finset J) \ heavy = ({i ∈ univ | (pieces i).length ≤ L/2} : Finset J) := by
      ext i
      simp [heavy]
    rw [equal]
    exact light
  refine regularization_list_frozen_after_packed_profile_trim_of_loss pieces pieceSimple legal
    hn hp dense long length degree fullMass.le filledV heavy lPos
    (fun v on => (degrees v).trans (fullV v on))
    (restV.le.trans_eq (Fintype.card_fin n)) fullI restI
    (fullMass.trans_le ((by omega : M ≤ 2*M).trans capI)) ?_
  dsimp only
  rw [fullMass]
  intro retained removedV removedI paid lossV lossI
  have vertexLoss : 12*removedV ≤ M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      M*(12*removedV) = 4*(3*M)*removedV := by ring
      _ ≤ 4*(D*n)*removedV := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ capV)
      _ ≤ M^2 := lossV
      _ = M*M := pow_two _
  have pathLoss : 8*removedI ≤ M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      M*(8*removedI) = 4*(2*M)*removedI := by ring
      _ ≤ 4*(minLength*p)*removedI := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ capI)
      _ ≤ M^2 := lossI
      _ = M*M := pow_two _
  omega

/-- The original path return radius gives frozen cleaning after degree copying. -/
theorem regularization_list_frozen_of_capped_short_return_partitions {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copyLegal : let M := ∑ i, (paths i).length; localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (canGroup : let M := ∑ i, (paths i).length
      HasCappedShortReturnPartition (splitListVertices paths (4*M/n)) (4*M/p) k) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_capped_short_return_partitions_with_radius paths simple hn hp dense long
    copyLegal canGroup (Or.inl rfl)

end OnlineReachabilityPreservers
