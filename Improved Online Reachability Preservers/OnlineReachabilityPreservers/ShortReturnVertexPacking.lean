import OnlineReachabilityPreservers.ShortReturnPiecePacking

/-! Group path occurrences that must share a degree copy to close a short return. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Two different rows form the first and last arcs of a short
closed walk through the original vertex. -/
def ShortReturnCopyRowPair {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (rows : I → List V) (cutoff : ℕ) (v : V) (i j : I) : Prop :=
  i ≠ j ∧ ∃ x y, Before rows i v x ∧ Before rows j y v ∧
    x ∈ reachIn (listPiecePrecedenceGraph rows) y (cutoff - 4)

/-- Each original vertex admits bounded groups of its incident rows,
with every short-return pair together. -/
def HasCappedShortReturnCopyPartition {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] [DecidableEq I]
    (rows : I → List V) (width cutoff : ℕ) : Prop :=
  ∀ v, ∃ groups, CappedPathPartition (occurrences (fun i => (rows i).toFinset) v)
    (ShortReturnCopyRowPair rows cutoff v) width groups

/-- Use such groups as vertex copies and merge groups whose total
size fits. The projection is exactly the original rows, every degree
meets the width, and the light copies inject into original vertices. -/
theorem copies_of_cappedShortReturnCopyPartition {n p w cutoff : ℕ} {half : Bool}
    {rows : Fin p → List (Fin n)} (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half cutoff rows)
    (canGroup : HasCappedShortReturnCopyPartition rows w cutoff) :
    ∃ (sizes : Fin n → ℕ) (copies : Fin p → List (Σₗ v : Fin n, Fin (sizes v))),
      (∀ i, (copies i).Nodup) ∧ localOrderAdmissible half cutoff copies ∧
      (∀ i, (copies i).map Sigma.fst = rows i) ∧
      (∀ v, (occurrences (fun i => (copies i).toFinset) v).card ≤ w) ∧
      ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ w/2} :
        Finset (Σₗ v : Fin n, Fin (sizes v))).card ≤ n := by
  classical
  let marks (i : Fin p) := (rows i).toFinset
  let incidence (v : Fin n) := occurrences marks v
  let linked (v : Fin n) := ShortReturnCopyRowPair rows cutoff v
  have existence (v : Fin n) := cappedPathPartition_of_pairwise_large (incidence v) (linked v) w (canGroup v)
  choose groups partition large using existence
  let sizes (v : Fin n) := (groups v).card
  let label (v : Fin n) : Fin (sizes v) ≃ ↥(groups v) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe (groups v))).symm
  let W := Σₗ v : Fin n, Fin (sizes v)
  let group (u : W) := (label u.fst u.snd).val
  have found (v : Fin n) (i : incidence v) : ∃ g : groups v, i.val ∈ g.val := by
    have covered : i.val ∈ (groups v).biUnion id := (partition v).cover.symm ▸ i.property
    obtain ⟨g, among, member⟩ := mem_biUnion.mp covered
    exact ⟨⟨g, among⟩, member⟩
  let selected (v : Fin n) (i : incidence v) := Classical.choose (found v i)
  have select_mem (v : Fin n) (i : incidence v) : i.val ∈ (selected v i).val :=
    Classical.choose_spec (found v i)
  have unique {v : Fin n} {i : Fin p} {a b : Finset (Fin p)} (amongA : a ∈ groups v)
      (amongB : b ∈ groups v) (inA : i ∈ a) (inB : i ∈ b) : a = b := by
    by_contra! different
    exact disjoint_left.mp ((partition v).apart amongA amongB different) inA inB
  let anchor (i : Fin p) (v : ↥(List.toFinset (rows i))) : incidence v.val :=
    ⟨i, mem_occurrences.mpr v.property⟩
  let copy (i : Fin p) (v : {x // x ∈ rows i}) : W :=
    ⟨v.val, (label v.val).symm (selected v.val (anchor i ⟨v.val, List.mem_toFinset.mpr v.property⟩))⟩
  let copies (i : Fin p) := (rows i).attach.map (copy i)
  have present (u : W) : group u ∈ groups u.fst := (label u.fst u.snd).property
  have same_label {u v : W} (base : u.fst = v.fst) (equal : group u = group v) : u = v := by
    obtain ⟨a, u⟩ := u
    obtain ⟨b, v⟩ := v
    change a = b at base
    subst b
    have same : u = v := (label a).injective (Subtype.ext equal)
    rw [same]
  have mem_copy (i : Fin p) (u : W) : u ∈ copies i ↔ i ∈ group u := by
    constructor
    · intro occurs
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp occurs
      change i ∈ (label v.val ((label v.val).symm (selected v.val _))).val
      rw [Equiv.apply_symm_apply]
      exact select_mem _ _
    · intro on
      have inOriginal : i ∈ incidence u.fst := by
        rw [← (partition u.fst).cover]
        exact mem_biUnion.mpr ⟨group u, present u, on⟩
      let x : {x // x ∈ rows i} := ⟨u.fst, List.mem_toFinset.mp
        ((mem_occurrences (marks := marks)).mp inOriginal)⟩
      refine List.mem_map.mpr ⟨x, List.mem_attach _ _, same_label rfl ?_⟩
      have onCopy : i ∈ group (copy i x) := by
        change i ∈ (label x.val ((label x.val).symm (selected x.val _))).val
        rw [Equiv.apply_symm_apply]
        exact select_mem _ _
      exact unique (present (copy i x)) (present u) onCopy on
  have piece_degree (u : W) : occurrences (fun i => (copies i).toFinset) u = group u := by
    ext i
    exact ((mem_occurrences (marks := fun i => (copies i).toFinset)).trans List.mem_toFinset).trans (mem_copy i u)
  have projects (i : Fin p) : (copies i).map (fun v => v.fst) = rows i := by
    unfold copies
    rw [List.map_map]
    exact List.attach_map_subtype_val _
  have rowSimple (i : Fin p) : (copies i).Nodup :=
    List.Nodup.of_map _ ((projects i).symm ▸ simple i)
  have steps ⦃i : Fin p⦄ ⦃u v : W⦄ (s : Before copies i u v) : Before rows i u.fst v.fst := by
    have step := listBefore_map (fun v : W => v.fst) ((projects i).symm ▸ simple i) s
    have pathsEq : (fun i => (copies i).map (fun v => v.fst)) = rows := funext projects
    rwa [pathsEq] at step
  have safe : ShortReturnCopyCompatible rows copies (fun u : W => u.fst) cutoff := by
    intro i j u x y v apart same start finish back
    change u.fst = v.fst at same
    have last : Before rows j y.fst u.fst := by
      have comparison := steps finish
      rwa [← same] at comparison
    have connected : linked u.fst i j := ⟨apart, x.fst, y.fst, steps start, last, back⟩
    obtain ⟨g, among, firstOn, lastOn⟩ := (partition u.fst).together connected
    have firstEq := unique (present u) among ((mem_copy i u).mp start.1) firstOn
    have vPresent : group v ∈ groups u.fst := by rw [same]; exact present v
    have lastEq := unique vPresent among ((mem_copy j v).mp finish.2.1) lastOn
    exact same_label same (firstEq.trans lastEq.symm)
  have legal : localOrderAdmissible half cutoff copies :=
    localOrderAdmissible_of_short_return_compatible_copies (fun u : W => u.fst) free steps safe
  refine ⟨sizes, copies, rowSimple, legal, projects, ?_, ?_⟩
  · intro u
    exact (congrArg card (piece_degree u)).trans_le ((partition u.fst).fits _ (present u))
  · let light : Finset W := univ.filter fun u => (occurrences (fun i => (copies i).toFinset) u).card ≤ w/2
    have count : light.card ≤ (univ : Finset (Fin n)).card := by
      apply card_le_card_of_injOn (fun u : W => u.fst) (fun _ _ => mem_univ _)
      intro u onU v onV same
      change u.fst = v.fst at same
      by_contra! different
      have groupApart : group u ≠ group v := fun eq => different (same_label same eq)
      have tooLarge := large u.fst (present u) (same ▸ present v) groupApart
      have left : (occurrences (fun i => (copies i).toFinset) u).card ≤ w/2 := (mem_filter.mp onU).2
      have right : (occurrences (fun i => (copies i).toFinset) v).card ≤ w/2 := (mem_filter.mp onV).2
      rw [piece_degree u] at left
      rw [piece_degree v] at right
      omega
    simpa only [card_univ, Fintype.card_fin] using count

/-- With at most one light degree copy per original vertex, the two
heavy-group profiles can be trimmed at the actual original widths.
A valid short-return path partition gives at least one quarter of the
original mass after both support trims and frozen peeling. -/
theorem regularization_list_frozen_after_grouped_width_splits {V : Type*}
    [LinearOrder V] [Fintype V] {n p k M : ℕ} {half : Bool}
    (copies : Fin p → List V) (simple : ∀ i, (copies i).Nodup)
    (free : localOrderAdmissible half k copies)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (mass : (∑ i, (copies i).length) = M)
    (degree : ∀ v, (occurrences (fun i => (copies i).toFinset) v).card ≤ 4*M/n)
    (lightV : ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ (4*M/n)/2} :
      Finset V).card ≤ n)
    (pathRoom : HasCappedShortReturnPartition copies (4*M/p) k) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  let L := 4*M/p
  let dMin := D/2 + 1
  let lMin := L/2 + 1
  obtain ⟨sizes, pieces, pieceSimple, legal, length, pieceMass, degrees, lightI⟩ :=
    split_of_cappedShortReturnPartition simple free pathRoom
  let J := Σₗ i : Fin p, Fin (sizes i)
  let rowSets := fun (i : J) => (pieces i).toFinset
  let fullV := (univ : Finset V).filter fun v => D/2 < (occurrences rowSets v).card
  let fullI := (univ : Finset J).filter fun i => L/2 < (pieces i).length
  have retained : (∑ i, (pieces i).length) = M := pieceMass.trans mass
  have dRoom : 2*M ≤ dMin*n := half_average_width_capacity hn
  have lRoom : 2*M ≤ lMin*p := half_average_width_capacity hp
  have full_v (v : V) (on : v ∈ fullV) : dMin ≤ (occurrences rowSets v).card := (mem_filter.mp on).2
  have full_i (i : J) (on : i ∈ fullI) : lMin ≤ (pieces i).length := (mem_filter.mp on).2
  have vRemainder : (univ \ fullV).card ≤ n := by
    have which : (univ : Finset V) \ fullV =
        ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ D/2} : Finset V) := by
      ext v
      simp only [fullV, mem_sdiff, mem_univ, mem_filter, true_and, not_lt, rowSets]
      rw [degrees v]
    exact which ▸ lightV
  have iRemainder : (univ \ fullI).card ≤ p := by
    have which : (univ : Finset J) \ fullI =
        ({i ∈ univ | (pieces i).length ≤ L/2} : Finset J) := by
      ext i
      simp [fullI]
    exact which ▸ lightI
  have mPos : 0 < M := hn.trans_le dense
  have massRoomV : (∑ i, (pieces i).length) ≤ dMin*n := retained.trans_le ((by omega : M ≤ 2*M).trans dRoom)
  have massRoomI : (∑ i, (pieces i).length) ≤ lMin*p := retained.trans_le ((by omega : M ≤ 2*M).trans lRoom)
  refine regularization_list_frozen_after_threshold_profile_trim_of_loss pieces pieceSimple legal
    hn hp dense long length (fun v => (degrees v).trans_le (degree v)) retained.le fullV fullI
    (Nat.succ_pos _) (Nat.succ_pos _) full_v vRemainder full_i iRemainder massRoomV massRoomI ?_
  dsimp only
  rw [retained]
  intro kept lostV lostI paid boundV boundI
  have smallLoss {capacity loss : ℕ} (room : 2*M ≤ capacity) (bound : 4*capacity*loss ≤ M^2) :
      8*loss ≤ M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      M*(8*loss) = 4*(2*M)*loss := by ring
      _ ≤ 4*capacity*loss := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ room)
      _ ≤ M^2 := bound
      _ = M*M := pow_two _
  have lessV := smallLoss dRoom boundV
  have lessI := smallLoss lRoom boundI
  omega

end OnlineReachabilityPreservers
