import OnlineReachabilityPreservers.HalfFiveCleaning
import OnlineReachabilityPreservers.HalfFivePathRepair
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Frozen half-five cleaning by repairing crossed opposite comparisons. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- Trimming consecutive path pieces back to the original budget costs
at most two thirty-firsts of the mass in the dense case. -/
theorem trimSplitListPaths_at_original_width {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (hp : 0 < p) (dense : 8*p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let L := 4*M/p
    ∃ kept : Finset (ListBlockIndex paths L), kept.card ≤ p ∧
      31*(∑ i ∈ univ \ kept, (splitListPaths paths L i).length) ≤ 2*M := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let raw := splitListPaths paths L
  have long : p ≤ M := by omega
  have Mpos := hp.trans_le long
  have width : 0 < L := (four_average_width hp long).1
  have capacity : 31*M ≤ 8*(L*p) := by
    have floor := four_average_width_product hp (M := M)
    change 4*M < L*p+p at floor
    omega
  have rawMass : (∑ i, (raw i).length) = M := splitListPaths_size paths simple L
  obtain ⟨filled,full,leftover⟩ := splitListPaths_full_block_profile paths simple width
  have remaining : (univ \ filled).card ≤ p := by simpa only [Fintype.card_fin] using leftover.le
  obtain ⟨kept,budget,trimLoss⟩ := trim_full_weight_blocks_quadratic (fun i => (raw i).length)
    filled width full remaining (by rw [rawMass]; omega)
  let omitted := ∑ i ∈ univ \ kept, (raw i).length
  refine ⟨kept,budget,?_⟩
  change 31*omitted ≤ 2*M
  apply (Nat.mul_le_mul_left_iff Mpos).mp
  calc
    _ = (31*M)*omitted := by ring
    _ ≤ (8*(L*p))*omitted := Nat.mul_le_mul_right _ capacity
    _ = 2*(4*(L*p)*omitted) := by ring
    _ ≤ 2*M^2 := Nat.mul_le_mul_left _ (rawMass ▸ trimLoss)
    _ = _ := by ring

private theorem halfFive_repaired_path_widths {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hp : 0 < p)
    (pDense : 8*p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let L := 4*M/p
    let affected := oppositeWidthConflictIncidences paths (splitListPaths paths L) Sigma.fst
    ∃ q ≤ p, ∃ chosen : Fin q → List (Fin n),
      (∀ i, (chosen i).Nodup) ∧ HalfBridgeFree (Before chosen) 5 ∧
      (∀ i, (chosen i).length ≤ L) ∧ (∑ i, (chosen i).length) ≤ M ∧
      58*M ≤ 62*(∑ i, (chosen i).length)+31*affected.card ∧
      (∀ v, (occurrences (fun i => (chosen i).toFinset) v).card ≤
        (occurrences (fun i => (paths i).toFinset) v).card) := by
  classical
  let M := ∑ i, (paths i).length
  have long : p ≤ M := by omega
  let L := 4*M/p
  let J := ListBlockIndex paths L
  let raw := splitListPaths paths L
  let parent (j : J) := j.fst
  let affected := oppositeWidthConflictIncidences paths raw parent
  have width : 0 < L := (four_average_width hp long).1
  have rawSimple (i : J) : (raw i).Nodup := List.filter_sublist.nodup (simple i.fst)
  have rawLength (i : J) : (raw i).length ≤ L := localPathBlock_length _ (simple i.fst) width i.snd.val
  have rawMass : (∑ i : J, (raw i).length) = M := splitListPaths_size paths simple L
  have steps {i : J} {x y : Fin n} (step : Before raw i x y) : Before paths (parent i) x y :=
    listBefore_of_sublist (paths := fun j : J => paths j.fst) (simple i.fst) List.filter_sublist step
  have apart {i j : J} {x : Fin n} :
      i ≠ j → parent i = parent j → x ∈ raw i → x ∈ raw j → False := splitListPaths_disjoint
  let orig (i : Fin p) := (paths i).toFinset
  obtain ⟨kept,budget,trimBudget⟩ := trimSplitListPaths_at_original_width paths simple hp pDense
  let omitted := ∑ i ∈ univ \ kept, (raw i).length
  have trimBound : 31*omitted ≤ 2*M := trimBudget
  have trimExact : omitted+(∑ i ∈ kept, (raw i).length) = M :=
    (sum_sdiff (subset_univ kept)).trans rawMass
  obtain ⟨color,colorBudget⟩ := oppositeWidthDeletion_small paths raw parent
  let deleted := oppositeWidthDeletion paths raw parent color
  let repaired := erasePieceIncidences raw deleted
  have colorBound : 2*deleted.card ≤ affected.card := colorBudget
  have repairedFree : HalfBridgeFree (Before repaired) 5 :=
    eraseOppositeWidthConflicts_halfFree free rawSimple
      (block_parent_mono orig L) (fun {_ _ _} => steps) (fun {_ _ _} => apart) deleted
      (fun {_ _} edge => oppositeWidthDeletion_covers free (by decide) (fun {_ _ _} => steps) edge color)
  let q := kept.card
  let label : Fin q ≃o kept := Fintype.orderIsoFinOfCardEq _ (Fintype.card_coe _)
  let chosen (i : Fin q) := repaired (label i).val
  have injection : Function.Injective (fun i : Fin q => (label i).val) :=
    Subtype.val_injective.comp label.injective
  have chosenFree : HalfBridgeFree (Before chosen) 5 := by
    intro j small bridge earlier
    exact repairedFree small (bridge.mapPaths _ injection (fun _ _ _ step => step)) (label.strictMono earlier)
  have chosenSimple (i : Fin q) : (chosen i).Nodup :=
    (erasePieceIncidences_sublist raw deleted _).nodup (rawSimple _)
  have chosenLength (i : Fin q) : (chosen i).length ≤ L :=
    (erasePieceIncidences_sublist raw deleted _).length_le.trans (rawLength _)
  let K := ∑ i, (chosen i).length
  have count : K = ∑ j ∈ kept, (repaired j).length := by
    change (∑ i, (repaired (label.toEquiv i).val).length) = _
    rw [Equiv.sum_comp label.toEquiv (fun j : kept => (repaired j.val).length)]
    exact sum_attach kept (fun j => (repaired j).length)
  have loss : K+(pieceIncidences raw kept ∩ deleted).card = ∑ i ∈ kept, (raw i).length := by
    rw [count]
    exact erasePieceIncidences_mass_add_loss rawSimple kept deleted
  have intersection : (pieceIncidences raw kept ∩ deleted).card ≤ deleted.card :=
    card_le_card inter_subset_right
  have noIncrease (v : Fin n) : (occurrences (fun i => (chosen i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
    let origin (i : Fin q) := parent (label i).val
    have isOn {i : Fin q} (member : i ∈ occurrences (fun j => (chosen j).toFinset) v) : v ∈ raw (label i).val :=
      (mem_erasePieceIncidences.mp (List.mem_toFinset.mp
        ((mem_occurrences (marks := fun j => (chosen j).toFinset)).mp member))).1
    apply card_le_card_of_injOn origin
    · intro i member
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (List.filter_sublist.subset (isOn member)))
    · intro i hi j hj eq
      apply injection
      by_contra different
      exact apart different eq (isOn hi) (isOn hj)
  refine ⟨q,budget,chosen,chosenSimple,chosenFree,chosenLength,?_,?_,noIncrease⟩
  · change K ≤ M
    omega
  · change 58*M ≤ 62*K+31*affected.card
    omega

/-- The crossed comparisons may use either a small incidence budget
or a joint budget with the total original degree excess. -/
theorem regularization_list_frozen_half_five_of_width_conflict_budget {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (room : let M := ∑ i, (paths i).length
      let L := 4*M/p
      let E := (oppositeWidthConflictIncidences paths (splitListPaths paths L) Sigma.fst).card
      20*E ≤ 3*M ∨ 100*listDegreeExcess paths (4*M/n)+50*E ≤ 43*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',hn',p',hp',clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨n',hn',p',hp',clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let L := 4*M/p
  let D := 4*M/n
  let E := (oppositeWidthConflictIncidences paths (splitListPaths paths L) Sigma.fst).card
  change 20*E ≤ 3*M ∨ 100*listDegreeExcess paths D+50*E ≤ 43*M at room
  have nDense : 8*n ≤ M := by have h := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have h := le_max_right n p; omega
  obtain ⟨q,budget,chosen,chosenSimple,legal,lengthCap,upper,retained,degreeLe⟩ :=
    halfFive_repaired_path_widths paths simple free hp pDense
  let K := ∑ i, (chosen i).length
  change 58*M ≤ 62*K+31*E at retained
  rcases room with few | joint
  · exact regularization_list_frozen_half_five_after_length_cap_with_path_budget
      chosen chosenSimple legal hn hp nDense long budget lengthCap (by omega) upper
  have excess : listDegreeExcess chosen D ≤ listDegreeExcess paths D := by
    unfold listDegreeExcess
    exact sum_le_sum fun v _ => Nat.sub_le_sub_right (degreeLe v) D
  apply regularization_list_frozen_half_five_after_degree_clipping chosen chosenSimple legal
    hn hp dense long budget lengthCap upper
  change 5002*M+10000*listDegreeExcess chosen D ≤ 10000*K
  omega

end OnlineReachabilityPreservers
