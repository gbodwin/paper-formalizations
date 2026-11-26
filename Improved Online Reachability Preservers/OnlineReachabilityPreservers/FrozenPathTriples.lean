import OnlineReachabilityPreservers.FrozenLengthCappedPaths
import OnlineReachabilityPreservers.LocalFrozenLowMass
import Mathlib.Data.Finset.Powerset

/-! Count triples of paths through a vertex to cover sparse path budgets. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem three_paths_share_at_most_one_vertex {n k : ℕ} {I : Type*} [LinearOrder I]
    {paths : I → List (Fin n)} (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) {rows : Finset I}
    (three : rows.card = 3) {x y : Fin n}
    (atX : ∀ i ∈ rows, x ∈ paths i) (atY : ∀ i ∈ rows, y ∈ paths i) : x = y := by
  classical
  by_contra different
  let direction (i : rows) : Bool := decide (ListBefore paths i.val x y)
  have onlyOne : Function.Injective direction := by
    intro i j equal
    by_contra unequal
    have differentRows : i.val ≠ j.val := fun e => unequal (Subtype.ext e)
    rcases listBefore_total (atX i.val i.property) (atY i.val i.property) different with xy | yx
    · have jxy : ListBefore paths j.val x y := by
        have level : direction j = true := equal.symm.trans (decide_eq_true xy)
        exact of_decide_eq_true level
      exact no_parallel_list_steps free cutoff differentRows xy jxy
    · have directionI : direction i = false := decide_eq_false (fun xy =>
        lt_asymm xy.2.2 yx.2.2)
      rcases listBefore_total (atX j.val j.property) (atY j.val j.property) different with jxy | jyx
      · have directionJ : direction j = true := decide_eq_true jxy
        simp [directionI, directionJ] at equal
      · exact no_parallel_list_steps free cutoff differentRows yx jyx
  have count := Fintype.card_le_of_injective direction onlyOne
  simp only [Fintype.card_coe, three, Fintype.card_bool] at count
  omega

private theorem mul_degree_le_triples {slope intercept threshold : ℕ}
    (initial : ∀ d ≤ threshold, slope * d ≤ intercept + d.choose 3)
    (increasing : slope ≤ threshold.choose 2) (d : ℕ) : slope * d ≤ intercept + d.choose 3 := by
  induction d with
  | zero => exact initial 0 (Nat.zero_le _)
  | succ d ih =>
    by_cases small : d + 1 ≤ threshold
    · exact initial _ small
    · have large : threshold ≤ d := by omega
      have rate := increasing.trans (Nat.choose_le_choose 2 large)
      rw [Nat.mul_succ, Nat.choose_succ_succ]
      change slope * d + slope ≤ intercept + (d.choose 2 + d.choose 3)
      omega

private theorem listMass_mul_le_of_path_triples {n k : ℕ} {I : Type*} [LinearOrder I] [Fintype I]
    (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) {slope intercept : ℕ}
    (affine : ∀ d, slope * d ≤ intercept + d.choose 3) :
    slope * (∑ i, (paths i).length) ≤ intercept * n + (Fintype.card I).choose 3 := by
  let marks (i : I) := (paths i).toFinset
  let incident (v : Fin n) := occurrences marks v
  let tagged := (univ : Finset (Fin n)).sigma (fun v => (incident v).powersetCard 3)
  let all := (univ : Finset I).powersetCard 3
  let forget (tag : tagged) : all := ⟨tag.val.2, mem_powersetCard.mpr
    ⟨subset_univ _, (mem_powersetCard.mp (mem_sigma.mp tag.property).2).2⟩⟩
  have injective : Function.Injective forget := by
    intro a b same
    have rows : a.val.2 = b.val.2 := congrArg Subtype.val same
    obtain ⟨atA, three⟩ := mem_powersetCard.mp (mem_sigma.mp a.property).2
    have atB : a.val.2 ⊆ incident b.val.1 := rows ▸ (mem_powersetCard.mp (mem_sigma.mp b.property).2).1
    have vertex := three_paths_share_at_most_one_vertex free cutoff three
      (fun i member => List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp (atA member)))
      (fun i member => List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp (atB member)))
    exact Subtype.ext (Sigma.ext vertex (heq_of_eq rows))
  have triples : (∑ v : Fin n, (incident v).card.choose 3) ≤ (Fintype.card I).choose 3 := by
    have bound := Fintype.card_le_of_injective forget injective
    simpa only [Fintype.card_coe, tagged, all, card_sigma, card_powersetCard, card_univ, Fintype.card_fin] using bound
  have mass : (∑ i, (paths i).length) = ∑ v : Fin n, (incident v).card := by
    rw [sum_occurrences marks]
    exact sum_congr rfl (fun i _ => (List.toFinset_card_of_nodup (simple i)).symm)
  rw [mass, mul_sum]
  calc
    _ ≤ ∑ v : Fin n, (intercept + (incident v).card.choose 3) :=
      sum_le_sum (fun v _ => affine (incident v).card)
    _ = intercept * n + ∑ v : Fin n, (incident v).card.choose 3 := by simp [sum_add_distrib, Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left triples _

/-- A triple of distinct rows meets at at most one vertex. The total
incidence count is at most twice the vertex count plus the number of
triples of rows. -/
theorem listMass_le_two_vertices_add_path_triples {n k : ℕ} {I : Type*} [LinearOrder I] [Fintype I]
    (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) :
    (∑ i, (paths i).length) ≤ 2 * n + (Fintype.card I).choose 3 := by
  have affine : ∀ d : ℕ, 1 * d ≤ 2 + d.choose 3 :=
    mul_degree_le_triples (threshold := 2) (by intro d h; interval_cases d <;> decide) (by decide)
  simpa only [Nat.one_mul] using listMass_mul_le_of_path_triples paths simple free cutoff affine

/-- The lower affine estimate for the number of triples through a vertex
at degrees seven and eight improves the bound around mean degree eight. -/
theorem listMass_mul_twentyOne_le_path_triples {n k : ℕ} {I : Type*} [LinearOrder I] [Fintype I]
    (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) :
    21 * (∑ i, (paths i).length) ≤ 112 * n + (Fintype.card I).choose 3 := by
  exact listMass_mul_le_of_path_triples paths simple free cutoff
    (mul_degree_le_triples (threshold := 7) (by intro d h; interval_cases d <;> decide) (by decide))

/-- If the number of triples of path labels is at most 56 times the vertex
budget, the low-mass witnesses meet the original caps and retain at least
one eighth of the input mass. -/
theorem regularization_list_frozen_of_few_path_triples {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : p.choose 3 ≤ 56 * n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have bound := listMass_mul_twentyOne_le_path_triples paths simple free cutoff
  rw [Fintype.card_fin] at bound
  have small : (∑ i, (paths i).length) ≤ 8 * n := by omega
  exact regularization_list_frozen_low_mass paths simple free cutoff hn hp dense long
    (small.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))

/-- Few rows above the original length cap suffice even when clipping
would lose too much. In that case the overlong row triples force the
whole input into the low-mass regime. -/
theorem regularization_list_frozen_of_few_overlong_path_triples {half : Bool} {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (cutoff : 2 ≤ k) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : let M := ∑ i, (paths i).length
      let q := (univ.filter fun i => 4 * M / p < (paths i).length).card
      5 * q.choose 3 ≤ 16 * n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4 * M / p
  let rows := (univ : Finset (Fin p)).filter fun i => L < (paths i).length
  let chosen (i : rows) := paths i.val
  let S := listMassAboveWidth paths L
  let T := listLengthExcess paths L
  change 5 * rows.card.choose 3 ≤ 16 * n at few
  by_cases clipping : 15 * T ≤ 7 * M
  · exact regularization_list_frozen_of_small_length_excess paths simple allowed size hn hp dense long clipping
  have free : HalfBridgeFree (ListBefore paths) k := by
    cases half
    · exact allowed.halfFree
    · exact allowed
  have subFree : HalfBridgeFree (ListBefore chosen) k := by
    intro j length bridge arrival
    exact free length (bridge.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) arrival
  have mass : (∑ i : rows, (chosen i).length) = S := sum_attach rows (fun i => (paths i).length)
  have bound := listMass_mul_le_of_path_triples chosen (fun i => simple i.val) subFree cutoff
    (slope := 3) (intercept := 8)
    (mul_degree_le_triples (threshold := 3) (by intro d h; interval_cases d <;> decide) (by decide))
  rw [mass, Fintype.card_coe] at bound
  have excess : T + rows.card * L = S := listLengthExcess_add_count_mul paths L
  have sparse : M ≤ 8 * n := by omega
  obtain ⟨n', nCap, p', pCap, clean, cleanSimple, full, retained, upper, caps⟩ :=
    regularization_list_frozen_low_mass paths simple free cutoff hn hp dense long
      (sparse.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
  refine ⟨n', nCap, p', pCap, clean, cleanSimple, ?_, retained.trans (by omega), upper, caps⟩
  cases half
  · exact full
  · exact full.halfFree

end OnlineReachabilityPreservers
