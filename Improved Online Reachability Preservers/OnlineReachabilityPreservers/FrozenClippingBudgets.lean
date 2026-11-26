import OnlineReachabilityPreservers.ClippedVertexPartitions
import OnlineReachabilityPreservers.FrozenLengthCappedPaths
import OnlineReachabilityPreservers.FrozenSmallBudgets

/-! Count ordered pairs to control length clipping. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- Clipping all rows at a positive width loses at most twice the
ordered-pair budget divided by four times the width minus two. -/
theorem listLengthExcess_mul_le_halfTwo {k n p L : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (cutoff : 2 ≤ k) (width : 0 < L) : (4*L-2)*listLengthExcess paths L ≤ 2*(n*n-n) := by
  let M := ∑ i, (paths i).length
  let weight (i : Fin p) := (paths i).length
  have clipping : (4*L-2)*listLengthExcess paths L ≤ ∑ i, (weight i*weight i-weight i) := by
    rw [listLengthExcess, mul_sum]
    exact sum_le_sum fun _ _ => overflow_le_ordered_pairs width
  have total : (∑ i, (weight i*weight i-weight i)) + M = ∑ i, (paths i).length^2 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    change weight i * weight i - weight i + weight i = weight i ^ 2
    rw [pow_two]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  have pairs := listLength_square_sum_le_halfTwo paths simple free cutoff
  change (∑ i, (paths i).length^2) ≤ 2*(n*n-n)+M at pairs
  omega

/-- In the dense case, rounding the original width leaves these lower
bounds on its clipping coefficient and capacity. -/
theorem dense_clipping_coefficient {M q : ℕ} (hq : 0 < q) (dense : 8*q ≤ M) :
    126 ≤ 4*(4*M/q)-2 ∧ 61*M ≤ 4*((4*(4*M/q)-2)*q) := by
  let L := 4*M/q
  let A := 4*L-2
  have width : 32 ≤ L := (Nat.le_div_iff_mul_le hq).mpr (by omega)
  have rounded : 4*M < L*q+q := four_average_width_product hq
  have area : A*q+2*q = 4*(L*q) := by
    rw [← Nat.add_mul]
    have scaled : A+2 = 4*L := Nat.sub_add_cancel (by omega)
    rw [scaled]
    ring
  change 126 ≤ A ∧ 61*M ≤ 4*(A*q)
  refine ⟨?_,by omega⟩
  dsimp [A]
  omega

private theorem clipping_budget_of_path_count {M n p : ℕ} (hp : 0 < p)
    (dense : 8*n ≤ M) (long : 8*p ≤ M) (count : p ≤ 227 ∨ n*n-n ≤ 235*p) :
    30*(n*n-n) ≤ 7*M*(4*(4*M/p)-2) := by
  let A := 4*(4*M/p)-2
  obtain ⟨minimum, capacity⟩ := dense_clipping_coefficient hp long
  change 30*(n*n-n) ≤ 7*M*A
  rcases count with small | large
  · change 61*M ≤ 4*(A*p) at capacity
    have squares : 64*(n*n-n) ≤ M^2 := calc
      _ ≤ 64*(n*n) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (8*n)^2 := by ring
      _ ≤ _ := Nat.pow_le_pow_left dense 2
    have scale : (256*p)*(30*(n*n-n)) ≤ (256*p)*(7*M*A) := calc
      _ = (120*p)*(64*(n*n-n)) := by ring
      _ ≤ (120*p)*M^2 := Nat.mul_le_mul_left _ squares
      _ ≤ 27328*M^2 := Nat.mul_le_mul_right _ (by omega)
      _ = (7*64*M)*(61*M) := by ring
      _ ≤ (7*64*M)*(4*(A*p)) := Nat.mul_le_mul_left _ capacity
      _ = _ := by ring
    exact (Nat.mul_le_mul_left_iff (by positivity : 0 < 256*p)).mp scale
  · calc
      _ ≤ 30*(235*p) := Nat.mul_le_mul_left _ large
      _ ≤ (7*(8*p))*126 := by omega
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ long) minimum

/-- When one of these path-count conditions holds, clipping and splitting
vertices suffice. Full exclusion survives at the input cutoff, and half
exclusion survives through cutoff four. -/
theorem regularization_list_frozen_of_clipping_budgets {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (two : 2 ≤ k) (halfSize : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (count : p ≤ 227 ∨ n*n-n ≤ 235*p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have free : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n', hn', p', hp', clean, cleanSimple, cleanFull, mass, upper, caps⟩ :=
      regularization_list_frozen_low_mass paths simple free two hn hp dense long low
    have legal : localOrderAdmissible half k clean := by cases half; exact cleanFull; exact cleanFull.halfFree
    exact ⟨n', hn', p', hp', clean, cleanSimple, legal, by omega, upper, caps⟩
  let L := 4*M/p
  let A := 4*L-2
  let T := listLengthExcess paths L
  have vDense : 8*n ≤ M := by have sides := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have sides := le_max_right n p; omega
  have width : 0 < L := (four_average_width hp long).1
  have Apos : 0 < A := by dsimp [A]; omega
  have loss : A*T ≤ 2*(n*n-n) := listLengthExcess_mul_le_halfTwo paths simple free two width
  have capacity : 30*(n*n-n) ≤ 7*M*A := clipping_budget_of_path_count hp vDense pDense count
  have enough : 15*T ≤ 7*M := by
    apply (Nat.mul_le_mul_left_iff Apos).mp
    calc
      _ = 15*(A*T) := by ring
      _ ≤ 30*(n*n-n) := by rw [show 30*(n*n-n) = 15*(2*(n*n-n)) by ring]; exact Nat.mul_le_mul_left _ loss
      _ ≤ 7*M*A := capacity
      _ = _ := by ring
  exact regularization_list_frozen_of_small_length_excess paths simple allowed halfSize hn hp dense long enough

/-- The unrestricted maximum has the same guarantees under the stated
path-count conditions. -/
theorem localOrderExtremal_frozen_of_clipping_budgets (n p k : ℕ) (half : Bool)
    (two : 2 ≤ k) (halfSize : half = true → k ≤ 4) (hn : 0 < n) (hp : 0 < p)
    (count : p ≤ 227 ∨ n*n-n ≤ 235*p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths, simple, allowed, maximal, dense, long⟩ := localOrderExtremal_isDense n p k half hn hp
  exact ⟨paths, simple, allowed, maximal,
    regularization_list_frozen_of_clipping_budgets paths simple allowed two halfSize hn hp dense long count⟩

end OnlineReachabilityPreservers
