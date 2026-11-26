import OnlineReachabilityPreservers.FrozenDegreeClipping

/-! Frozen cleaning when one budget is large relative to the square of the other. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Apply Cauchy--Schwarz to the reverse-partner bound on squared degrees. -/
theorem listMass_square_le_halfThree_degree {k n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (three : 3 ≤ k) :
    let M := ∑ i, (paths i).length
    M^2 ≤ n*(p*p-p+3*M) := by
  let M := ∑ i, (paths i).length
  let d := fun v => (occurrences (fun i => (paths i).toFinset) v).card
  have mass : (∑ v, d v) = M := by
    rw [sum_occurrences]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  have counted : (∑ v, (d v*d v-d v))+M = ∑ v, (d v)^2 := by
    rw [← mass,← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    rw [pow_two]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  have moment : (∑ v, (d v)^2) ≤ p*p-p+3*M := by
    have pairBound : (∑ v, (d v*d v-d v)) ≤ p*p-p+2*M :=
      listDegree_square_sub_sum_le_halfThree paths simple free three
    omega
  have square : (∑ v, d v)^2 ≤ n*(∑ v, (d v)^2) := by
    simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (Fin n)) (fun _ => 1) d
  rw [mass] at square
  exact square.trans (Nat.mul_le_mul_left _ moment)

/-- Compare a quadratic bound with the positive factors above `a*q`. -/
theorem mass_le_mul_of_quadratic {M q a c : ℕ} (hq : 0 < q) (hc : c ≤ a)
    (bound : M^2 ≤ q*(a*c*q+(a-c)*M)) : M ≤ a*q := by
  by_contra! high
  have highReal : 0 < (M : ℝ)-(a : ℝ)*(q : ℝ) := sub_pos.mpr (by exact_mod_cast high)
  have positive : 0 < (M : ℝ) := by
    have h : 0 < M := by omega
    exact_mod_cast h
  have larger : 0 < (M : ℝ)+(c : ℝ)*(q : ℝ) := by positivity
  have castBound : ((M^2 : ℕ) : ℝ) ≤ ((q*(a*c*q+(a-c)*M) : ℕ) : ℝ) := Nat.cast_le.mpr bound
  push_cast [Nat.cast_sub hc] at castBound
  nlinarith only [mul_pos highReal larger, castBound]

/-- A sufficiently large budget on one side bounds the mean on that side
by eight. The low-mass construction then meets both original budgets and
all four original-average caps, excluding full bridges of every size. -/
theorem regularization_list_frozen_of_unbalanced_budgets {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (shape : n*n-n ≤ 28*p ∨ (3 ≤ k ∧ p*p-p ≤ 40*n)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ j, BridgeFree (ListBefore clean) j) ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have low : M ≤ 8*max n p := by
    rcases shape with manyPaths | ⟨three,manyVertices⟩
    · have raw : M^2 ≤ p*(2*(n*n-n)+M) := listMass_square_le_halfTwo paths simple free two
      have cap : M ≤ 8*p := mass_le_mul_of_quadratic hp (a := 8) (c := 7) (by decide)
        (raw.trans (Nat.mul_le_mul_left _ (by omega)))
      exact cap.trans (Nat.mul_le_mul_left _ (le_max_right _ _))
    · have raw : M^2 ≤ n*(p*p-p+3*M) := listMass_square_le_halfThree_degree paths simple free three
      have cap : M ≤ 8*n := mass_le_mul_of_quadratic hn (a := 8) (c := 5) (by decide)
        (raw.trans (Nat.mul_le_mul_left _ (by omega)))
      exact cap.trans (Nat.mul_le_mul_left _ (le_max_left _ _))
  obtain ⟨n',vn,p',pn,clean,simpleClean,freeAtBudget,retained,upper,caps⟩ :=
    regularization_list_frozen_low_mass_at_cutoff n paths simple free two hn hp dense long low
  have freeAll : ∀ j, BridgeFree (ListBefore clean) j := by
    intro j r _
    refine ⟨fun b => (freeAtBudget ?_).false b⟩
    have size : r+2 ≤ n' := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective b.vertex b.distinctVertices
    exact size.trans vn
  exact ⟨n',vn,p',pn,clean,simpleClean,freeAll,retained,upper,caps⟩

/-- Under the same two budget inequalities, the unrestricted maximum is
within a factor eight of a witness meeting the original caps and budgets. -/
theorem localOrderExtremal_frozen_of_unbalanced_budgets (n p k : ℕ) (half : Bool)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (shape : n*n-n ≤ 28*p ∨ (3 ≤ k ∧ p*p-p ≤ 40*n)) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ (∀ j, BridgeFree (ListBefore clean) j) ∧
        M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,allowed,maximal,dense,long⟩ := localOrderExtremal_isDense n p k half hn hp
  have free : HalfBridgeFree (ListBefore paths) k := by
    cases half
    · exact (show BridgeFree (ListBefore paths) k from allowed).halfFree
    · exact allowed
  exact ⟨paths,simple,allowed,maximal,
    regularization_list_frozen_of_unbalanced_budgets paths simple free two hn hp dense long shape⟩

end OnlineReachabilityPreservers
