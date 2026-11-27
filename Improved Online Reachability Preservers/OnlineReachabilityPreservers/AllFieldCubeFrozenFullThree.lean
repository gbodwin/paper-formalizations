import OnlineReachabilityPreservers.WengerThreeRows
import OnlineReachabilityPreservers.FrozenUnbalancedBudgets
import OnlineReachabilityPreservers.IncidenceFullThree

/-! The literal starting-average witness at every equal field cube. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At equal field-cube budgets, the half mass is at most four regular
witness masses for every field size, including the small cubes. -/
theorem half_three_mass_le_four_on_cube_budgets_of_two {q cutoff : ℕ} (qLarge : 2 ≤ q)
    (paths : Fin (q^3) → List (Fin (q^3))) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*q^4 := by
  have qPos : 0 < q := by omega
  have nPos : 0 < q^3 := by positivity
  by_cases big : 5 ≤ q
  · have charge : 4*q^3+q^3 ≤ q^4 := calc
      _ = 5*q^3 := by ring
      _ ≤ q*q^3 := Nat.mul_le_mul_right _ big
      _ = _ := by ring
    have volume : (q^3*q^3)^2 ≤ (q^4)^3 := le_of_eq (by ring)
    exact half_three_mass_le_four_of_volume nPos nPos charge volume paths simple half three
  · let n := q^3
    let M := ∑ i, (paths i).length
    let width := 4*q
    have moment : M^2 ≤ n*(2*(n*n-n)+M) := listMass_square_le_halfTwo paths simple half (by omega)
    have widths : 2*n ≤ width*(width-1) := by
      change 2*q^3 ≤ (4*q)*(4*q-1)
      have cases : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      rcases cases with rfl | rfl | rfl <;> decide
    have comparison : 2*(n*n-n) ≤ width*(width-1)*n := calc
      _ ≤ 2*(n*n) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2*n)*n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ widths
    have coefficient : width-(width-1) = 1 := by dsimp only [width]; omega
    have cap : M ≤ width*n :=
      mass_le_mul_of_quadratic nPos (Nat.sub_le width 1)
        (moment.trans (Nat.mul_le_mul_left _ (by rw [coefficient,one_mul]; omega)))
    exact cap.trans_eq (by dsimp only [width,n]; ring)

/-- For every finite field, the literal half maximum at equal field-cube
budgets and cutoff three admits a full-three witness on the exact same
budgets, with all four starting caps and quarter-mass retention. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_any_field_cube (F : Type*) [Field F] [Fintype F] :
    let q := Fintype.card F
    ∃ paths : Fin (q^3) → List (Fin (q^3)), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin (q^3) → List (Fin (q^3)), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ rows : Fin (q^3) → List (Fin (q^3)), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = q^4 ∧ (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
        frozenListCaps (q^3) (q^3) M rows := by
  let q := Fintype.card F
  have qPos : 0 < q := Fintype.card_pos
  have qLarge : 2 ≤ q := Fintype.one_lt_card
  have nPos : 0 < q^3 := by positivity
  obtain ⟨rows,injective,lengths,free,mass,degrees,_⟩ := wenger_full_three_rows F
  have valid (i) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (by rw [(lengths i).2]; exact qPos),(lengths i).1⟩
  have upper (paths : Fin (q^3) → List (Fin (q^3))) (simple : ∀ i, (paths i).Nodup)
      (excluded : HalfBridgeFree (Before paths) 3) : (∑ i, (paths i).length) ≤ 4*(q^3*q) := by
    rw [← pow_succ]
    exact half_three_mass_le_four_on_cube_budgets_of_two qLarge paths simple excluded le_rfl
  obtain ⟨paths,distinct,well,half,maximal,lower,retain,caps⟩ :=
    literal_half_maximum_frozen_full_three_of_regular_rows nPos nPos rows injective valid free
      (fun i => (lengths i).2) degrees rfl upper
  exact ⟨paths,distinct,well,half,maximal,rows,injective,valid,free,mass,lower,retain,caps⟩

end OnlineReachabilityPreservers
