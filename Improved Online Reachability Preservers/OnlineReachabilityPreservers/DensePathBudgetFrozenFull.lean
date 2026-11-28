import OnlineReachabilityPreservers.FullThreeLiteralFeasibility
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass
import OnlineReachabilityPreservers.PositiveMatchingDensity

/-! Half-to-full mass transfer at positive quadratic path density. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At any fixed positive quadratic path density, the half-three mass
is at most `(2 + ε) * p` for sufficiently large vertex budgets. -/
theorem half_three_mass_le_near_twice_paths_at_quadratic_path_budget (δ ε : ℝ)
    (δPos : 0 < δ) (εPos : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → δ*(n:ℝ)^2 ≤ p → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      ((∑ i, (paths i).length : ℕ):ℝ) ≤ (2+ε)*(p:ℝ) := by
  obtain ⟨N,small⟩ := half_three_mass_le_twice_paths_add_subquadratic (ε*δ) (by positivity)
  refine ⟨N,?_⟩
  intro n p k large density three paths simple free
  have scale := mul_le_mul_of_nonneg_left density εPos.le
  have total := small large three paths simple free
  linarith only [scale,total]

/-- Within the one-way pair capacity, a full-free family on the exact
budgets attains mass `2p`. At positive quadratic path density every simple
indexed half-three input has mass at most `(1 + ε) * 2p` for large `n`. -/
theorem literal_full_pair_witness_near_half_at_quadratic_path_budget (δ ε : ℝ)
    (δPos : 0 < δ) (εPos : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → δ*(n:ℝ)^2 ≤ p → p ≤ (n/2)*(n-n/2) → 3 ≤ k →
      ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
        (∀ d, IsEmpty (Bridge (Before rows) d)) ∧ (∑ i, (rows i).length) = 2*p ∧
        ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
          ((∑ i, (paths i).length : ℕ):ℝ) ≤ (1+ε)*((∑ i, (rows i).length : ℕ):ℝ) := by
  obtain ⟨N,small⟩ := half_three_mass_le_near_twice_paths_at_quadratic_path_budget δ (2*ε) δPos (by positivity)
  refine ⟨N,?_⟩
  intro n p k large density capacity three
  obtain ⟨rows,distinct,valid,free,mass⟩ := literal_full_all_short_rows capacity (Nat.zero_le n)
  simp only [Nat.add_zero] at mass
  refine ⟨rows,distinct,valid,free,mass,?_⟩
  intro paths simple half
  rw [mass,Nat.cast_mul,Nat.cast_ofNat]
  convert small large density three paths simple half using 1
  ring

/-- Positive quadratic path density suffices for the starting-average
literal half-to-full comparison from cutoff three onwards. The exact
half maximum only needs to be feasible. The output keeps at least one
eighth of its mass within both budgets and excludes every full bridge. -/
theorem localOrderDistinctExtremal_frozen_full_all_of_quadratic_path_budget (δ : ℝ) (δPos : 0 < δ) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → δ*(n:ℝ)^2 ≤ p → 3 ≤ k →
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) k) →
      ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) k ∧
        (∀ other : Fin p → List (Fin n), Function.Injective other →
          (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) k →
          (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
        let M := ∑ i, (paths i).length
        ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
          (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ cutoff, BridgeFree (Before rows) cutoff) ∧
          M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨N,small⟩ := half_three_mass_le_near_twice_paths_at_quadratic_path_budget δ 1 δPos (by positivity)
  refine ⟨max N 1,?_⟩
  intro n p k large density three feasible
  have hn : 0 < n := (le_max_right N 1).trans large
  have nPos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < p := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : 0 < δ*(n:ℝ)^2) density)
  obtain ⟨paths,distinct,valid,half,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense (k := k) true hp feasible
  have bound := small ((le_max_left N 1).trans large) density three paths (fun i => (valid i).2) half
  norm_num at bound
  have linear : (∑ i, (paths i).length) ≤ 3*p := by exact_mod_cast bound
  have low : (∑ i, (paths i).length) ≤ 8*max n p := by
    have fits := le_max_right n p
    omega
  exact ⟨paths,distinct,valid,half,maximal,
    regularization_literal_half_full_all_of_low_mass paths distinct valid half (by omega) hn hp dense low⟩

end OnlineReachabilityPreservers
