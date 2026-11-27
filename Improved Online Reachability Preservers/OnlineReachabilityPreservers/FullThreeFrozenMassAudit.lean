import OnlineReachabilityPreservers.FullThreeLongRows
import OnlineReachabilityPreservers.FullThreeLiteralFeasibility

/-! Mass bounds at dense path budgets and a consequence for the original lower cap. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The subquadratic long-row bound holds uniformly over all smaller
vertex budgets once the outer budget is sufficiently large. -/
theorem full_three_long_mass_subquadratic_within_vertex_budget (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v p k : ℕ}, N ≤ n → v ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin v),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ ε*(n:ℝ)^2 := by
  obtain ⟨N₀,small⟩ := full_three_long_mass_subquadratic ε positive
  let threshold := ⌈(N₀:ℝ)^2/ε⌉₊
  refine ⟨N₀+threshold+1,?_⟩
  intro n v p k large fits three paths simple free
  by_cases size : N₀ ≤ v
  · exact (small size three paths simple free).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_left fits 2) positive.le)
  have nEnough : (N₀:ℝ)^2/ε ≤ (n:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  have nFits : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    _ ≤ (v:ℝ)^2 := by exact_mod_cast long_mass_le_square_of_full_two paths simple free (by omega)
    _ ≤ (N₀:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left (le_of_lt (lt_of_not_ge size)) 2
    _ ≤ ε*(n:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ positive).mp nEnough
    _ ≤ ε*(n:ℝ)^2 := mul_le_mul_of_nonneg_left (by nlinarith only [nFits,sq_nonneg ((n:ℝ)-1)]) positive.le

/-- An original mean length above eight forces every output row to be
long. At quadratic input mass, no full-three-free witness can then keep
a prescribed constant fraction while satisfying the original lower cap. -/
theorem full_frozen_high_mean_excludes_dense_retention (η : ℝ) (densityPositive : 0 < η)
    (retention : ℕ) (retentionPositive : 0 < retention) :
    ∃ N : ℕ, ∀ {n p M v q k : ℕ}, N ≤ n → v ≤ n → 0 < p → 3 ≤ k → 8*p < M → η*(n:ℝ)^2 ≤ M →
      ∀ paths : Fin q → List (Fin v), (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      frozenListCaps n p M paths → retention*(∑ i, (paths i).length) < M := by
  let ε := η/(2*(retention:ℝ))
  have positive : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,small⟩ := full_three_long_mass_subquadratic_within_vertex_budget ε positive
  refine ⟨N,?_⟩
  intro n p M v q k large fits pPos three high dense paths simple free caps
  have rPos : (0:ℝ) < retention := Nat.cast_pos.mpr retentionPositive
  have mean : (2:ℝ) < (M:ℝ)/(4*(p:ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have h : (8:ℝ)*(p:ℝ) < M := by exact_mod_cast high
    linarith only [h]
  have long (i : Fin q) : 2 < (paths i).length := by
    exact_mod_cast mean.trans_le (caps.2 i).1
  have mass : listMassAboveWidth paths 2 = ∑ i, (paths i).length := by
    unfold listMassAboveWidth
    simp [long]
  have little := small large fits three paths simple free
  rw [mass] at little
  have split : (retention:ℝ)*ε = η/2 := by
    dsimp [ε]
    field_simp [rPos.ne']
  have halfMass : (retention:ℝ)*((∑ i, (paths i).length : ℕ):ℝ) ≤ (M:ℝ)/2 := calc
    _ ≤ (retention:ℝ)*(ε*(n:ℝ)^2) := mul_le_mul_of_nonneg_left little rPos.le
    _ = η*(n:ℝ)^2/2 := by rw [← mul_assoc,split]; ring
    _ ≤ _ := by linarith only [dense]
  have mPos : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
  exact_mod_cast halfMass.trans_lt (by linarith only [mPos] : (M:ℝ)/2 < M)

/-- Within the one-way bipartite pair capacity, all full cutoffs from
three have mass between `2p` and `2p + o(n^2)`. The same exact-count
lower witness is literal and excludes full bridges at every size. -/
theorem full_three_extrema_at_pair_capacity (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → p ≤ (n/2)*(n-n/2) →
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before paths) d)) ∧
        (∑ i, (paths i).length) = 2*p) ∧
      (∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
        ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+ε*(n:ℝ)^2) := by
  obtain ⟨N,small⟩ := full_three_mass_le_twice_paths_add_subquadratic ε positive
  refine ⟨N,?_⟩
  intro n p k large three capacity
  exact ⟨by simpa only [Nat.add_zero] using literal_full_all_short_rows capacity (Nat.zero_le n),
    fun paths simple free => small large three paths simple free⟩

end OnlineReachabilityPreservers
