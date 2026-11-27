import OnlineReachabilityPreservers.FrozenUnbalancedBudgets
import OnlineReachabilityPreservers.FrozenDistinctCleaning

/-! Compare the literal last-arc and full extrema in the two unbalanced budget regimes. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Either the path budget controls the vertex-pair count, or the
vertex budget controls the path-pair count and half-three is excluded. -/
def UnbalancedBridgeBudgets (n p cutoff factor : ℕ) : Prop :=
  2*(n*n-n) ≤ factor*(factor-1)*p ∨
    (3 ≤ cutoff ∧ p*p-p ≤ factor*(factor-3)*n)

/-- Uniform bounds on either pair-count ratio give one uniform factor
for all budget pairs in the corresponding regime. -/
theorem unbalancedBridgeBudgets_of_bounded_pair_ratios {n p cutoff C : ℕ}
    (budget : n*n-n ≤ C*p ∨ (3 ≤ cutoff ∧ p*p-p ≤ C*n)) :
    UnbalancedBridgeBudgets n p cutoff (C+3) := by
  rcases budget with manyPaths | ⟨three,manyVertices⟩
  · left
    have factor : 2*C ≤ (C+3)*(C+3-1) := calc
      _ ≤ (C+3)*2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    calc
      _ ≤ 2*(C*p) := Nat.mul_le_mul_left _ manyPaths
      _ = (2*C)*p := by rw [Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_right _ factor
  · right
    refine ⟨three,manyVertices.trans (Nat.mul_le_mul_right n ?_)⟩
    rw [show C+3-3 = C by omega]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right C (show 1 ≤ C+3 by omega)

/-- The two degree and length moments give a linear mass bound in
the designated regime. The constant can depend on the budget ratio. -/
theorem halfBridgeFree_mass_le_of_unbalanced_budgets {n p cutoff factor : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (factorLarge : 3 ≤ factor)
    (budget : UnbalancedBridgeBudgets n p cutoff factor) :
    (∑ i, (paths i).length) ≤ factor*max n p := by
  let M := ∑ i, (paths i).length
  rcases budget with manyPaths | ⟨three,manyVertices⟩
  · have moment : M^2 ≤ p*(2*(n*n-n)+M) := listMass_square_le_halfTwo paths simple free two
    have coefficient : factor-(factor-1) = 1 := by omega
    have bound := mass_le_mul_of_quadratic hp (a := factor) (c := factor-1) (Nat.sub_le _ _)
      (moment.trans (Nat.mul_le_mul_left _ (by rw [coefficient,one_mul]; omega)))
    exact bound.trans (Nat.mul_le_mul_left _ (le_max_right _ _))
  · have moment : M^2 ≤ n*(p*p-p+3*M) := listMass_square_le_halfThree_degree paths simple free three
    have coefficient : factor-(factor-3) = 3 := by omega
    have bound := mass_le_mul_of_quadratic hn (a := factor) (c := factor-3) (Nat.sub_le _ _)
      (moment.trans (Nat.mul_le_mul_left _ (by rw [coefficient]; omega)))
    exact bound.trans (Nat.mul_le_mul_left _ (le_max_left _ _))

/-- The indexed full maximum controls every half-bridge-free mass
at the same budgets and cutoff under either unbalanced budget condition. -/
theorem indexed_full_extremum_controls_half_of_unbalanced_budgets (n p cutoff factor : ℕ)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (factorLarge : 3 ≤ factor)
    (budget : UnbalancedBridgeBudgets n p cutoff factor) :
    ∃ full : Fin p → List (Fin n), (∀ i, (full i).Nodup) ∧ BridgeFree (Before full) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (full i).length) ∧
      ∀ half : Fin p → List (Fin n), (∀ i, (half i).Nodup) → HalfBridgeFree (Before half) cutoff →
        (∑ i, (half i).length) ≤ factor*(∑ i, (full i).length) := by
  obtain ⟨full,simple,free,maximal,nLe,pLe⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  refine ⟨full,simple,free,maximal,?_⟩
  intro half halfSimple halfFree
  exact (halfBridgeFree_mass_le_of_unbalanced_budgets half halfSimple halfFree two hn hp factorLarge budget).trans
    (Nat.mul_le_mul_left _ (max_le nLe pLe))

/-- The same constant applies to the literal exact-count full maximum
whenever a distinct nonempty full family exists at those counts. -/
theorem distinct_full_extremum_controls_half_of_unbalanced_budgets {n p cutoff factor : ℕ}
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (factorLarge : 3 ≤ factor)
    (budget : UnbalancedBridgeBudgets n p cutoff factor)
    (feasible : ∃ full : Fin p → List (Fin n), Function.Injective full ∧
      (∀ i, full i ≠ [] ∧ (full i).Nodup) ∧ BridgeFree (Before full) cutoff) :
    ∃ full : Fin p → List (Fin n), Function.Injective full ∧
      (∀ i, full i ≠ [] ∧ (full i).Nodup) ∧ BridgeFree (Before full) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
          (∑ i, (other i).length) ≤ ∑ i, (full i).length) ∧
      ∀ half : Fin p → List (Fin n), (∀ i, (half i).Nodup) → HalfBridgeFree (Before half) cutoff →
        (∑ i, (half i).length) ≤ factor*(∑ i, (full i).length) := by
  obtain ⟨full,distinct,simple,free,maximal,nLe,pLe⟩ := localOrderDistinctExtremal_isDense false hp feasible
  refine ⟨full,distinct,simple,free,maximal,?_⟩
  intro half halfSimple halfFree
  exact (halfBridgeFree_mass_le_of_unbalanced_budgets half halfSimple halfFree two hn hp factorLarge budget).trans
    (Nat.mul_le_mul_left _ (max_le nLe pLe))

end OnlineReachabilityPreservers
