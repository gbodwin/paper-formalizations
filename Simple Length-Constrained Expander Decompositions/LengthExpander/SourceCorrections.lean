import LengthExpander.Demands
import Lean.Elab.Tactic.Omega

/-! Concrete counterexamples to intermediate formulas in arXiv:2510.10227v1.
These do not refute the main asymptotic theorems. -/
namespace LengthExpander.SourceCorrections
open Finset

def unitWeight : NodeWeight Bool := fun _ => 1

/-- The literal ordered-pair reading of Definition A.1 already fails for
one asymmetric demand. An undirected edge count is symmetric. -/
def oneWay : Demand Bool := fun u v => if u = false ∧ v = true then 1 else 0

theorem oneWay_respects : Respects oneWay unitWeight := by
  constructor <;> intro v <;> cases v <;> decide

theorem asymmetric_demand_not_undirected_count :
    ¬ ∃ count : Bool → Bool → ℕ,
      (∀ u v, count u v = count v u) ∧ (∀ u v, count u v = oneWay u v) := by
  rintro ⟨count, hsym, hcount⟩
  have h := hsym false true
  rw [hcount, hcount] at h
  norm_num [oneWay] at h

/-- One unit of demand in each direction between two distinct vertices. -/
def twoWay : Demand Bool := fun u v => if u = v then 0 else 1

theorem twoWay_respects : Respects twoWay unitWeight := by
  constructor <;> intro v <;> cases v <;> decide

theorem twoWay_size : demandSize twoWay = 2 := by decide

/-- Every undirected matching using A(v) copies can accommodate at most
A(v) total incidences at v. Definition 2.4 only bounds incoming/outgoing
incidences separately. Thus Definition A.1's matching need not exist. -/
theorem twoWay_exceeds_copy_capacity :
    ¬ (∀ v : Bool, (∑ u, twoWay v u) + (∑ u, twoWay u v) ≤ unitWeight v) := by
  intro h
  have := h false
  norm_num [twoWay, unitWeight, Fintype.sum_bool] at this

/-- In Definition A.5, a single tree edge with arboricity one is multiplied
by 1/(2α)=1/2. This is not an integral demand as required in Definition 2.2. -/
theorem half_not_integral : ¬ ∃ n : ℕ, (n : ℝ) = (1 / 2 : ℝ) := by
  rintro ⟨n, hn⟩
  have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  have hn0 : n = 0 := by omega
  norm_num [hn0] at hn

/-- Theorem 5.1's displayed sum-of-ratios assertion fails even with two
identical positive terms, each of sparsity one. The ratio-of-sums assertion
used elsewhere in the paper is correct. -/
theorem sum_ratios_counterexample :
    (∀ i : Bool, (1 : ℝ) / 1 ≤ 1) ∧
    ¬ (∑ _i : Bool, (1 : ℝ) / 1) ≤ 1 := by
  norm_num [Fintype.sum_bool]

/-- Definition 2.10 gives an inequality, not the equality in (5.1). -/
theorem sparse_inequality_not_equality :
    (1 : ℝ) / 2 ≤ 1 ∧ ¬ (1 : ℝ) / 2 = 1 := by norm_num

end LengthExpander.SourceCorrections
