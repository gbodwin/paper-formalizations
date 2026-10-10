import VFTSpanners.EdgeShortestPaths
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds

/-! The paper only makes an informal runtime observation. This module checks
its combinatorial content for the naive exhaustive implementation: the exact
fault-set query schedule, an exponential lower bound, and a power-set
upper bound. It does not assert that the noncomputable
greedy specification is executable or analyze a shortest-path implementation. -/
namespace VFTSpanners
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- All fault sets of size at most `f` in a given finite universe. -/
def admissibleFaultSets (U : Finset α) (f : ℕ) : Finset (Finset α) :=
  U.powerset.filter (fun F => F.card ≤ f)

omit [DecidableEq α] in
@[simp] theorem mem_admissibleFaultSets (U : Finset α) (f : ℕ) (F : Finset α) :
    F ∈ admissibleFaultSets U f ↔ F ⊆ U ∧ F.card ≤ f := by
  simp [admissibleFaultSets]

omit [DecidableEq α] in
/-- Exact number of fault sets, including `f > |U|` without a convention gap. -/
theorem admissibleFaultSets_card (U : Finset α) (f : ℕ) :
    (admissibleFaultSets U f).card =
      ∑ j ∈ range (U.card+1), if j ≤ f then U.card.choose j else 0 := by
  rw [admissibleFaultSets, card_eq_sum_ones, sum_filter,
    sum_powerset_apply_card (fun j => if j ≤ f then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

/-- Exhaustive enumeration has at least `2^f` entries when `f ≤ |U|`. -/
theorem admissibleFaultSets_exponential (U : Finset α) (f : ℕ) (hf : f ≤ U.card) :
    2^f ≤ (admissibleFaultSets U f).card := by
  obtain ⟨S,hSU,hSf⟩ := exists_subset_card_eq hf
  have hsub : S.powerset ⊆ admissibleFaultSets U f := by
    intro F hF
    have hFS := mem_powerset.mp hF
    exact (mem_admissibleFaultSets _ _ _).mpr
      ⟨hFS.trans hSU, hSf ▸ card_le_card hFS⟩
  simpa [hSf] using card_le_card hsub

/-- Every entry of the exhaustive schedule is one edge/fault-set distance query. -/
def naiveQuerySchedule (E : Finset β) (U : Finset α) (f : ℕ) :
    Finset (β × Finset α) := E ×ˢ admissibleFaultSets U f

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem naiveQuerySchedule_card (E : Finset β) (U : Finset α) (f : ℕ) :
    (naiveQuerySchedule E U f).card = E.card*(admissibleFaultSets U f).card := by
  simp [naiveQuerySchedule]

theorem naiveQuerySchedule_exponential (E : Finset β) (U : Finset α) (f : ℕ)
    (hf : f ≤ U.card) : E.card*2^f ≤ (naiveQuerySchedule E U f).card := by
  rw [naiveQuerySchedule_card]
  exact Nat.mul_le_mul_left _ (admissibleFaultSets_exponential U f hf)

/-- The power-set schedule never exceeds all subsets of the fault universe. -/
theorem naiveQuerySchedule_le_powerset (E : Finset β) (U : Finset α) (f : ℕ) :
    (naiveQuerySchedule E U f).card ≤ E.card*2^U.card := by
  rw [naiveQuerySchedule_card]
  apply Nat.mul_le_mul_left
  simpa [admissibleFaultSets] using card_le_card (filter_subset (fun F : Finset α => F.card ≤ f) U.powerset)

end VFTSpanners
