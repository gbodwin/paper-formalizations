import SlackSparsification.PlusSixRouting
import Mathlib.Tactic

/-! Explicit rounding and endpoint contract for the remaining subset +2 construction.
The constant 16 is a conservative uniform bound, not a claimed optimal constant. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph

/-- Integer replacement for the paper's real clustering parameter. -/
theorem exists_square_parameter (s : ℕ) (hs : 0 < s) :
    ∃ d : ℕ, 0 < d ∧ s ≤ d ^ 2 ∧ (d : ℝ) ≤ 2 * Real.sqrt s := by
  let r := Real.sqrt (s : ℝ)
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ s by omega))
  have hr0 : 0 ≤ r := by linarith
  let d := ⌈r⌉₊
  have hdr : r ≤ (d : ℝ) := Nat.le_ceil r
  have hdu : (d : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hd : 0 < d := by
    have : (0 : ℝ) < d := by linarith
    exact_mod_cast this
  have hrsq : r ^ 2 = (s : ℝ) := Real.sq_sqrt (by positivity)
  have hsd : (s : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  exact ⟨d, hd, by exact_mod_cast hsd, by linarith⟩

/-- Clustering costs ≤2nd and purchases cost ≤6sq, with qd≤n and s≤d². -/
theorem integer_subset_budget (n s d q : ℕ) (hqd : q * d ≤ n) (hs : s ≤ d ^ 2) :
    2 * n * d + 6 * s * q ≤ 8 * n * d := by
  have ha := Nat.mul_le_mul_right q hs
  have hb := Nat.mul_le_mul_right d hqd
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Remaining constructive endpoint, exposed as a proposition rather than an axiom.
No inhabitant is supplied here: clustering and the finite purchase fold remain to be built. -/
def IntegerSubsetConstruction (G : SimpleGraph V) : Prop :=
  ∀ (S : Finset V) (d : ℕ), 0 < d → S.card ≤ d ^ 2 →
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card ≤ 8 * Fintype.card V * d ∧
      ∀ s ∈ S, ∀ t ∈ S, H.edist s t ≤ G.edist s t + 2

omit [DecidableEq V] in
/-- A verified integer construction suffices for the exact existing +6 interface.
This is an implication, not a proof of the remaining construction premise. -/
theorem uniform_of_integer_subset_construction (G : SimpleGraph V)
    (hconstruct : IntegerSubsetConstruction G) : UniformSubsetPlusTwo G 16 := by
  intro S
  by_cases hs : 0 < S.card
  · obtain ⟨d, hd, hsd, hdr⟩ := exists_square_parameter S.card hs
    obtain ⟨H, hHG, hcost, hsat⟩ := hconstruct S d hd hsd
    refine ⟨H, hHG, ?_, hsat⟩
    have hc : (H.edgeFinset.card : ℝ) ≤ 8 * (Fintype.card V : ℝ) * d := by
      exact_mod_cast hcost
    calc
      _ ≤ 8 * (Fintype.card V : ℝ) * d := hc
      _ ≤ 8 * (Fintype.card V : ℝ) * (2 * Real.sqrt (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hdr (by positivity)
      _ = 16 * Fintype.card V * Real.sqrt (S.card : ℝ) := by ring
  · have he : S = ∅ := card_eq_zero.mp (by omega)
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · simp [he]
    · simp [he]

end SlackSparsification.SubsetPlusTwo
