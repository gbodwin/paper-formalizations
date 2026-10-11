import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! The paper's main lemma, with explicit constants and actual finite unions.
`Satisfies H d` is any upward-closed demand property of the edge set `H`.
The two construction hypotheses are precisely the two premises of Lemma 1.
No termination, union, or geometric-series estimate is an extra hypothesis. -/
namespace SlackSparsification
open Finset

variable {E D : Type*} [DecidableEq E] [DecidableEq D]

/-- Finite, quantitative slack-to-complete amplification (Lemma 1).
The slack constructor leaves a residual of size at most `q * |Q|`.
Here `q = 1 - α`, and the explicit overhead is `1 / (1 - q ^ c)`. -/
theorem complete_of_slack
    (U : Finset E) (Satisfies : Finset E → D → Prop)
    (hmono : ∀ H K, H ⊆ K → ∀ d, Satisfies H d → Satisfies K d)
    (A B q c : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c) (threshold : ℕ)
    (small : ∀ Q : Finset D, Q.card ≤ threshold →
      ∃ H : Finset E, H ⊆ U ∧ (H.card : ℝ) ≤ A ∧ ∀ d ∈ Q, Satisfies H d)
    (slack : ∀ Q : Finset D, threshold < Q.card →
      ∃ (H : Finset E) (R : Finset D), H ⊆ U ∧ R ⊆ Q ∧
        (R.card : ℝ) ≤ q * Q.card ∧ (H.card : ℝ) ≤ B * (Q.card : ℝ) ^ c ∧
        ∀ d ∈ Q \ R, Satisfies H d)
    (P : Finset D) :
    ∃ H : Finset E, H ⊆ U ∧
      (H.card : ℝ) ≤ A + B / (1 - q ^ c) * (P.card : ℝ) ^ c ∧
      ∀ d ∈ P, Satisfies H d := by
  have hqc : q ^ c < 1 := Real.rpow_lt_one hq0 hq1 hc
  have hden : 0 < 1 - q ^ c := sub_pos.mpr hqc
  let C : ℝ := B / (1 - q ^ c)
  have hC : 0 ≤ C := div_nonneg hB hden.le
  have hCB : C * (1 - q ^ c) = B := div_mul_cancel₀ B (ne_of_gt hden)
  suffices ∀ n (Q : Finset D), Q.card = n →
      ∃ H : Finset E, H ⊆ U ∧ (H.card : ℝ) ≤ A + C * (Q.card : ℝ) ^ c ∧
        ∀ d ∈ Q, Satisfies H d from this P.card P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q hn
    by_cases hsmall : Q.card ≤ threshold
    · obtain ⟨H, hHU, hcost, hsat⟩ := small Q hsmall
      refine ⟨H, hHU, hcost.trans ?_, hsat⟩
      exact le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    · obtain ⟨H, R, hHU, hRQ, hRsize, hcost, hsat⟩ := slack Q (by omega)
      have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast (show 0 < Q.card by omega)
      have hRlt : R.card < Q.card := by
        have : (R.card : ℝ) < Q.card := lt_of_le_of_lt hRsize (by nlinarith)
        exact_mod_cast this
      obtain ⟨K, hKU, hKcost, hKsat⟩ := ih R.card (by omega) R rfl
      have hp : (R.card : ℝ) ^ c ≤ q ^ c * (Q.card : ℝ) ^ c := by
        calc
          _ ≤ (q * (Q.card : ℝ)) ^ c := Real.rpow_le_rpow (by positivity) hRsize hc.le
          _ = _ := Real.mul_rpow hq0 (by positivity)
      have hpC := mul_le_mul_of_nonneg_left hp hC
      have hcard : ((H ∪ K).card : ℝ) ≤ H.card + K.card := by
        exact_mod_cast card_union_le H K
      refine ⟨H ∪ K, union_subset hHU hKU, ?_, ?_⟩
      · have heq : C * (Q.card : ℝ) ^ c =
            B * (Q.card : ℝ) ^ c + C * (q ^ c * (Q.card : ℝ) ^ c) := by
          nlinarith [congrArg (fun x : ℝ => x * (Q.card : ℝ) ^ c) hCB]
        linarith
      · intro d hd
        by_cases hdr : d ∈ R
        · exact hmono K (H ∪ K) subset_union_right d (hKsat d hdr)
        · exact hmono H (H ∪ K) subset_union_left d (hsat d (mem_sdiff.mpr ⟨hd, hdr⟩))

/-- The geometric overhead is finite and positive for every fixed positive
exponent and fixed positive coverage fraction (including complete coverage). -/
theorem overhead_pos (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c) :
    0 < 1 / (1 - q ^ c) := by
  exact div_pos zero_lt_one (sub_pos.mpr (Real.rpow_lt_one hq0 hq1 hc))

end SlackSparsification
