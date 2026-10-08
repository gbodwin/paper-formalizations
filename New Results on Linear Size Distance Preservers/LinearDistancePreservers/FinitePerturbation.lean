import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The finite small-epsilon argument in Lemma 7. A single positive scale
preserves every strict lexicographic comparison in a finite collection.
This proves the analytic perturbation step; it does not assume that the
obstacle-product graph has the required projection or path correspondence. -/
namespace LinearDistancePreservers
open Finset

/-- One positive scale works uniformly, including all smaller positive
scales. Ties in the primary cost are settled by the secondary cost. -/
theorem exists_uniform_perturbation {X : Type*} [Fintype X]
    (primary secondary : X → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∀ x y,
      (primary x < primary y ∨
        (primary x = primary y ∧ secondary x < secondary y)) →
      primary x + δ * secondary x < primary y + δ * secondary y := by
  classical
  let A : Finset (X × X) := univ.filter fun e => primary e.1 < primary e.2
  let gap : X × X → ℝ := fun e =>
    (primary e.2 - primary e.1) / (|secondary e.2 - secondary e.1| + 1)
  have hgap : ∀ e ∈ A, 0 < gap e := by
    intro e he
    exact div_pos (sub_pos.mpr (mem_filter.mp he).2) (by positivity)
  have hex : ∃ ε : ℝ, 0 < ε ∧ ∀ e ∈ A, ε < gap e := by
    by_cases hA : A.Nonempty
    · obtain ⟨e, he, hmin⟩ := exists_min_image A gap hA
      refine ⟨gap e / 2, half_pos (hgap e he), ?_⟩
      intro f hf
      exact (half_lt_self (hgap e he)).trans_le (hmin f hf)
    · exact ⟨1, by norm_num, by simp [not_nonempty_iff_eq_empty.mp hA]⟩
  obtain ⟨ε, hε, hbound⟩ := hex
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε x y hxy
  rcases hxy with hp | ⟨hp, hs⟩
  · have hb := lt_of_le_of_lt hδε (hbound (x,y) (by simp [A, hp]))
    have hden : 0 < |secondary y - secondary x| + 1 := by positivity
    have hmul : δ * (|secondary y - secondary x| + 1) < primary y - primary x :=
      (lt_div_iff₀ hden).mp hb
    have hab := neg_abs_le (secondary y - secondary x)
    have hprod := mul_le_mul_of_nonneg_left hab hδ.le
    nlinarith
  · rw [hp]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hs hδ) _

/-- Finite lexicographic unique minimizers become genuine unique minimizers
of scalar costs. `valid` permits many endpoint classes in one finite set. -/
theorem exists_scalar_unique_minimizers {X I : Type*} [Fintype X]
    (primary secondary : X → ℝ) (chosen : I → X) (valid : I → X → Prop)
    (hmin : ∀ i x, valid i x → x ≠ chosen i →
      primary (chosen i) < primary x ∨
      (primary (chosen i) = primary x ∧ secondary (chosen i) < secondary x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∀ i x, valid i x →
      primary (chosen i) + δ * secondary (chosen i) ≤ primary x + δ * secondary x ∧
      (primary x + δ * secondary x =
        primary (chosen i) + δ * secondary (chosen i) → x = chosen i) := by
  obtain ⟨ε, hε, hcompare⟩ := exists_uniform_perturbation primary secondary
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε i x hx
  by_cases he : x = chosen i
  · subst x
    exact ⟨le_rfl, fun _ => rfl⟩
  · have hlt := hcompare δ hδ hδε (chosen i) x (hmin i x hx he)
    exact ⟨hlt.le, fun h => False.elim (hlt.ne h.symm)⟩

end LinearDistancePreservers
