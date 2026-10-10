import GreedyShortcuts.FinitePotential

/-! Finite guard descent with additive rank depletion. This arithmetic
principle is separate from construction of bad graph windows. -/
namespace GreedyShortcuts.FiniteGuardDescent

variable {A : Type*} (rank distance : A → ℕ) (Good : A → Prop)

/-- A linear invariant preserves at least three quarters of the original
length while a bad state strictly reduces its finite rank. -/
theorem exists_good (L K k : ℕ) (hL : 0<L) (hk : 0<k)
    (hLK : L≤K) (hscale : 64*K*k≤L^2)
    (step : ∀ x, L≤2*distance x → ¬Good x →
      ∃ y, rank y+distance x≤rank x+k ∧ distance x≤distance y+5*k)
    (x₀ : A) (hrank : rank x₀≤K) (hdist : L≤distance x₀) :
    ∃ x, Good x ∧ L≤2*distance x := by
  have hkL : 64*k≤L := by
    have hm := Nat.mul_le_mul_right (64*k) hLK
    nlinarith
  have aux : ∀ n,∀ x, rank x=n →
      L^2+16*k*rank x≤L*distance x+16*k*K →
      ∃ y, Good y ∧ L≤2*distance y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hr hinv
      have hhigh : 3*L≤4*distance x := by nlinarith
      have hactive : L≤2*distance x := by omega
      by_cases hg : Good x
      · exact ⟨x,hg,hactive⟩
      · obtain ⟨y,hry,hdy⟩ := step x hactive hg
        have hdrop : rank y<rank x := by omega
        have hinvy : L^2+16*k*rank y≤L*distance y+16*k*K := by
          have ha := Nat.mul_le_mul_left L hdy
          have hb := Nat.mul_le_mul_left (16*k) hry
          have hc : 5*k*L+16*k*k≤16*k*distance x := by
            have hm1 := Nat.mul_le_mul_left (4*k) hhigh
            have hm2 := Nat.mul_le_mul_left k hkL
            nlinarith
          nlinarith
        exact ih (rank y) (by omega) y rfl hinvy
  apply aux (rank x₀) x₀ rfl
  nlinarith [Nat.mul_le_mul_left L hdist,Nat.mul_le_mul_left (16*k) hrank]

end GreedyShortcuts.FiniteGuardDescent
