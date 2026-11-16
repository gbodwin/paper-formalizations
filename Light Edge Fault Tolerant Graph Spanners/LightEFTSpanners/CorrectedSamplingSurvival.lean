import LightEFTSpanners.CorrectedSamplingAvoidance

/-! Candidate survival for the deterministic host sampler in Lemma 27.
This is the literal `1/f` Bernoulli experiment, distinct from empirical voting.
The candidate is excluded from its own blocker set. -/

namespace LightEFTSpanners.CorrectedDeterministicSampling
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [DecidableEq α]
attribute [local instance] Classical.propDecidable

/-- Selecting one candidate is independent of avoiding all other specified
identities, derived from the finite mass rather than assumed independence. -/
theorem inclusion_avoiding_mass (U B : Finset α) (p : ℝ) {e : α}
    (he : e∈U) (hne : e∉B) :
    (∑ S∈U.powerset with e∈S ∧ Disjoint B S, mass U p S) =
      p*(∑ A∈(U.erase e).powerset with Disjoint A B, mass (U.erase e) p A) := by
  have hdis (S : Finset α) (hSU : S⊆U) :
      Disjoint (S∩U.erase e) B ↔ Disjoint S B := by
    constructor
    · intro hd
      apply disjoint_left.mpr
      intro a haS haB
      have hae : a≠e := fun hh => hne (hh ▸ haB)
      exact disjoint_left.mp hd (mem_inter.mpr ⟨haS,mem_erase.mpr ⟨hae,hSU haS⟩⟩) haB
    · intro hd
      exact hd.mono_left inter_subset_left
  have hr := sum_mass_mem_restrict U (U.erase e) p
    (fun A => if Disjoint A B then (1:ℝ) else 0) (erase_subset _ _) he (by simp)
  calc
    _ = ∑ S∈U.powerset, mass U p S*
        (if e∈S then (if Disjoint (S∩U.erase e) B then (1:ℝ) else 0) else 0) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S hS
      simp only [hdis S (mem_powerset.mp hS)]
      by_cases heS : e∈S
      · by_cases hd : Disjoint B S
        · have hd' : Disjoint S B := hd.symm
          simp [heS,hd,hd']
        · have hd' : ¬Disjoint S B := fun hh => hd hh.symm
          simp [heS,hd,hd']
      · simp [heS]
    _ = p*(∑ A∈(U.erase e).powerset,
        mass (U.erase e) p A*(if Disjoint A B then (1:ℝ) else 0)) := hr
    _ = _ := by simp only [mul_ite,mul_one,mul_zero,←sum_filter]

/-- A candidate with at most f blockers survives inclusion and deletion with
probability at least `1/(4f)` at the paper's actual rate `1/f`. -/
theorem survival_lower (U B : Finset α) (f : ℕ) (hf : 2≤f) {e : α}
    (he : e∈U) (hne : e∉B) (hcap : B.card≤f) :
    1/(4*(f:ℝ)) ≤ ∑ S∈U.powerset with e∈S ∧ Disjoint B S, mass U (1/(f:ℝ)) S := by
  rw [inclusion_avoiding_mass U B (1/(f:ℝ)) he hne]
  have hh := mul_le_mul_of_nonneg_left
    (CorrectedSampling.fault_avoidance (U.erase e) B f hf hcap)
    (show (0:ℝ)≤1/(f:ℝ) by positivity)
  have heq : (1/(f:ℝ))*((1:ℝ)/4)=1/(4*(f:ℝ)) := by ring
  rwa [heq] at hh

end LightEFTSpanners.CorrectedDeterministicSampling
