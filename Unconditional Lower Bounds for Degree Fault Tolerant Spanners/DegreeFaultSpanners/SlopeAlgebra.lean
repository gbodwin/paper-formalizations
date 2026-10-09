import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fintype.EquivFin

/-!
# Moment-curve independence for the Wenger incidence construction

This file proves the algebraic core of Lemma 9 of arXiv:2607.07576v1.
The statement is valid over any field.  It makes distinctness explicit:
any at most k **distinct** slope vectors are independent.  Repeated slopes
must first be grouped; their aggregate coefficients then vanish.
-/

namespace DegreeFaultSpanners

open scoped BigOperators

variable {F : Type*} [Field F]

/-- The first `k` moments distinguish any at most `k` distinct field elements. -/
theorem coefficients_eq_zero_of_moments {n k : ℕ} (hnk : n ≤ k)
    (t c : Fin n → F) (ht : Function.Injective t)
    (hm : ∀ j : Fin k, (∑ i : Fin n, c i * t i ^ (j : ℕ)) = 0) :
    c = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht
  intro j
  exact hm ⟨j.val, Nat.lt_of_lt_of_le j.isLt hnk⟩

/-- A version of moment independence with an arbitrary finite indexing type. -/
theorem coefficients_eq_zero_of_moments_fintype {I : Type*} [Fintype I]
    {k : ℕ} (hcard : Fintype.card I ≤ k) (t c : I → F)
    (ht : Function.Injective t)
    (hm : ∀ j : Fin k, (∑ i : I, c i * t i ^ (j : ℕ)) = 0) :
    c = 0 := by
  classical
  let e := Fintype.equivFin I
  have h := coefficients_eq_zero_of_moments hcard (t ∘ e.symm) (c ∘ e.symm)
    (ht.comp e.symm.injective) (by
      intro j
      simpa only [Function.comp_apply] using
        (Equiv.sum_comp e.symm (fun i : I => c i * t i ^ (j : ℕ))).trans (hm j))
  funext i
  have hi := congrFun h (e i)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using hi

/-- Equal slopes in a vanishing sum have vanishing aggregate coefficient. -/
theorem grouped_coefficients_eq_zero [DecidableEq F] {r k : ℕ} (hrk : r ≤ k)
    (t c : Fin r → F)
    (hm : ∀ j : Fin k, (∑ i : Fin r, c i * t i ^ (j : ℕ)) = 0)
    (u : F) : (∑ i ∈ Finset.univ.filter (fun i => t i = u), c i) = 0 := by
  classical
  let S : Finset F := Finset.univ.image t
  let a : S → F := fun s => ∑ i ∈ Finset.univ.filter (fun i => t i = s.val), c i
  have hcard : Fintype.card S ≤ k := by
    calc
      Fintype.card S = S.card := Fintype.card_coe _
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := Finset.card_fin r
      _ ≤ k := hrk
  have ha : a = 0 := coefficients_eq_zero_of_moments_fintype hcard
    (fun s : S => s.val) a Subtype.val_injective (by
      intro j
      calc
        (∑ s : S, a s * s.val ^ (j : ℕ)) =
            ∑ s ∈ S, (∑ i ∈ Finset.univ.filter (fun i => t i = s), c i) *
              s ^ (j : ℕ) := by
          simpa only [a] using
            (Finset.sum_coe_sort S (fun s =>
              (∑ i ∈ Finset.univ.filter (fun i => t i = s), c i) * s ^ (j : ℕ)))
        _ = ∑ s ∈ S, ∑ i ∈ Finset.univ.filter (fun i => t i = s),
            c i * t i ^ (j : ℕ) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = ∑ i : Fin r, c i * t i ^ (j : ℕ) :=
          Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem t (Finset.mem_univ i)) _
        _ = 0 := hm j)
  by_cases hu : u ∈ S
  · have h := congrFun ha ⟨u, hu⟩
    exact h
  · have hn : ∀ i : Fin r, t i ≠ u := by
      intro i h
      apply hu
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩
    simp [hn]

/-- A nonzero coefficient cannot have a slope which occurs exactly once. -/
theorem no_singleton_slope {r k : ℕ} (hrk : r ≤ k) (t c : Fin r → F)
    (hc : ∀ i, c i ≠ 0)
    (hm : ∀ j : Fin k, (∑ i : Fin r, c i * t i ^ (j : ℕ)) = 0)
    (i : Fin r) : ∃ j : Fin r, j ≠ i ∧ t j = t i := by
  classical
  by_contra h
  have hnone : ∀ j : Fin r, j ≠ i → t j ≠ t i := by
    intro j hji htji
    exact h ⟨j, hji, htji⟩
  have hf : Finset.univ.filter (fun j => t j = t i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hji
      by_contra hne
      exact hnone j hne hji
    · rintro rfl
      rfl
  have hz := grouped_coefficients_eq_zero hrk t c hm (t i)
  rw [hf, Finset.sum_singleton] at hz
  exact hc i hz

end DegreeFaultSpanners
