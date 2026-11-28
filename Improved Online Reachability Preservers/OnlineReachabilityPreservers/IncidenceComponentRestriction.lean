import OnlineReachabilityPreservers.IncidenceDegreeComponentCleaning
import OnlineReachabilityPreservers.ShortReturnOverflow

/-! Incidence-component cleaning after deleting incidences. -/

namespace OnlineReachabilityPreservers

open Finset

/-- A restriction keeping at least two thirds of the incidences may use
its own deletion components with the original widths. Both budgets and
all four original-average caps hold with one eighteenth of the mass. -/
theorem regularization_list_frozen_of_incidence_component_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ kept i → (incidenceVertexDeletionGroup kept x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ kept i, (incidenceRowDeletionGroup kept i x).card ≤ 4*M/p)
    (retained : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let K := ∑ i, (kept i).length
  have upper : K ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptLegal := localOrderAdmissible_of_sublist simple sub legal
  refine regularization_list_frozen_of_incidence_deletion_group_rooms_of_mass (retention := 18)
    kept keptSimple keptLegal hn hp dense long upper degreeRoom rowRoom ?_
  exact fun _ _ _ paid lossV lossI =>
    shortReturnTrim_mass_of_two_thirds hn hp (hn.trans_le dense) retained upper paid lossV lossI

/-- The same restriction certificate gives the literal frozen witness
for distinct nonempty simple input at cutoffs at least two. -/
theorem regularization_literal_frozen_of_incidence_component_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ kept i → (incidenceVertexDeletionGroup kept x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ kept i, (incidenceRowDeletionGroup kept i x).card ≤ 4*M/p)
    (retained : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨v,vFits,q,qFits,clean,injective,nonempty,cleanSimple,cleanLegal,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (retention := 18) rows distinct (fun i => (valid i).1)
      (fun i => (valid i).2) legal two hn hp dense (by decide) (fun long =>
        regularization_list_frozen_of_incidence_component_restriction rows (fun i => (valid i).2) legal
          hn hp dense long kept sub degreeRoom rowRoom retained)
  exact ⟨v,vFits,q,qFits,clean,injective,fun i => ⟨nonempty i,cleanSimple i⟩,cleanLegal,mass,upper,caps⟩

end OnlineReachabilityPreservers
