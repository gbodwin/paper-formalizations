import OnlineReachabilityPreservers.FrozenMatchedPartners
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass

/-! Distinct starting-average witnesses from two compatible classes at half cutoff five. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The two-class repair yields a literal witness with both budgets and
all four starting-average caps. In the low-mass branch one can choose
a witness excluding full bridges at every cutoff. -/
theorem regularization_literal_frozen_half_five_of_two_class_mass {n p : ℕ}
    (paths kept : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (sub : ∀ i, (kept i).Sublist (paths i))
    (classes : Fin p → Bool)
    (separated : ∀ {i j x y}, i ≠ j → Before kept i x y → Before kept j y x → classes i ≠ classes j)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (retained : 6*(∑ i, (paths i).length) ≤ 7*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,all,retain,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(all 5).halfFree,by omega,upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_iff.mpr (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
    regularization_list_frozen_half_five_of_two_class_mass paths kept (fun i => (valid i).2)
      free sub classes (fun {_ _ _ _} => separated) hn hp dense long retained
  have highMean : 4*p < M := by have width := le_max_right n p; omega
  obtain ⟨oneToOne, nonempty⟩ :=
    frozen_length_distinct_of_large_mean rowsSimple rowsFree (by decide) hp highMean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,retain,upper,caps⟩

/-- Join two row labels when their rows give opposite comparisons
of one pair of vertices. -/
def listReversalGraph {I V : Type*} [DecidableEq V] (paths : I → List V) : SimpleGraph I where
  Adj a b := a ≠ b ∧ ∃ x y, Before paths a x y ∧ Before paths b y x
  symm := ⟨by
    rintro a b ⟨different,x,y,forward,backward⟩
    exact ⟨different.symm,y,x,backward,forward⟩⟩
  loopless := ⟨fun _ on => on.1 rfl⟩

/-- A bipartite reversal graph supplies the two compatible row classes
with no deletion. Forests are included by acyclic bipartiteness. -/
theorem regularization_literal_frozen_half_five_of_bipartite_reversal_graph {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (bipartite : (listReversalGraph paths).IsBipartite)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨color⟩ := bipartite
  let labels := finTwoEquiv ∘ color
  apply regularization_literal_frozen_half_five_of_two_class_mass paths paths distinct valid free
    (fun _ => List.Sublist.refl _) labels _ hn hp dense (Nat.mul_le_mul_right _ (by decide))
  intro i j x y different forward backward same
  exact color.valid (show (listReversalGraph paths).Adj i j from ⟨different,x,y,forward,backward⟩)
    (finTwoEquiv.injective same)

end OnlineReachabilityPreservers
