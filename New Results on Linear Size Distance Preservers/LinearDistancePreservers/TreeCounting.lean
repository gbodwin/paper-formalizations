import LinearDistancePreservers.LazyTreeSelection

/-! The `2|D|` bound for branching edges of a pruned parent tree. -/
namespace LinearDistancePreservers.LazyTreeSelection
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def children (f : V → Option V) (u : V) : Finset V :=
  univ.filter fun v => f v = some u

theorem single_iff_card (f : V → Option V) (u : V) :
    Single f u ↔ (children f u).card = 1 := by
  classical
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨v, hv, hu⟩
    refine ⟨v, ?_⟩
    ext z
    simp only [children, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun hz => hu z hz, fun hz => hz ▸ hv⟩
  · rintro ⟨v, hv⟩
    have he (z : V) : f z = some u ↔ z = v := by
      have := Finset.ext_iff.mp hv z
      simpa [children] using this
    exact ⟨v, (he v).mpr rfl, fun z hz => (he z).mp hz⟩

theorem sum_children (f : V → Option V) :
    ∑ u, (children f u).card = (support f).card := by
  classical
  simp only [children, support, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  cases h : f v with
  | none => simp
  | some u => simp

noncomputable def branchEdges (f : V → Option V) : Finset (V × V) :=
  univ.filter fun e => f e.2 = some e.1 ∧ ¬ Single f e.1

theorem branchEdges_card (f : V → Option V) :
    (branchEdges f).card = ∑ u, if Single f u then 0 else (children f u).card := by
  classical
  simp only [branchEdges, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro u hu
  by_cases h : Single f u <;>
    simp only [h, if_false, if_true, not_false_eq_true, not_true_eq_false,
      and_true, and_false, sum_const_zero, children, card_eq_sum_ones, sum_filter]

/-- The argument uses only a parent function and the fact that every
non-root leaf is a demand endpoint; no edge-count bound is assumed. -/
theorem branchEdges_le_two_demands (f : V → Option V) (D : Finset V)
    (hleaf : ∀ v, f v ≠ none → (∀ z, f z ≠ some v) → v ∈ D) :
    (branchEdges f).card ≤ 2 * D.card := by
  classical
  let N : Finset V := univ.filter fun u => (children f u).card ≠ 0
  have hsub : support f ⊆ N ∪ D := by
    intro v hv
    by_cases hd : (children f v).card = 0
    · refine mem_union_right _ (hleaf v (mem_filter.mp hv).2 ?_)
      intro z hz
      have hzmem : z ∈ children f v := by simp [children, hz]
      simpa [Finset.card_eq_zero.mp hd] using hzmem
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hd⟩)
  have hS : (support f).card ≤ N.card + D.card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hpoint (u : V) :
      (if Single f u then 0 else (children f u).card) +
        2 * (if (children f u).card = 0 then 0 else 1) ≤ 2 * (children f u).card := by
    rw [single_iff_card]
    split_ifs <;> omega
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun u _ => hpoint u)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_children, ← branchEdges_card] at hsum
  have hN : (∑ u : V, if (children f u).card = 0 then 0 else 1) = N.card := by
    simp only [N, card_eq_sum_ones, sum_filter, ite_not]
  rw [hN] at hsum
  omega

end LinearDistancePreservers.LazyTreeSelection
