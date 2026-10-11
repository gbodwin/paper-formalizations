import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The actual d-initialization construction used throughout Section 2. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Choose up to d neighbors per vertex and take the undirected union.
The finite graph is constructed, has at most nd edges, and every endpoint
of a missing original edge has initialized degree at least d. -/
theorem exists_initialization (G : SimpleGraph V) (d : ℕ) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card ≤ Fintype.card V * d ∧
      ∀ u v, G.Adj u v → ¬H.Adj u v → d ≤ H.degree u := by
  classical
  have hex (u : V) : ∃ S : Finset V, S ⊆ G.neighborFinset u ∧
      S.card = min d (G.degree u) := by
    apply exists_subset_card_eq
    simpa using min_le_right d (G.degree u)
  choose S hS hcard using hex
  let H : SimpleGraph V := {
    Adj := fun u v => v ∈ S u ∨ u ∈ S v
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun u h => by
      have hu : u ∈ S u := h.elim id id
      have ha : G.Adj u u := by simpa using hS u hu
      exact G.loopless u ha⟩ }
  have hHG : H ≤ G := by
    intro u v h
    rcases h with h | h
    · simpa using hS u h
    · exact (show G.Adj v u by simpa using hS v h).symm
  let E := univ.biUnion fun u => (S u).image fun v => s(u,v)
  have hE : H.edgeFinset ⊆ E := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have ha : H.Adj u v := by simpa using he
      rcases ha with ha | ha
      · exact mem_biUnion.mpr ⟨u, mem_univ _, mem_image.mpr ⟨v, ha, rfl⟩⟩
      · exact mem_biUnion.mpr ⟨v, mem_univ _, mem_image.mpr ⟨u, ha, Sym2.eq_swap⟩⟩
  have hsize : H.edgeFinset.card ≤ Fintype.card V * d := by
    calc
      _ ≤ E.card := card_le_card hE
      _ ≤ ∑ u : V, ((S u).image fun v => s(u,v)).card := card_biUnion_le
      _ ≤ ∑ u : V, d := by
        apply sum_le_sum
        intro u _
        exact card_image_le.trans ((hcard u).trans_le (min_le_left _ _))
      _ = _ := by simp
  refine ⟨H, hHG, hsize, ?_⟩
  intro u v huv hmissing
  have hdG : d ≤ G.degree u := by
    by_contra hd
    have hc : (S u).card = (G.neighborFinset u).card := by
      rw [hcard u, min_eq_right (by omega)]
      simp
    have heq : S u = G.neighborFinset u := eq_of_subset_of_card_le (hS u) (by omega)
    apply hmissing
    exact Or.inl (by simpa [heq] using huv)
  have hsubset : S u ⊆ H.neighborFinset u := by
    intro v hv
    exact mem_neighborFinset.mpr (Or.inl hv)
  have hcount := card_le_card hsubset
  simpa [hcard u, min_eq_left hdG] using hcount

end SlackSparsification
