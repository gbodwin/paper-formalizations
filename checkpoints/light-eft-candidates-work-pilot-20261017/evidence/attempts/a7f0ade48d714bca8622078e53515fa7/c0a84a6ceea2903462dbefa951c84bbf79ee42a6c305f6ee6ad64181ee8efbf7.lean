import LightEFTSpanners.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-! The finite fault pigeonhole step for the source's 2f−1 lower construction.
No cycles or connectivity are asserted to exist by this counting lemma. -/
namespace LightEFTSpanners
open Finset SimpleGraph
variable {I E : Type*} [DecidableEq E]

theorem exists_at_most_one_fault (indices : Finset I) (edges : I → Finset E)
    (F : Finset E)
    (hdis : (indices : Set I).PairwiseDisjoint edges)
    (hF : F.card < 2*indices.card) :
    ∃ i∈indices,(F ∩ edges i).card≤1 := by
  classical
  by_contra! hh
  have hpair : (indices : Set I).PairwiseDisjoint (fun i => F ∩ edges i) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono inter_subset_right inter_subset_right
  have hsub : indices.biUnion (fun i => F ∩ edges i) ⊆ F := by
    intro e he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    exact (mem_inter.mp hi).1
  have hcount := card_le_card hsub
  rw [card_biUnion hpair] at hcount
  have hlo : 2*indices.card ≤ ∑ i∈indices,(F ∩ edges i).card := by
    calc
      _ = ∑ _i∈indices,2 := by simp; omega
      _ ≤ _ := sum_le_sum (fun i hi => by have := hh i hi; omega)
  omega

end LightEFTSpanners
