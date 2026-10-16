import SlackSparsification.DirectedComplete

/-! Actual ambient-arc support for the recovered nonnegative weighted theorem.
The original partial modules are preserved separately by their recovery manifest. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal ENNReal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The directed input consists of the allowed ordered arcs supported by K. -/
noncomputable def inputArcs (K : SimpleGraph V) (A : V → V → Prop) : Finset (V × V) :=
  univ.filter fun e => K.Adj e.1 e.2 ∧ A e.1 e.2

omit [Fintype V] [DecidableEq V] in
/-- Removing pairs outside the ambient graph cannot change any allowed walk. -/
theorem distance_filter_ambient (K : SimpleGraph V) (F : Finset (V × V))
    (w : V → V → ℝ≥0) (s t : V) :
    distance K (edgeRel (F.filter fun e => K.Adj e.1 e.2)) w s t =
      distance K (edgeRel F) w s t := by
  unfold distance
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, fun d hd => (mem_filter.mp (hp d hd)).1, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, fun d hd => mem_filter.mpr ⟨hp d hd, d.adj⟩, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- Finite arc weights make finite distance equivalent to actual reachability.
Unreachable demands retain infinity; zero weights cause no exception. -/
theorem distance_ne_top_iff (K : SimpleGraph V) (A : V → V → Prop)
    (w : V → V → ℝ≥0) (s t : V) :
    distance K A w s t ≠ ⊤ ↔ ∃ p : K.Walk s t, Allowed A p := by
  constructor
  · intro h
    by_contra hn
    exact h (distance_of_no_walk w hn)
  · rintro ⟨p, hp⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (distance_le_cost w p hp)

/-- Complete directed nonnegative-weight distance preserver on actual input
arcs, with no supplied shortest paths, trees, samples, or successful preserver.
The vertex type and demand set may be empty. -/
theorem exists_exact_input_preserver (K : SimpleGraph V) (A : V → V → Prop)
    (w : V → V → ℝ≥0) (P : Finset (V × V)) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
      (F.card : ℝ) ≤ (14 * Fintype.card V / (1 - (1 / 2 : ℝ) ^ (1 / 2 : ℝ))) *
        (P.card : ℝ) ^ (1 / 2 : ℝ) ∧
      ∀ st ∈ P, distance K (edgeRel F) w st.1 st.2 = distance K A w st.1 st.2 := by
  obtain ⟨F, hFA, hsize, hdist⟩ := exists_exact_complete K A w P
  refine ⟨F.filter (fun e => K.Adj e.1 e.2), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hF, hK⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, hK, hFA e hF⟩
  · have hc : ((F.filter fun e => K.Adj e.1 e.2).card : ℝ) ≤ F.card := by
      exact_mod_cast card_filter_le F (fun e : V × V => K.Adj e.1 e.2)
    exact hc.trans hsize
  · intro st hst
    rw [distance_filter_ambient]
    exact hdist st hst

end SlackSparsification.Directed
