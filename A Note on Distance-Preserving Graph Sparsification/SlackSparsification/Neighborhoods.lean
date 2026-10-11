import SlackSparsification.Hitting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic

/-! The paper's Lemma 6 with actual unweighted graph distances and explicit
constant 1/3. Missing path edges are indexed in source-to-target order, so
one source endpoint is counted per missing edge, without duplicates. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Subpaths of an actual shortest walk realize the index difference. -/
theorem shortest_index_distance (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hsub := ((p.drop i).isSubwalk_take (j - i)).trans (p.isSubwalk_drop i)
  have h := SimpleGraph.length_eq_dist_of_subwalk hp hsub
  simpa only [Walk.take_length, Walk.drop_length, Walk.drop_getVert,
    Nat.add_sub_of_le hij, Nat.min_eq_left (show j - i ≤ p.length - i by omega)] using h.symm

/-- No vertex has neighbors at positions differing by more than two on a
shortest walk: otherwise the two-edge route through that vertex is shorter. -/
theorem neighbors_span_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t)
    (y : V) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length)
    (hi : G.Adj (p.getVert i) y) (hj' : G.Adj (p.getVert j) y) : j - i ≤ 2 := by
  have h := G.dist_le (Walk.cons hi (Walk.cons hj'.symm Walk.nil))
  simpa [shortest_index_distance G p hp i j hij hj] using h

theorem card_le_three_of_span (S : Finset ℕ)
    (h : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → j - i ≤ 2) : S.card ≤ 3 := by
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hsub : S ⊆ Icc m (m + 2) := by
      intro j hj
      have hm : m ≤ j := min'_le S j hj
      have hd := h m (min'_mem S hs) j hj hm
      exact mem_Icc.mpr ⟨hm, by omega⟩
    have hc := card_le_card hsub
    simpa using hc
  · simp [not_nonempty_iff_eq_empty.mp hs]

/-- At most three indexed vertices of a shortest path are adjacent to y. -/
theorem adjacent_index_card_le_three (G H : SimpleGraph V) (hHG : H ≤ G)
    {s t : V} (p : G.Walk s t) (hp : p.length = G.dist s t)
    (I : Finset ℕ) (hI : I ⊆ range p.length) (y : V) :
    (I.filter fun i => H.Adj (p.getVert i) y).card ≤ 3 := by
  apply card_le_three_of_span
  intro i hi j hj hij
  have hi' := mem_filter.mp hi
  have hj' := mem_filter.mp hj
  exact neighbors_span_two G p hp y i j hij
    (Nat.le_of_lt (mem_range.mp (hI hj'.1))) (hHG hi'.2) (hHG hj'.2)

/-- Explicit Lemma 6: d times the number of selected missing edges is at
most three times the cardinality of the union of their initialized
source-endpoint neighborhoods. The degree premise is exactly what a
`d`-initialization supplies at every missing-edge endpoint. -/
theorem path_neighborhood_count (G H : SimpleGraph V) (hHG : H ≤ G)
    {s t : V} (p : G.Walk s t) (hp : p.length = G.dist s t)
    (I : Finset ℕ) (hI : I ⊆ range p.length) (d : ℕ)
    (hdegree : ∀ i ∈ I, d ≤ H.degree (p.getVert i)) :
    d * I.card ≤ 3 * (I.biUnion fun i => H.neighborFinset (p.getVert i)).card := by
  let N := fun i => H.neighborFinset (p.getVert i)
  let U := I.biUnion N
  have hN : ∀ i ∈ I, N i ⊆ U := by
    intro i hi v hv
    exact mem_biUnion.mpr ⟨i, hi, hv⟩
  have hsum := sum_hits U I N hN
  have hover : ∀ y ∈ U, (hits I N y).card ≤ 3 := by
    intro y _
    simpa [hits, N] using adjacent_index_card_le_three G H hHG p hp I hI y
  calc
    d * I.card = ∑ _ ∈ I, d := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ I, (N i).card := by
      apply sum_le_sum
      intro i hi
      simpa [N] using hdegree i hi
    _ = ∑ y ∈ U, (hits I N y).card := hsum.symm
    _ ≤ ∑ _ ∈ U, 3 := sum_le_sum hover
    _ = 3 * U.card := by simp [Nat.mul_comm]

end SlackSparsification
