import LengthExpander.MatchingPermutations
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
attribute [local instance] Classical.propDecidable

theorem moved_matching_eq_indicator {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (i : ℕ) (v : V) :
    moved (matchingPermutation G index H i) v =
      if (∃ u, G.Adj u v ∧ index s(u,v) = i) then 1 else 0 := by
  classical
  change (if stageMate G index i v = v then 0 else 1) = _
  by_cases hex : ∃ u, G.Adj u v ∧ index s(u,v) = i
  · obtain ⟨u,hu,hi⟩ := hex
    have hmate := stageMate_of_edge H hu hi
    have hne : stageMate G index i v ≠ v := fun he => hu.ne (hmate.symm.trans he)
    simp [hne, show ∃ u, G.Adj u v ∧ index s(u,v) = i from ⟨u,hu,hi⟩]
  · simp [stageMate, hex]

variable [Fintype V]

/-- Proper matching labels count each incident edge in exactly one stage. -/
theorem sum_moved_at_vertex {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (K : ℕ) (hK : ∀ e ∈ G.edgeFinset, index e < K) (v : V) :
    (∑ i ∈ range K, moved (matchingPermutation G index H i) v) = G.degree v := by
  classical
  let P := fun i => ∃ u, G.Adj u v ∧ index s(u,v) = i
  have hsets : (range K).filter P = (G.neighborFinset v).image (fun u => index s(u,v)) := by
    ext i
    constructor
    · intro hi
      obtain ⟨_,u,hu,heq⟩ := mem_filter.mp hi
      exact mem_image.mpr ⟨u, (G.mem_neighborFinset v u).mpr hu.symm, heq⟩
    · intro hi
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
      have hadj := (G.mem_neighborFinset v u).mp hu
      exact mem_filter.mpr ⟨mem_range.mpr (hK s(u,v) (by simpa using hadj.symm)),
        ⟨u,hadj.symm,rfl⟩⟩
  calc
    (∑ i ∈ range K, moved (matchingPermutation G index H i) v) = ((range K).filter P).card := by
      simp only [moved_matching_eq_indicator H, card_eq_sum_ones, sum_filter, P]
      apply sum_congr rfl
      intro i hi
      by_cases hex : ∃ u, G.Adj u v ∧ index s(u,v) = i <;> simp [hex]
    _ = ((G.neighborFinset v).image (fun u => index s(u,v))).card := congrArg Finset.card hsets
    _ = (G.neighborFinset v).card := by
      apply card_image_of_injOn
      intro u hu z hz heq
      exact H u z v ((G.mem_neighborFinset v u).mp hu).symm
        ((G.mem_neighborFinset v z).mp hz).symm heq
    _ = G.degree v := G.card_neighborFinset_eq_degree v

/-- The exact conservation law used in Lemma 3.4, on the actual graph. -/
theorem graph_hiker_total_travel {index : Sym2 V → ℕ} (H : MatchingLabels G index)
    (K : ℕ) (hK : ∀ e ∈ G.edgeFinset, index e < K) :
    (∑ v, hikerTravel (matchingPermutation G index H) K v) = 2 * G.edgeFinset.card := by
  rw [hiker_total_travel]
  simp only [movedCount]
  rw [sum_comm]
  simp_rw [sum_moved_at_vertex H K hK]
  exact G.sum_degrees_eq_twice_card_edges

/-- An explicit long monotone walk exists under the weak counting density
threshold. The finite upper label cutoff K is supplied only to delimit the
actual matching process; no walk/count conclusion is assumed. -/
theorem exists_long_increasing_walk [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) (K r : ℕ)
    (hK : ∀ e ∈ G.edgeFinset, index e < K)
    (hm : Fintype.card V * r ≤ 2 * G.edgeFinset.card) :
    ∃ u v, ∃ p : G.Walk u v, Increasing index p ∧ r ≤ p.length := by
  have hc : Fintype.card V * r ≤ ∑ i ∈ range K, movedCount (matchingPermutation G index H i) := by
    rw [← hiker_total_travel, graph_hiker_total_travel H K hK]
    exact hm
  obtain ⟨u,hu⟩ := exists_hiker_long (matchingPermutation G index H) K r hc
  refine ⟨u,_,graphHikerWalk H K u,graphHikerWalk_increasing H K u,?_⟩
  simpa only [graphHikerWalk, hikerWalk_length] using hu

theorem increasing_take {index : Sym2 V → ℕ} {u v : V} {p : G.Walk u v}
    (hp : Increasing index p) (r : ℕ) : Increasing index (p.take r) := by
  have h := List.Pairwise.take (i := r) hp
  simpa only [Increasing, Walk.edges_take, List.map_take] using h

/-- Exact finite weak counting lemma, without a stage cutoff hypothesis.
A nonempty vertex set is necessary in the zero-edge, r=0 case. -/
theorem weak_counting_walk [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) (r : ℕ)
    (hm : Fintype.card V * r ≤ 2 * G.edgeFinset.card) :
    ∃ u v, ∃ p : G.Walk u v, Increasing index p ∧ p.length = r := by
  classical
  let K := G.edgeFinset.sup index + 1
  have hK : ∀ e ∈ G.edgeFinset, index e < K := by
    intro e he
    exact Nat.lt_succ_of_le (Finset.le_sup he)
  obtain ⟨u,v,p,hp,hlen⟩ := exists_long_increasing_walk H K r hK hm
  refine ⟨u,p.getVert r,p.take r,increasing_take hp r,?_⟩
  simpa only [Walk.take_length, inf_eq_left.mpr hlen]

end LengthExpander
