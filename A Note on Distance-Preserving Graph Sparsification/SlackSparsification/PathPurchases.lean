import SlackSparsification.Attachments
import SlackSparsification.PairConnector
import Mathlib.Tactic

namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- Buy short paths over an existing initial graph. -/
theorem exists_short_path_purchase (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (m : ℕ) (hshort : ∀ i ∈ P, (missingIndices H₀ (p i)).card ≤ m) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card ≤ H₀.edgeFinset.card + P.card * m ∧
      ∀ i ∈ P, H.edist (src i) (dst i) = G.edist (src i) (dst i) := by
  classical
  let F := fun i => (p i).edges.toFinset \ H₀.edgeFinset
  let E := H₀.edgeFinset ∪ P.biUnion F
  let H := graphOfEdges E
  have hE : E ⊆ G.edgeFinset := by
    apply union_subset (edgeFinset_mono h₀G)
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact mem_edgeFinset.mpr ((p i).edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp hi).1))
  have hHG : H ≤ G := graphOfEdges_le hE
  have h₀H : H₀ ≤ H := le_graphOfEdges subset_union_left
  refine ⟨H, hHG, ?_, ?_⟩
  · have hc : (P.biUnion F).card ≤ P.card * m := calc
      _ ≤ ∑ i ∈ P, (F i).card := card_biUnion_le
      _ ≤ ∑ _ ∈ P, m := sum_le_sum (fun i hi => (missing_edges_card_le H₀ (p i)).trans (hshort i hi))
      _ = _ := by simp
    exact (graphOfEdges_card_le E).trans ((card_union_le _ _).trans (Nat.add_le_add_left hc _))
  · intro i hi
    apply captured_path_distance hHG (p i) (hp i)
    apply captured_edges_of_purchase h₀H
    intro e he
    have heE : e ∈ E := mem_union_right _ (mem_biUnion.mpr ⟨i, hi, he⟩)
    exact graphOfEdges_mem (hE heE) heE

/-- Long missing-edge paths are handled by actual shortest-path trees;
at least half are preserved with additive error two. -/
theorem exists_long_path_purchase (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d K : ℕ) (hd : 0 < d)
    (hdegree : ∀ u v, G.Adj u v → ¬H₀.Adj u v → 3 * d ≤ H₀.degree u)
    (hlong : ∀ i ∈ P, K < (missingIndices H₀ (p i)).card) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 2 * Q.card ∧
      H.edgeFinset.card ≤ H₀.edgeFinset.card +
        Fintype.card V * (2 * Fintype.card V / (d * (K + 1)) + 1) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 2 := by
  classical
  let M := fun i => missingIndices H₀ (p i)
  let N := fun i => (M i).biUnion fun j => H₀.neighborFinset ((p i).getVert j)
  have hN (i : D) (hi : i ∈ P) : d * (K + 1) ≤ (N i).card := by
    have hc := path_neighborhood_count G H₀ h₀G (p i) (hp i) (M i)
      (missingIndices_subset H₀ (p i)) (3 * d) (by
        intro j hj
        have hj' := mem_filter.mp hj
        exact hdegree _ _ ((p i).adj_getVert_succ (mem_range.mp hj'.1)) hj'.2)
    have hm := Nat.mul_le_mul_left d (show K + 1 ≤ (M i).card from hlong i hi)
    change 3 * d * (M i).card ≤ 3 * (N i).card at hc
    nlinarith
  obtain ⟨S, Q, _, hSsize, hQP, hhalf, hhit⟩ := exists_half_hitting_set
    (univ : Finset V) univ_nonempty P N (d * (K + 1)) (by positivity)
    (by intro i _; exact subset_univ _) hN
  choose T hTG hTsize hTdist using fun r : V => exists_shortest_path_tree G r
  let E := H₀.edgeFinset ∪ S.biUnion (fun r => (T r).edgeFinset)
  let H := graphOfEdges E
  have hE : E ⊆ G.edgeFinset := by
    apply union_subset (edgeFinset_mono h₀G)
    intro e he
    obtain ⟨r, _, hr⟩ := mem_biUnion.mp he
    exact edgeFinset_mono (hTG r) hr
  have hHG : H ≤ G := graphOfEdges_le hE
  have hTH (r : V) (hr : r ∈ S) : T r ≤ H := le_graphOfEdges (by
    intro e he
    exact mem_union_right _ (mem_biUnion.mpr ⟨r, hr, he⟩))
  refine ⟨H, Q, hHG, hQP, hhalf, ?_, ?_⟩
  · have hc : (S.biUnion fun r => (T r).edgeFinset).card ≤
        Fintype.card V * (2 * Fintype.card V / (d * (K + 1)) + 1) := calc
      _ ≤ ∑ r ∈ S, (T r).edgeFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ S, Fintype.card V := sum_le_sum (fun r _ => hTsize r)
      _ = S.card * Fintype.card V := by simp
      _ ≤ _ := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (Fintype.card V) hSsize
    exact (graphOfEdges_card_le E).trans ((card_union_le _ _).trans (Nat.add_le_add_left hc _))
  · intro i hi
    obtain ⟨r, hr, hri⟩ := hhit i hi
    obtain ⟨j, hj, hrj⟩ := mem_biUnion.mp hri
    have hroot : ∀ v, H.edist r v = G.edist r v := by
      intro v
      exact le_antisymm ((edist_anti (hTH r hr)).trans_eq (hTdist r v)) (edist_anti hHG)
    apply plus_two_from_tree G H r _ _ ((p i).getVert j) hroot
    · exact (h₀G (by simpa using hrj)).symm
    · exact shortest_split (p i) (hp i) j
        (Nat.le_of_lt (mem_range.mp (missingIndices_subset H₀ (p i) hj)))

end SlackSparsification
