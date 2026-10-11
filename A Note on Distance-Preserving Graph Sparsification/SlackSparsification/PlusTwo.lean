import SlackSparsification.Initialization
import SlackSparsification.ParameterBounds
import SlackSparsification.PathEdges
import Mathlib.Tactic

/-! A deterministic graph-level implementation of the paper's +2 slack
construction. Integer parameters include the dense regime m = 0. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- An actual +2 subgraph for at least half of a finite indexed collection
of shortest paths. No hitting set or favorable random sample is assumed. -/
theorem exists_plus_two_slack_paths (G : SimpleGraph V)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d m : ℕ) (hd : 0 < d) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧
      P.card ≤ 2 * Q.card ∧
      H.edgeFinset.card ≤ 3 * Fintype.card V * d + P.card * m +
        Fintype.card V * (2 * Fintype.card V / (d * (m + 1)) + 1) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 2 := by
  classical
  obtain ⟨H₀, h₀G, h₀size, h₀degree⟩ := exists_initialization G (3 * d)
  let M := fun i => missingIndices H₀ (p i)
  let A := P.filter fun i => (M i).card ≤ m
  let B := P \ A
  let N := fun i => (M i).biUnion fun j => H₀.neighborFinset ((p i).getVert j)
  have hNsize (i : D) (hi : i ∈ B) : d * (m + 1) ≤ (N i).card := by
    have hlong : m < (M i).card := by
      have hi' := mem_sdiff.mp hi
      by_contra hn
      exact hi'.2 (mem_filter.mpr ⟨hi'.1, by omega⟩)
    have hc := path_neighborhood_count G H₀ h₀G (p i) (hp i) (M i)
      (missingIndices_subset H₀ (p i)) (3 * d) (by
        intro j hj
        have hj' := mem_filter.mp hj
        exact h₀degree _ _ ((p i).adj_getVert_succ (mem_range.mp hj'.1)) hj'.2)
    change 3 * d * (M i).card ≤ 3 * (N i).card at hc
    have hm := Nat.mul_le_mul_left d (show m + 1 ≤ (M i).card by omega)
    nlinarith
  obtain ⟨S, Q₁, _, hSsize, hQ₁B, hhalf, hhit⟩ := exists_half_hitting_set
    (univ : Finset V) univ_nonempty B N (d * (m + 1)) (by positivity)
    (by intro i _; exact subset_univ _) hNsize
  choose T hTG hTsize hTdist using fun r : V => exists_shortest_path_tree G r
  let F := fun i => (p i).edges.toFinset \ H₀.edgeFinset
  let E := H₀.edgeFinset ∪ A.biUnion F ∪ S.biUnion (fun r => (T r).edgeFinset)
  let H := graphOfEdges E
  have hE : E ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact edgeFinset_mono h₀G he
      · obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
        exact mem_edgeFinset.mpr ((p i).edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp hi).1))
    · obtain ⟨r, _, hr⟩ := mem_biUnion.mp he
      exact edgeFinset_mono (hTG r) hr
  have hHG : H ≤ G := graphOfEdges_le hE
  have h₀H : H₀ ≤ H := le_graphOfEdges (by intro e he; exact mem_union_left _ (mem_union_left _ he))
  have hTH (r : V) (hr : r ∈ S) : T r ≤ H := le_graphOfEdges (by
    intro e he
    exact mem_union_right _ (mem_biUnion.mpr ⟨r, hr, he⟩))
  have hFsize (i : D) (hi : i ∈ A) : (F i).card ≤ m :=
    (missing_edges_card_le H₀ (p i)).trans (mem_filter.mp hi).2
  have hsize : H.edgeFinset.card ≤ 3 * Fintype.card V * d + P.card * m +
      Fintype.card V * (2 * Fintype.card V / (d * (m + 1)) + 1) := by
    have ha : A.card ≤ P.card := card_le_card (filter_subset _ _)
    have hF : (A.biUnion F).card ≤ P.card * m := calc
      _ ≤ ∑ i ∈ A, (F i).card := card_biUnion_le
      _ ≤ ∑ _ ∈ A, m := sum_le_sum hFsize
      _ = A.card * m := by simp
      _ ≤ P.card * m := Nat.mul_le_mul_right _ ha
    have hT : (S.biUnion fun r => (T r).edgeFinset).card ≤
        Fintype.card V * (2 * Fintype.card V / (d * (m + 1)) + 1) := calc
      _ ≤ ∑ r ∈ S, (T r).edgeFinset.card := card_biUnion_le
      _ ≤ ∑ _ ∈ S, Fintype.card V := sum_le_sum (fun r _ => hTsize r)
      _ = S.card * Fintype.card V := by simp
      _ ≤ _ := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (Fintype.card V) hSsize
    have hc := (graphOfEdges_card_le E).trans (card_union_le _ _)
    have hc' := card_union_le H₀.edgeFinset (A.biUnion F)
    change H.edgeFinset.card ≤ _ at hc
    nlinarith
  let Q := A ∪ Q₁
  have hAP : A ⊆ P := filter_subset _ _
  have hdis : Disjoint A Q₁ := disjoint_left.mpr (by
    intro i hi hi₁
    exact (mem_sdiff.mp (hQ₁B hi₁)).2 hi)
  refine ⟨H, Q, hHG, union_subset hAP (hQ₁B.trans sdiff_subset), ?_, hsize, ?_⟩
  · have hb := card_sdiff_add_card_eq_card hAP
    have hq := card_union_of_disjoint hdis
    change P.card ≤ 2 * (A ∪ Q₁).card
    change B.card + A.card = P.card at hb
    omega
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · have hpath : (p i).edges.toFinset ⊆ H.edgeFinset := by
        intro e he
        by_cases he₀ : e ∈ H₀.edgeFinset
        · exact edgeFinset_mono h₀H he₀
        · have heF : e ∈ F i := mem_sdiff.mpr ⟨he, he₀⟩
          have heE : e ∈ E := mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i, hi, heF⟩))
          have hG : e ∈ G.edgeFinset := hE heE
          have hn : e ∉ Sym2.diagSet := G.edgeSet_subset_compl_diagSet (mem_edgeFinset.mp hG)
          apply mem_edgeFinset.mpr
          simpa [H, graphOfEdges] using (show e ∈ (↑E : Set (Sym2 V)) \ Sym2.diagSet from ⟨heE, hn⟩)
      rw [captured_path_distance hHG (p i) (hp i) hpath]
      exact le_self_add
    · obtain ⟨r, hr, hri⟩ := hhit i hi
      obtain ⟨j, hj, hrj⟩ := mem_biUnion.mp hri
      have hroot : ∀ v, H.edist r v = G.edist r v := by
        intro v
        apply le_antisymm _ (edist_anti hHG)
        exact (edist_anti (hTH r hr)).trans_eq (hTdist r v)
      apply plus_two_from_tree G H r _ _ ((p i).getVert j) hroot
      · exact (h₀G (by simpa using hrj)).symm
      · exact shortest_split (p i) (hp i) j
          (Nat.le_of_lt (mem_range.mp (missingIndices_subset H₀ (p i) hj)))

end SlackSparsification
