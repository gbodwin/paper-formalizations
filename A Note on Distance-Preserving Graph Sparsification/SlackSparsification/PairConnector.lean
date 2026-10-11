import SlackSparsification.PathEdges
import SlackSparsification.GraphRouting
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! The actual shortest-candidate purchase in Theorem 12. Minimizing over
all eligible shortest paths avoids an extra canonical-consistency assumption.
This is a finite existential construction, not a claim of efficient enumeration. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

abbrev PathCandidate (G : SimpleGraph V) := Σ st : V × V, G.Path st.1 st.2

theorem graphOfEdges_mem {G : SimpleGraph V} {E : Finset (Sym2 V)} {e : Sym2 V}
    (hG : e ∈ G.edgeFinset) (hE : e ∈ E) : e ∈ (graphOfEdges E).edgeFinset := by
  apply mem_edgeFinset.mpr
  have hn := G.edgeSet_subset_compl_diagSet (mem_edgeFinset.mp hG)
  simpa [graphOfEdges] using (show e ∈ (↑E : Set (Sym2 V)) \ Sym2.diagSet from ⟨hE, hn⟩)

/-- Buy at most K edges for a root pair. Every eligible comparison path
then has an additive-4 route between its endpoints. -/
theorem exists_single_pair_connector (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (r q : V) (K : ℕ) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ F.card ≤ K ∧
      ∀ (x y : V) (p : G.Walk x y), p.length = G.dist x y →
        H₀.Adj r x → H₀.Adj y q → (p.edges.toFinset \ H₀.edgeFinset).card ≤ K →
        (graphOfEdges (H₀.edgeFinset ∪ F)).edist x y ≤ G.edist x y + 4 := by
  classical
  let C : Finset (PathCandidate G) := univ.filter fun c =>
    H₀.Adj r c.1.1 ∧ H₀.Adj c.1.2 q ∧ c.2.val.length = G.dist c.1.1 c.1.2 ∧
      (c.2.val.edges.toFinset \ H₀.edgeFinset).card ≤ K
  by_cases hC : C.Nonempty
  · obtain ⟨c, hc, hmin⟩ := exists_min_image C (fun c => c.2.val.length) hC
    have hc' := (mem_filter.mp hc).2
    let F := c.2.val.edges.toFinset \ H₀.edgeFinset
    let H := graphOfEdges (H₀.edgeFinset ∪ F)
    have hFG : F ⊆ G.edgeFinset := by
      intro e he
      exact mem_edgeFinset.mpr (c.2.val.edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp he).1))
    have hHG : H ≤ G := graphOfEdges_le (union_subset (edgeFinset_mono h₀G) hFG)
    have h₀H : H₀ ≤ H := le_graphOfEdges subset_union_left
    have hpath : c.2.val.edges.toFinset ⊆ H.edgeFinset := by
      intro e he
      apply graphOfEdges_mem (mem_edgeFinset.mpr (c.2.val.edges_subset_edgeSet (List.mem_toFinset.mp he)))
      by_cases he₀ : e ∈ H₀.edgeFinset
      · exact mem_union_left _ he₀
      · exact mem_union_right _ (mem_sdiff.mpr ⟨he, he₀⟩)
    refine ⟨F, hFG, hc'.2.2.2, ?_⟩
    intro x y p hp hrx hyq hmissing
    let a : PathCandidate G := ⟨(x,y), ⟨p, p.isPath_of_length_eq_dist hp⟩⟩
    have ha : a ∈ C := mem_filter.mpr ⟨mem_univ _, hrx, hyq, hp, hmissing⟩
    have hlength := hmin a ha
    have hdist : G.edist c.1.1 c.1.2 ≤ G.edist x y := by
      rw [← c.2.val.reachable.coe_dist_eq_edist, ← p.reachable.coe_dist_eq_edist]
      exact_mod_cast (show G.dist c.1.1 c.1.2 ≤ G.dist x y by simpa [hc'.2.2.1, hp, a] using hlength)
    exact plus_four_selected_path G H x y r q c.1.1 c.1.2
      (h₀H hrx.symm) (h₀H hc'.1) (h₀H hc'.2.1) (h₀H hyq.symm)
      (captured_path_distance hHG c.2.val hc'.2.2.1 hpath) hdist
  · refine ⟨∅, empty_subset _, by simp, ?_⟩
    intro x y p hp hrx hyq hmissing
    exact (hC ⟨⟨(x,y), ⟨p, p.isPath_of_length_eq_dist hp⟩⟩,
      mem_filter.mpr ⟨mem_univ _, hrx, hyq, hp, hmissing⟩⟩).elim

/-- The complete sampled-root-pair connector from Theorem 12, with a
literal finite union and its |R|²K purchase budget. -/
theorem exists_pair_connector (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (R : Finset V) (K : ℕ) :
    ∃ H : SimpleGraph V, H₀ ≤ H ∧ H ≤ G ∧
      H.edgeFinset.card ≤ H₀.edgeFinset.card + R.card ^ 2 * K ∧
      ∀ r ∈ R, ∀ q ∈ R, ∀ (x y : V) (p : G.Walk x y),
        p.length = G.dist x y → H₀.Adj r x → H₀.Adj y q →
        (p.edges.toFinset \ H₀.edgeFinset).card ≤ K → H.edist x y ≤ G.edist x y + 4 := by
  classical
  choose F hFG hFsize hFsat using fun rq : V × V => exists_single_pair_connector G H₀ h₀G rq.1 rq.2 K
  let E := H₀.edgeFinset ∪ (R ×ˢ R).biUnion F
  let H := graphOfEdges E
  have h₀H : H₀ ≤ H := le_graphOfEdges subset_union_left
  have hEG : E ⊆ G.edgeFinset := by
    apply union_subset (edgeFinset_mono h₀G)
    intro e he
    obtain ⟨rq, _, h⟩ := mem_biUnion.mp he
    exact hFG rq h
  refine ⟨H, h₀H, graphOfEdges_le hEG, ?_, ?_⟩
  · calc
      _ ≤ E.card := graphOfEdges_card_le E
      _ ≤ H₀.edgeFinset.card + ((R ×ˢ R).biUnion F).card := card_union_le _ _
      _ ≤ H₀.edgeFinset.card + ∑ rq ∈ R ×ˢ R, (F rq).card := Nat.add_le_add_left card_biUnion_le _
      _ ≤ H₀.edgeFinset.card + ∑ _ ∈ R ×ˢ R, K := Nat.add_le_add_left (sum_le_sum (fun rq _ => hFsize rq)) _
      _ = _ := by simp [pow_two]
  · intro r hr q hq x y p hp hrx hyq hmissing
    have hsub : H₀.edgeFinset ∪ F (r,q) ⊆ E := by
      apply union_subset subset_union_left
      intro e he
      exact mem_union_right _ (mem_biUnion.mpr ⟨(r,q), mem_product.mpr ⟨hr,hq⟩, he⟩)
    exact (edist_anti (graphOfEdges_mono hsub)).trans (hFsat (r,q) x y p hp hrx hyq hmissing)

end SlackSparsification
