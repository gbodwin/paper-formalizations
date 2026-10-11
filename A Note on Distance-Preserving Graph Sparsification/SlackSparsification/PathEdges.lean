import SlackSparsification.GraphBasics
import SlackSparsification.Neighborhoods
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Tactic

namespace SlackSparsification
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def graphOfEdges (E : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (↑E)

theorem graphOfEdges_card_le (E : Finset (Sym2 V)) :
    (graphOfEdges E).edgeFinset.card ≤ E.card := by
  apply card_le_card
  intro e he
  have h : e ∈ (↑E : Set (Sym2 V)) \ Sym2.diagSet := by
    simpa [graphOfEdges] using (mem_edgeFinset.mp he)
  exact h.1

theorem graphOfEdges_le {E : Finset (Sym2 V)} {G : SimpleGraph V}
    (h : E ⊆ G.edgeFinset) : graphOfEdges E ≤ G := by
  intro u v huv
  exact mem_edgeFinset.mp (h huv.1)

theorem le_graphOfEdges {E : Finset (Sym2 V)} {G : SimpleGraph V}
    (h : G.edgeFinset ⊆ E) : G ≤ graphOfEdges E := by
  intro u v huv
  exact ⟨h (by simpa using huv), huv.ne⟩

noncomputable def missingIndices {G : SimpleGraph V} {s t : V}
    (H : SimpleGraph V) (p : G.Walk s t) : Finset ℕ :=
  (range p.length).filter fun i => ¬H.Adj (p.getVert i) (p.getVert (i + 1))

theorem missingIndices_subset {G : SimpleGraph V} {s t : V}
    (H : SimpleGraph V) (p : G.Walk s t) : missingIndices H p ⊆ range p.length :=
  filter_subset _ _

/-- Buying all missing path edges costs at most the number of missing
indexed steps. No path simplicity assumption is needed for this inequality. -/
theorem missing_edges_card_le {G : SimpleGraph V} {s t : V}
    (H : SimpleGraph V) (p : G.Walk s t) :
    (p.edges.toFinset \ H.edgeFinset).card ≤ (missingIndices H p).card := by
  classical
  let f := fun i => s(p.getVert i, p.getVert (i + 1))
  have hsub : p.edges.toFinset \ H.edgeFinset ⊆ (missingIndices H p).image f := by
    intro e he
    obtain ⟨hep, heH⟩ := mem_sdiff.mp he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨i, hi, heq⟩ := p.mk_mem_edges_iff_exists.mp (List.mem_toFinset.mp hep)
      have hmissing : ¬H.Adj (p.getVert i) (p.getVert (i + 1)) := by
        intro ha
        apply heH
        rw [← heq]
        simpa using ha
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hmissing⟩, heq⟩
  exact (card_le_card hsub).trans card_image_le

/-- Capturing the edges of an actual G-shortest walk preserves its distance. -/
theorem captured_path_distance {G H : SimpleGraph V} (hHG : H ≤ G)
    {s t : V} (p : G.Walk s t) (hp : p.length = G.dist s t)
    (hpath : p.edges.toFinset ⊆ H.edgeFinset) : H.edist s t = G.edist s t := by
  have he : ∀ e, e ∈ p.edges → e ∈ H.edgeSet :=
    fun e he => mem_edgeFinset.mp (hpath (List.mem_toFinset.mpr he))
  have h := (p.transfer H he).edist_le
  rw [Walk.length_transfer, hp, p.reachable.coe_dist_eq_edist] at h
  exact le_antisymm h (edist_anti hHG)

/-- The exact extended-distance split at any position of a shortest walk. -/
theorem shortest_split {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (i : ℕ) (hi : i ≤ p.length) :
    G.edist s (p.getVert i) + G.edist (p.getVert i) t = G.edist s t := by
  have ht := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  have hd := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_drop i)
  calc
    _ = ((p.take i).length : ℕ∞) + ((p.drop i).length : ℕ∞) := by
      rw [ht, hd, (p.take i).reachable.coe_dist_eq_edist,
        (p.drop i).reachable.coe_dist_eq_edist]
    _ = (p.length : ℕ∞) := by
      rw [← Nat.cast_add, Walk.take_length, Walk.drop_length, Nat.min_eq_left hi,
        Nat.add_sub_of_le hi]
    _ = G.edist s t := by rw [hp, p.reachable.coe_dist_eq_edist]

end SlackSparsification
