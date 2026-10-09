import DegreeFaultSpanners.FaultSpanner
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding

/-!
# Padding degree-fault forcing graphs by isolated vertices

Mapping a graph along a vertex embedding adds only isolated vertices. This
preserves the exact number of undirected edges, admissible fault degrees,
and the assertion that every degree-fault spanner must retain every edge.
The final theorem realizes the result on `Fin N` for every sufficiently
large target vertex count, without changing the fault budget or stretch.
-/

namespace DegreeFaultSpanners

open SimpleGraph

variable {V W : Type*}

/-- Relabeling vertices injectively preserves the exact undirected edge count. -/
theorem embedding_map_edge_count (i : V ↪ W) (G : SimpleGraph V) :
    Nat.card (G.map i).edgeSet = Nat.card G.edgeSet := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ i.sym2Map.injective

/-- Vertices outside the embedded graph have no neighbors. -/
theorem embedding_map_neighborSet_eq_empty (i : V ↪ W) (G : SimpleGraph V)
    {w : W} (hw : w ∉ Set.range i) : (G.map i).neighborSet w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨u, v, _, hu, _⟩ := (SimpleGraph.map_adj i G w x).mp hx
  exact hw ⟨u, hu⟩

/-- Adding isolated vertices does not increase any fault degree. -/
theorem HasDegreeBound.embedding_map [Fintype V] [Fintype W]
    {F : SimpleGraph V} {f : ℕ} (hF : HasDegreeBound F f) (i : V ↪ W) :
    HasDegreeBound (F.map i) f := by
  intro w
  by_cases hw : w ∈ Set.range i
  · obtain ⟨v, rfl⟩ := hw
    rw [SimpleGraph.neighborSet_map, Set.ncard_image_of_injective _ i.injective]
    exact hF v
  · rw [embedding_map_neighborSet_eq_empty i F hw]
    simp

/-- The same admissible fault graph remains admissible after adding isolated vertices. -/
theorem AdmissibleFault.embedding_map [Fintype V] [Fintype W]
    {G F : SimpleGraph V} {f : ℕ} (hF : AdmissibleFault G f F) (i : V ↪ W) :
    AdmissibleFault (G.map i) f (F.map i) :=
  ⟨SimpleGraph.map_monotone i hF.1, hF.2.embedding_map i⟩

/-- A spanner of a graph with extra isolated vertices restricts to a spanner
of the original graph. The chosen inverse is used only on embedded vertices:
every edge of the spanner lies in the image of the original graph. -/
theorem IsDegreeFaultSpanner.comap_embedding [Fintype V] [Fintype W] [Nonempty V]
    {G : SimpleGraph V} {H : SimpleGraph W} {f t : ℕ} (i : V ↪ W)
    (h : IsDegreeFaultSpanner (G.map i) H f t) :
    IsDegreeFaultSpanner G (H.comap i) f t := by
  classical
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact SimpleGraph.map_adj_apply.mp (h.1 huv)
  · intro F hF
    apply walkStretch_iff_edges.mpr
    intro u v huv
    obtain ⟨q, hq⟩ := h.edge_replacement (hF.embedding_map i)
      (SimpleGraph.map_adj_apply.mpr huv.1)
      (fun hadj ↦ huv.2 (SimpleGraph.map_adj_apply.mp hadj))
    let r : W → V := Function.invFun i
    have hr : Function.LeftInverse r i := Function.leftInverse_invFun i.injective
    let φ : (H \ F.map i) →g ((H.comap i) \ F) :=
      { toFun := r
        map_rel' := by
          intro a b hab
          obtain ⟨x, y, _, rfl, rfl⟩ :=
            (SimpleGraph.map_adj i G a b).mp (h.1 hab.1)
          change H.Adj (i (r (i x))) (i (r (i y))) ∧ ¬ F.Adj (r (i x)) (r (i y))
          rw [hr x, hr y]
          exact ⟨hab.1, fun hxy ↦ hab.2 (SimpleGraph.map_adj_apply.mpr hxy)⟩ }
    refine ⟨(q.map φ).copy (hr u) (hr v), ?_⟩
    simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map] using hq

/-- The property that every degree-fault spanner is the whole input graph is
preserved by relabeling and adjoining arbitrarily many isolated vertices. -/
theorem embedding_map_forces_all_edges [Fintype V] [Fintype W] [Nonempty V]
    (i : V ↪ W) (G : SimpleGraph V) {f t : ℕ}
    (hforce : ∀ H, IsDegreeFaultSpanner G H f t → H = G) :
    ∀ H, IsDegreeFaultSpanner (G.map i) H f t → H = G.map i := by
  intro H hH
  apply le_antisymm hH.1
  have hbase : H.comap i = G := hforce _ (hH.comap_embedding i)
  calc
    G.map i = (H.comap i).map i := congrArg (SimpleGraph.map i) hbase.symm
    _ ≤ H := SimpleGraph.map_comap_le i H

/-- Pad a nonempty finite forcing graph to every larger number of vertices.
The graph on `Fin N` has exactly the original number of edges, and every
spanner with the original fault budget and stretch must still equal it. -/
theorem exists_padded_forcing_graph [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {N f t : ℕ} (hcard : Fintype.card V ≤ N)
    (hforce : ∀ H, IsDegreeFaultSpanner G H f t → H = G) :
    ∃ G' : SimpleGraph (Fin N),
      Nat.card G'.edgeSet = Nat.card G.edgeSet ∧
      ∀ H, IsDegreeFaultSpanner G' H f t → H = G' := by
  classical
  let i : V ↪ Fin N := (Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb hcard)
  exact ⟨G.map i, embedding_map_edge_count i G, embedding_map_forces_all_edges i G hforce⟩

end DegreeFaultSpanners
