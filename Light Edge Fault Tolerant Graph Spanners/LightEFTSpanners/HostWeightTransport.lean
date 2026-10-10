import LightEFTSpanners.BlockerTransport
import LightSpanners.Weight

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- The edge-image equality is independent of both finite enumerations. -/
theorem mapped_edgeFinset_at (j : V ↪ W) (G : SimpleGraph V)
    (a : Fintype (G.map j).edgeSet) (b : Fintype G.edgeSet) :
    @SimpleGraph.edgeFinset W (G.map j) a =
      (@SimpleGraph.edgeFinset V G b).map j.sym2Map := by
  apply Finset.coe_injective
  simp only [coe_edgeFinset,coe_map]
  exact G.edgeSet_map j

omit [DecidableEq V] in
/-- The actual mapped graph counts each original unordered edge once. -/
theorem mapped_edgeFinset (j : V ↪ W) (G : SimpleGraph V) :
    (G.map j).edgeFinset = G.edgeFinset.map j.sym2Map := by
  apply Finset.coe_injective
  simp only [coe_edgeFinset,coe_map]
  exact G.edgeSet_map j

omit [DecidableEq V] [DecidableEq W] in
/-- Exact weight transport, with no factor for the embedding or enumeration. -/
theorem totalWeight_map_embedding (j : V ↪ W) (G : SimpleGraph V) (w : Sym2 W → ℝ) :
    totalWeight (G.map j) w = totalWeight G (fun e => w (j.sym2Map e)) := by
  unfold totalWeight
  have hh (a : Fintype (G.map j).edgeSet) (b : Fintype G.edgeSet) :
      (∑ e∈@SimpleGraph.edgeFinset W (G.map j) a,w e) =
        ∑ e∈@SimpleGraph.edgeFinset V G b,w (j.sym2Map e) := by
    rw [mapped_edgeFinset_at j G a b,Finset.sum_map]
  exact hh _ _

omit [DecidableEq V] in
/-- Pulling back the seed gives exactly the induced seed graph's edges. -/
theorem pullEdges_edgeFinset (j : V ↪ W) (G : SimpleGraph W) :
    pullEdges j G.edgeFinset = (G.comap j).edgeFinset := by
  ext e
  simp only [mem_pullEdges,mem_edgeFinset,mem_comap_edgeSet]

omit [DecidableEq V] in
/-- Local blocker avoidance is equivalent to avoiding the actual global host. -/
theorem disjoint_pullEdges_host (j : V ↪ W) (B : Finset (Sym2 W)) (T : SimpleGraph V) :
    Disjoint (pullEdges j B) T.edgeFinset ↔ Disjoint B (T.map j).edgeFinset := by
  rw [mapped_edgeFinset]
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro d hd hm
    obtain ⟨e,he,rfl⟩ := mem_map.mp hm
    exact Finset.disjoint_left.mp h ((mem_pullEdges j B e).mpr hd) he
  · intro h
    apply Finset.disjoint_left.mpr
    intro e he ht
    exact Finset.disjoint_left.mp h ((mem_pullEdges j B e).mp he)
      (mem_map.mpr ⟨e,ht,rfl⟩)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Candidate weights likewise transport by an exact finite sum equality. -/
theorem mapped_candidate_weight (j : V ↪ W) (U : Finset (Sym2 V)) (w : Sym2 W → ℝ) :
    (∑ e∈U.map j.sym2Map,w e) = ∑ e∈U,w (j.sym2Map e) := by
  rw [Finset.sum_map]
end LightEFTSpanners
