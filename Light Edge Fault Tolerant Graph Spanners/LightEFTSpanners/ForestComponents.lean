import LightEFTSpanners.HostWeightTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*}

/-- The actual inclusion of one connected component's vertex domain. -/
def componentEmbedding (F : SimpleGraph V) (c : F.ConnectedComponent) : c ↪ V :=
  Function.Embedding.subtype (fun v => v ∈ c.supp)

/-- A forest component maps to an actual subgraph of the original forest. -/
theorem component_tree_le (F : SimpleGraph V) (c : F.ConnectedComponent) :
    c.toSimpleGraph.map (componentEmbedding F c) ≤ F := by
  exact map_le_iff_le_comap.mpr le_rfl

/-- Native connected components supply genuine trees, not spanning surrogates. -/
theorem component_isTree {F : SimpleGraph V} (hF : F.IsAcyclic)
    (c : F.ConnectedComponent) : c.toSimpleGraph.IsTree :=
  hF.isTree_connectedComponent c

theorem component_mapped_adj (F : SimpleGraph V) (c : F.ConnectedComponent) (a b : V) :
    (c.toSimpleGraph.map (componentEmbedding F c)).Adj a b ↔ a∈c.supp ∧ F.Adj a b := by
  exact c.adj_spanningCoe_toSimpleGraph

/-- An actual edge belongs to at most one connected-component tree. -/
theorem component_edge_unique (F : SimpleGraph V) {c d : F.ConnectedComponent}
    {e : Sym2 V}
    (hc : e∈(c.toSimpleGraph.map (componentEmbedding F c)).edgeSet)
    (hd : e∈(d.toSimpleGraph.map (componentEmbedding F d)).edgeSet) : c=d := by
  obtain ⟨a,b⟩ := e
  have ha := (component_mapped_adj F c a b).mp hc
  have hb := (component_mapped_adj F d a b).mp hd
  exact ((ConnectedComponent.mem_supp_iff c a).mp ha.1).symm.trans
    ((ConnectedComponent.mem_supp_iff d a).mp hb.1)

/-- An unordered endpoint pair has a local preimage exactly when both actual
endpoints lie in the component, including diagonal pairs. -/
theorem component_pair_preimage (F : SimpleGraph V) (c : F.ConnectedComponent)
    (a b : V) :
    (∃ e, (componentEmbedding F c).sym2Map e=s(a,b)) ↔ a∈c.supp ∧ b∈c.supp := by
  constructor
  · rintro ⟨⟨⟨x,hx⟩,⟨y,hy⟩⟩,he⟩
    change s(x,y)=s(a,b) at he
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hx,hy⟩
    · exact ⟨hy,hx⟩
  · rintro ⟨ha,hb⟩
    exact ⟨s(⟨a,ha⟩,⟨b,hb⟩),rfl⟩

/-- Reachability supplies the actual canonical component containing both ends. -/
theorem reachable_component_pair {F : SimpleGraph V} {a b : V} (h : F.Reachable a b) :
    ∃ e, (componentEmbedding F (F.connectedComponentMk a)).sym2Map e=s(a,b) := by
  apply (component_pair_preimage F _ a b).mpr
  exact ⟨rfl,ConnectedComponent.sound h.symm⟩
end LightEFTSpanners
