import MinorFreeSpanners.ConnectedCorePacking
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Actual residual components, transported back to the original vertex type.
This keeps the original support and adjacency in the initialization construction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

namespace ResidualComponents
variable {V : Type*} (G : SimpleGraph V) (R : Finset V)

noncomputable def block (c : (G.induce (R:Set V)).ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image Subtype.val

 theorem mem_block (c : (G.induce (R:Set V)).ConnectedComponent) (v : V) :
    v∈block G R c ↔ ∃ hv : v∈R,
      (⟨v,hv⟩ : {v // v∈(R:Set V)})∈c.supp := by
  classical
  simp only [block,Finset.mem_image,Set.mem_toFinset]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨hv,hc⟩
    exact ⟨⟨v,hv⟩,hc,rfl⟩

 theorem nonempty (c : (G.induce (R:Set V)).ConnectedComponent) : (block G R c).Nonempty := by
  obtain ⟨x,hx⟩ := c.nonempty_supp
  exact ⟨x.val,(mem_block G R c x.val).mpr ⟨x.property,hx⟩⟩

 theorem subset (c : (G.induce (R:Set V)).ConnectedComponent) : block G R c ⊆ R := by
  intro v hv
  exact ((mem_block G R c v).mp hv).choose

 theorem disjoint (c d : (G.induce (R:Set V)).ConnectedComponent) (hcd : c≠d) :
    Disjoint (block G R c) (block G R d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hc hd
  obtain ⟨hv,hc⟩ := (mem_block G R c v).mp hc
  obtain ⟨_,hd⟩ := (mem_block G R d v).mp hd
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hd)

 theorem connected (c : (G.induce (R:Set V)).ConnectedComponent) :
    ConnectedWithin G (block G R c) := by
  classical
  intro x hx y hy
  obtain ⟨hxR,hxc⟩ := (mem_block G R c x).mp hx
  obtain ⟨hyR,hyc⟩ := (mem_block G R c y).mp hy
  let f : c.toSimpleGraph →g G := {toFun := fun z => z.val.val,map_rel' := fun h => h}
  obtain ⟨p⟩ := c.connected_toSimpleGraph.preconnected ⟨⟨x,hxR⟩,hxc⟩ ⟨⟨y,hyR⟩,hyc⟩
  refine ⟨p.map f,?_⟩
  intro z hz
  rw [Walk.support_map,List.mem_map] at hz
  obtain ⟨u,_,rfl⟩ := hz
  exact (mem_block G R c _).mpr ⟨u.val.property,u.property⟩

 theorem covers {v : V} (hv : v∈R) :
    ∃ c : (G.induce (R:Set V)).ConnectedComponent, v∈block G R c := by
  refine ⟨(G.induce (R:Set V)).connectedComponentMk ⟨v,hv⟩,?_⟩
  exact (mem_block G R _ v).mpr ⟨hv,SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

 theorem closed_adj (c : (G.induce (R:Set V)).ConnectedComponent) {x y : V}
    (hx : x∈block G R c) (hy : y∈R) (hxy : G.Adj x y) : y∈block G R c := by
  obtain ⟨hxR,hxc⟩ := (mem_block G R c x).mp hx
  exact (mem_block G R c y).mpr ⟨hy,c.mem_supp_of_adj_mem_supp hxc
    (show (G.induce (R:Set V)).Adj ⟨x,hxR⟩ ⟨y,hy⟩ from hxy)⟩

end ResidualComponents
end MinorFreeSpanners
