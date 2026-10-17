import LightEFTSpanners.ConnectivityCuts
import Mathlib.Combinatorics.Graph.Maps
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Connected.EdgeCut

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph Finset
variable {V W E : Type*}
attribute [local instance] Classical.propDecidable

/-- Native multigraph vertex maps preserve every edge identity; target cuts
are precisely the cuts of their vertex preimages, even with parallel edges
and loops created by the map. -/
theorem edgeCut_map (G : Graph V E) (f : V → W) (S : Set W) :
    (G.map f).edgeCut S=G.edgeCut (f ⁻¹' S) := by
  ext e
  constructor
  · rintro ⟨x,y,⟨u,v,h,rfl,rfl⟩,hx,hy⟩
    exact ⟨u,v,h,hx,hy⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨f u,f v,h.map f,hu,hv⟩

/-- The finite simple-graph cut model agrees exactly with mathlib's genuine
edge-identified multigraph cut, rather than collapsing multiplicities. -/
theorem ofSimpleGraph_cut [Fintype V] (G : SimpleGraph V) (S : Set V) :
    (Graph.ofSimpleGraph G).edgeCut S=(ConnectivityCuts.edges G S:Set (Sym2 V)) := by
  classical
  ext e
  constructor
  · rintro ⟨u,v,⟨heq,he⟩,hu,hv⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_edgeFinset.mpr he,
      ⟨⟨u,by rw [heq]; exact Sym2.mem_mk_left u v,hu⟩,⟨v,by rw [heq]; exact Sym2.mem_mk_right u v,hv⟩⟩⟩
  · intro he
    obtain ⟨he,⟨u,hu,huS⟩,v,hv,hvS⟩ := Finset.mem_filter.mp he
    have huv : u≠v := by rintro rfl; exact hvS huS
    have heq : e=s(u,v) := (Sym2.mem_and_mem_iff huv).mp ⟨hu,hv⟩
    exact ⟨u,v,⟨heq,mem_edgeFinset.mp he⟩,huS,hvS⟩

/-- Keep K's vertices distinct and contract its complement to one vertex.
Graph.map, unlike a simple-graph quotient, retains parallel edge identities. -/
noncomputable def collapseOutside (K : Set V) (v : V) : Option K :=
  if h : v∈K then some ⟨v,h⟩ else none

/-- Every subset of the retained core is the exact preimage of its actual
image in the contracted vertex type. -/
theorem collapse_preimage (K A : Set V) (hA : A⊆K) :
    collapseOutside K ⁻¹' (Option.some '' {v : K | v.val∈A})=A := by
  classical
  ext v
  by_cases hv : v∈K
  · simp [collapseOutside,hv]
  · have hvA : v∉A := fun h => hv (hA h)
    simp [collapseOutside,hv,hvA]

/-- Actual complement contraction preserves each inner core cut as a set of
original edge identities, including all parallel edges. This is the transport
step needed before applying the minimal deficient-core argument. -/
theorem collapse_inner_cut (G : Graph V E) (K A : Set V) (hA : A⊆K) :
    (G.map (collapseOutside K)).edgeCut (Option.some '' {v : K | v.val∈A})=
      G.edgeCut A := by
  rw [edgeCut_map,collapse_preimage K A hA]
end LightEFTSpanners.MultigraphCuts
