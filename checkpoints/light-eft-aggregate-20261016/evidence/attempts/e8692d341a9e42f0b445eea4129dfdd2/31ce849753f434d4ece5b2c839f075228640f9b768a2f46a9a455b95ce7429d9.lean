import LightSpanners.TreeReduction
import LightEFTSpanners.Basic

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A bottleneck-optimal spanning tree cannot contain every maximum-weight
edge of a cycle. This proves the exchange fact used in Lemma 26, including ties. -/
theorem cycle_maximum_outside_tree {G K : SimpleGraph V} {w : Sym2 V → ℝ}
    (hK : K.IsTree) (hKG : K ≤ G) (hbot : HasBottleneckPaths G K w)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ e ∈ p.edges, e ∉ K.edgeSet ∧ ∀ d ∈ p.edges, w d ≤ w e := by
  classical
  have hpne : p.edges.toFinset.Nonempty := by
    have hlen : 0 < p.edges.length := by
      rw [Walk.length_edges]
      exact Nat.zero_lt_of_ne_zero (fun h => hp.not_nil (Walk.length_eq_zero_iff.mp h))
    obtain ⟨e,he⟩ := List.length_pos_iff_exists_mem.mp hlen
    exact ⟨e,List.mem_toFinset.mpr he⟩
  obtain ⟨e,he,hmax⟩ := exists_max_image p.edges.toFinset w hpne
  have hep : e ∈ p.edges := List.mem_toFinset.mp he
  have hmax' : ∀ d ∈ p.edges, w d ≤ w e := fun d hd => hmax d (List.mem_toFinset.mpr hd)
  by_contra hn
  have heK : e ∈ K.edgeSet := by
    by_contra heN
    exact hn ⟨e,hep,heN,hmax'⟩
  obtain ⟨u,v,heq,q,hqw,hqe⟩ := cycle_complement p hp w hep
  have hbridge : K.IsBridge e := isAcyclic_iff_forall_isBridge.mp hK.isAcyclic heK
  have hcut : ¬ (K.deleteEdges {e}).Reachable v u := by
    intro hc
    have hc' : (K.deleteEdges {s(u,v)}).Reachable u v := by simpa [heq] using hc.symm
    exact (heq ▸ hbridge) hc'
  obtain ⟨x,y,hxy,hxyq,hxycut⟩ := exists_edge_not_reachable q hcut
  have hxyp : s(x,y) ∈ p.edges := (hqe _ hxyq).1
  have hxyne : s(x,y) ≠ e := (hqe _ hxyq).2
  have hxyK : s(x,y) ∉ K.edgeSet := by
    intro hh
    exact hxycut (Adj.reachable (deleteEdges_adj.mpr ⟨(mem_edgeSet K).mp hh,hxyne⟩))
  have hxylt : w s(x,y) < w e := by
    have hle := hmax' s(x,y) hxyp
    by_contra hnl
    have heqW : w s(x,y) = w e := le_antisymm hle (le_of_not_gt hnl)
    exact hn ⟨s(x,y),hxyp,hxyK,fun d hd => by simpa [heqW] using hmax' d hd⟩
  obtain ⟨r,hr⟩ := hbot x y hxy
  have her : e ∈ r.edges := by
    by_contra her
    apply hxycut
    exact ⟨r.transfer (K.deleteEdges {e}) (by
      intro d hd
      rw [edgeSet_deleteEdges]
      exact ⟨r.edges_subset_edgeSet hd,by
        intro h
        have heq : d = e := Set.mem_singleton_iff.mp h
        exact her (heq ▸ hd)⟩)⟩
  exact (not_le_of_gt hxylt) (hr e her)

end LightEFTSpanners
