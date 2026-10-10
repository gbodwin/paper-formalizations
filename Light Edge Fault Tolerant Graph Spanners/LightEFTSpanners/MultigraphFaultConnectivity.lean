import LightEFTSpanners.MultigraphCutTransport

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Genuine multigraph edge-fault connectivity: delete the specified original
edge identities first, then use native walk reachability on the surviving
adjacency graph. Parallel edges are never identified before deletion. -/
def FaultConnected (G : Graph V E) (k : ℕ) (a b : G.vertexSet) : Prop :=
  ∀ F : Finset E,F.card<k →
    (G.deleteEdges (F:Set E)).toSimpleGraph.Reachable a b

omit [Fintype E] in
/-- Native surviving walks cannot cross a deleted actual multigraph cut. -/
theorem after_cut_reachable_sides (G : Graph V E) (S : Set V)
    {a b : G.vertexSet}
    (hr : (G.deleteEdges (G.edgeCut S)).toSimpleGraph.Reachable a b) :
    a.val∈S ↔ b.val∈S := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | @cons x y z hadj p ih =>
    obtain ⟨_,e,he,hn⟩ := hadj
    have hxy : x.val∈S ↔ y.val∈S := by
      constructor
      · intro hx
        by_contra hy
        exact hn ⟨x.val,y.val,he,hx,hy⟩
      · intro hy
        by_contra hx
        exact hn ⟨y.val,x.val,he.symm,hy,hx⟩
    exact hxy.trans ih

/-- Genuine finite fault resilience forces the actual cardinality of every
separating edge cut, including all parallel edge identities. -/
theorem faultConnected_le_cut (G : Graph V E) {a b : G.vertexSet} {k : ℕ}
    (h : FaultConnected G k a b) (S : Set V) (ha : a.val∈S) (hb : b.val∉S) :
    k≤(G.edgeCut S).toFinset.card := by
  classical
  by_contra! hlt
  have hr := h (G.edgeCut S).toFinset hlt
  have hr' : (G.deleteEdges (G.edgeCut S)).toSimpleGraph.Reachable a b := by
    have heq : ((G.edgeCut S).toFinset:Set E)=G.edgeCut S := Set.coe_toFinset _
    exact (congrArg (fun U : Set E => (G.deleteEdges U).toSimpleGraph.Reachable a b) heq).mp hr
  exact hb ((after_cut_reachable_sides G S hr').mp ha)

/-- Conversely, if all genuine separating cuts are large, deleting fewer
edge identities leaves an actual native walk. The witness of failure is the
reachable component in the post-deletion graph, not a path-packing oracle. -/
theorem faultConnected_of_cut_lower (G : Graph V E) {a b : G.vertexSet} {k : ℕ}
    (hcut : ∀ S : Set V,a.val∈S → b.val∉S → k≤(G.edgeCut S).toFinset.card) :
    FaultConnected G k a b := by
  classical
  intro F hF
  by_contra hnot
  let H := (G.deleteEdges (F:Set E)).toSimpleGraph
  let S : Set V := {v | ∃ hv : v∈G.vertexSet,H.Reachable a ⟨v,hv⟩}
  have ha : a.val∈S := ⟨a.property,Reachable.refl a⟩
  have hb : b.val∉S := by
    rintro ⟨_,h⟩
    exact hnot h
  have hsub : (G.edgeCut S).toFinset⊆F := by
    intro e he
    obtain ⟨u,v,hlink,hu,hv⟩ := Set.mem_toFinset.mp he
    by_contra hn
    have hne : (⟨u,hlink.left_mem⟩:G.vertexSet)≠⟨v,hlink.right_mem⟩ := by
      intro heq
      have huv : u=v := congrArg Subtype.val heq
      exact hv (huv ▸ hu)
    have hadj : H.Adj ⟨u,hlink.left_mem⟩ ⟨v,hlink.right_mem⟩ :=
      ⟨hne,e,hlink,hn⟩
    obtain ⟨_,huR⟩ := hu
    exact hv ⟨hlink.right_mem,huR.trans hadj.reachable⟩
  have hlow := (hcut S ha hb).trans (card_le_card hsub)
  omega

theorem faultConnected_iff_cut_lower (G : Graph V E) {a b : G.vertexSet} {k : ℕ} :
    FaultConnected G k a b ↔
      ∀ S : Set V,a.val∈S → b.val∉S → k≤(G.edgeCut S).toFinset.card :=
  ⟨fun h S ha hb => faultConnected_le_cut G h S ha hb,
    faultConnected_of_cut_lower G⟩

/-- A mapped actual vertex has its original vertex as an explicit preimage. -/
def mapVertex (G : Graph V E) {W : Type*} (f : V → W) (a : G.vertexSet) :
    (G.map f).vertexSet := ⟨f a,Set.mem_image_of_mem f a.property⟩

/-- Native vertex contraction cannot reduce genuine edge-fault connectivity:
its cuts are exact preimage cuts with all original parallel identities kept. -/
theorem faultConnected_map (G : Graph V E) {W : Type*} (f : V → W)
    {a b : G.vertexSet} {k : ℕ} (h : FaultConnected G k a b) :
    FaultConnected (G.map f) k (mapVertex G f a) (mapVertex G f b) := by
  apply faultConnected_of_cut_lower
  intro S ha hb
  rw [edgeCut_map]
  exact faultConnected_le_cut G h (f ⁻¹' S) ha hb

/-- A concrete parallel-edge sanity check: deleting fewer than the number of
actual banana edges leaves a genuine connection (reflexive for equal endpoints).
For distinct endpoints, this would fail if
parallel identities had been collapsed before the fault operation. -/
theorem parallel_edges_faultConnected (u v : V) (edges : Finset E) {k : ℕ}
    (hk : k≤edges.card) :
    FaultConnected (Graph.banana u v (edges:Set E)) k
      ⟨u,by simp⟩ ⟨v,by simp⟩ := by
  classical
  apply faultConnected_of_cut_lower
  intro S hu hv
  have hc : (Graph.banana u v (edges:Set E)).edgeCut S=(edges:Set E) := by
    ext e
    constructor
    · exact fun h => Graph.edgeCut_subset_edgeSet h
    · intro he
      exact ⟨u,v,⟨he,Or.inl ⟨rfl,rfl⟩⟩,hu,hv⟩
  simpa [hc] using hk
end LightEFTSpanners.MultigraphCuts
