import LightEFTSpanners.NativeForestSelection

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- In a genuinely simple native graph, unordered adjacency edges are in
bijection with original edge identities. This is false for a general multigraph. -/
noncomputable def simpleEdgeEquiv (G : Graph V E) [G.Simple] :
    G.toSimpleGraph.edgeSet ≃ G.edgeSet :=
  Equiv.ofBijective
    (fun s => ⟨edgeRepresentative G s.val s.property,edgeRepresentative_mem G s.val s.property⟩)
    ⟨by
      intro s t hst
      exact Subtype.ext (edgeRepresentative_injective G s.property t.property
        (congrArg Subtype.val hst)),by
      intro e
      obtain ⟨u,v,huv⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
      let a : G.vertexSet := ⟨u,huv.left_mem⟩
      let b : G.vertexSet := ⟨v,huv.right_mem⟩
      have hne : a≠b := fun h => huv.ne (congrArg Subtype.val h)
      have hs : s(a,b)∈G.toSimpleGraph.edgeSet :=
        G.toSimpleGraph.mem_edgeSet.mpr ⟨hne,e.val,huv⟩
      refine ⟨⟨s(a,b),hs⟩,Subtype.ext ?_⟩
      exact (edgeRepresentative_spec G s(a,b) hs a b rfl).eq huv⟩

theorem native_simple_card_edges (G : Graph V E) [G.Simple] :
    Nat.card G.edgeSet=Nat.card G.toSimpleGraph.edgeSet :=
  (Nat.card_congr (simpleEdgeEquiv G)).symm

/-- A finite connected native forest has exactly one fewer original edge
identity than actual vertices. Ambient phantom vertices do not enter this count. -/
theorem native_tree_card (G : Graph V E) [Finite G.vertexSet]
    (hbridge : ∀ e∈G.edgeSet,G.IsBridge e) (hconn : G.toSimpleGraph.Connected) :
    Nat.card G.edgeSet+1=Nat.card G.vertexSet := by
  let : G.Simple := simple_of_all_edges_bridge G hbridge
  rw [native_simple_card_edges G]
  exact (isTree_iff_connected_and_card.mp
    ⟨hconn,acyclic_of_all_edges_bridge G hbridge⟩).2

/-- Connected native graphs have an actual original-edge spanning tree. The
chosen edge subset contains no loops or parallel cycles and has exact finite
cardinality; neither a tree certificate nor its size is a premise. -/
theorem exists_native_spanning_tree (G : Graph V E) [Finite G.vertexSet]
    (hconn : G.toSimpleGraph.Connected) :
    ∃ F : Set E,F⊆G.edgeSet ∧
      (∀ e∈(G.restrict F).edgeSet,(G.restrict F).IsBridge e) ∧
      (G.restrict F).toSimpleGraph.Connected ∧
      Nat.card F+1=Nat.card G.vertexSet := by
  obtain ⟨F,hF,hforest,hr⟩ := exists_native_spanning_forest G
  let : Nonempty (G.restrict F).vertexSet := hconn.nonempty
  let : Finite (G.restrict F).vertexSet := inferInstanceAs (Finite G.vertexSet)
  have hc : (G.restrict F).toSimpleGraph.Connected := by
    refine ⟨?_⟩
    intro u v
    exact (congrFun (congrFun hr u) v).mpr (hconn.preconnected u v)
  have hcount := native_tree_card (G.restrict F) hforest hc
  change Nat.card (G.restrict F).edgeSet+1=Nat.card G.vertexSet at hcount
  have heq : (G.restrict F).edgeSet=F := Set.inter_eq_right.mpr hF
  have hcard : Nat.card (G.restrict F).edgeSet=Nat.card F :=
    congrArg (fun S : Set E => Nat.card S) heq
  exact ⟨F,hF,hforest,hc,by simpa only [hcard] using hcount⟩

/-- The genuine finite native connectivity edge lower bound counts all
original identities, not simplified endpoint pairs. -/
theorem native_connected_card_lower (G : Graph V E) [Finite G.vertexSet]
    [Finite G.edgeSet] (hconn : G.toSimpleGraph.Connected) :
    Nat.card G.vertexSet≤Nat.card G.edgeSet+1 := by
  obtain ⟨F,hF,_,_,hcard⟩ := exists_native_spanning_tree G hconn
  have hle : Nat.card F≤Nat.card G.edgeSet :=
    Nat.card_le_card_of_injective (fun e : F => (⟨e.val,hF e.property⟩:G.edgeSet))
      (fun _ _ h => Subtype.ext (congrArg (fun z : G.edgeSet => z.val) h))
  omega
end LightEFTSpanners.MultigraphCuts
