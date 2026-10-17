import LightEFTSpanners.NativeBlockRefinement
import LightEFTSpanners.NativeForestSemantics

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V W E : Type*}
attribute [local instance] Classical.propDecidable

/-- Inside a fiber, every actual adjacency survives deletion of an edge whose
endpoints have distinct images. Parallel identities are handled individually. -/
theorem fiberBlock_le_delete_crossing (G : Graph V E) (f : V → W)
    {e : E} {u v : V} (he : G.IsLink e u v) (hne : f u≠f v) :
    blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a)) ≤
      (G.deleteEdges {e}).toSimpleGraph := by
  intro a b hab
  obtain ⟨⟨hneab,d,hd⟩,hfab⟩ := hab
  refine ⟨hneab,d,hd,?_⟩
  intro hde
  have hde' : d=e := Set.mem_singleton_iff.mp hde
  subst d
  change f a=f b at hfab
  rcases he.eq_and_eq_or_eq_and_eq hd with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact hne (hu ▸ hv ▸ hfab)
  · exact hne (hu ▸ hv ▸ hfab.symm)

/-- A bridge cut is constant on every genuinely connected fiber, provided its
bridge crosses fibers. The paths are actual within-fiber paths in the input. -/
theorem bridge_cut_fiber_saturated (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    {e : E} {u v : V} (he : G.IsLink e u v) (hne : f u≠f v)
    {S : Set V} (hcut : G.edgeCut S={e}) :
    ∀ a b : G.vertexSet,f a=f b → (a.val∈S ↔ b.val∈S) := by
  intro a b hab
  have hr := (hc a b hab).mono (fiberBlock_le_delete_crossing G f he hne)
  have hr' : (G.deleteEdges (G.edgeCut S)).toSimpleGraph.Reachable a b :=
    (congrArg (fun F : Set E => (G.deleteEdges F).toSimpleGraph.Reachable a b) hcut).mpr hr
  exact after_cut_reachable_sides G S hr'

/-- Pushing an actual-vertex-saturated cut through a vertex map preserves its
exact original edge identities. No surjectivity or phantom-vertex convention
is needed. -/
theorem edgeCut_map_image_of_saturated (G : Graph V E) (f : V → W) (S : Set V)
    (hs : ∀ a b : G.vertexSet,f a=f b → (a.val∈S ↔ b.val∈S)) :
    (G.map f).edgeCut (f '' (S∩G.vertexSet))=G.edgeCut S := by
  rw [edgeCut_map]
  have hmem : ∀ x∈G.vertexSet,x∈f ⁻¹' (f '' (S∩G.vertexSet)) ↔ x∈S := by
    intro x hx
    constructor
    · rintro ⟨y,⟨hyS,hyG⟩,hyx⟩
      exact (hs ⟨y,hyG⟩ ⟨x,hx⟩ hyx).mp hyS
    · intro hxS
      exact ⟨x,⟨hxS,hx⟩,rfl⟩
  ext e
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    exact ⟨x,y,hxy,(hmem x hxy.left_mem).mp hx,
      fun hyS => hy ((hmem y hxy.right_mem).mpr hyS)⟩
  · rintro ⟨x,y,hxy,hx,hy⟩
    exact ⟨x,y,hxy,(hmem x hxy.left_mem).mpr hx,
      fun hyS => hy ((hmem y hxy.right_mem).mp hyS)⟩

/-- Contracting genuinely connected fibers preserves every crossing bridge. -/
theorem crossing_bridge_map (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    {e : E} {u v : V} (he : G.IsLink e u v) (hne : f u≠f v)
    (hb : G.IsBridge e) : (G.map f).IsBridge e := by
  obtain ⟨S,hS⟩ := hb
  refine ⟨f '' (S∩G.vertexSet),?_⟩
  rw [edgeCut_map_image_of_saturated G f S
    (bridge_cut_fiber_saturated G f hc he hne hS),hS]

/-- The true edge-identified quotient discards internal edges after mapping;
all crossing identities and every actual image vertex are retained. -/
noncomputable def crossingQuotient (G : Graph V E) (f : V → W) : Graph W E :=
  (G.map f).restrict {e | ∃ u v,G.IsLink e u v ∧ f u≠f v}

/-- A native forest contracted along connected fibers remains a native forest.
This includes exclusion of new parallel cycles; it is not merely acyclicity
of a simple graph obtained by forgetting edge multiplicity. -/
theorem crossingQuotient_all_bridges (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    (hb : ∀ e∈G.edgeSet,G.IsBridge e) :
    ∀ e∈(crossingQuotient G f).edgeSet,(crossingQuotient G f).IsBridge e := by
  intro e he
  have hmem := he
  obtain ⟨_,u,v,huv,hne⟩ := hmem
  exact (crossing_bridge_map G f hc huv hne (hb e huv.edge_mem)).anti_of_mem
    (Graph.restrict_le ..) he
end LightEFTSpanners.MultigraphCuts
