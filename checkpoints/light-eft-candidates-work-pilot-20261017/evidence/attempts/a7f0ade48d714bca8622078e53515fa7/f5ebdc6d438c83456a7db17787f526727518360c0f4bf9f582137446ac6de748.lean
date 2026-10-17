import LightEFTSpanners.NativeSplitForestExpansion
import LightEFTSpanners.MultigraphCutTransport

namespace LightEFTSpanners.EvenSplitting
open SimpleGraph
variable {V W E : Type*}

/-- Enlarging selected original edge identities preserves actual connections. -/
theorem restrict_reachable_mono (G : Graph V E) {A B : Set E} (hAB : A⊆B)
    {x y : G.vertexSet} (h : (G.restrict A).toSimpleGraph.Reachable x y) :
    (G.restrict B).toSimpleGraph.Reachable x y :=
  h.mono (by rintro a b ⟨hne,e,he,hlink⟩; exact ⟨hne,e,hAB he,hlink⟩)

/-- The actual image of an original vertex in a native vertex map. -/
def mapVertex (G : Graph V E) (f : V → W) (x : G.vertexSet) : (G.map f).vertexSet :=
  ⟨f x.val,⟨x.val,x.property,rfl⟩⟩

/-- Lift a restricted quotient walk by the supplied actual connections within
its vertex fibers. Quotient links use their own original identities; joining
fiber paths is a literal original-graph walk construction. -/
theorem reachable_map_expand (G : Graph V E) (f : V → W) (A T : Set E)
    (hT : ∀ x y : G.vertexSet,f x.val=f y.val →
      (G.restrict T).toSimpleGraph.Reachable x y)
    {x y : G.vertexSet}
    (h : ((G.map f).restrict A).toSimpleGraph.Reachable
      (mapVertex G f x) (mapVertex G f y)) :
    (G.restrict (A∪T)).toSimpleGraph.Reachable x y := by
  have fiber (a b : G.vertexSet) (hab : f a.val=f b.val) :
      (G.restrict (A∪T)).toSimpleGraph.Reachable a b :=
    restrict_reachable_mono G Set.subset_union_right (hT a b hab)
  have liftWalk : ∀ {u v : (G.map f).vertexSet},
      ((G.map f).restrict A).toSimpleGraph.Walk u v →
      ∀ a b : G.vertexSet,mapVertex G f a=u → mapVertex G f b=v →
        (G.restrict (A∪T)).toSimpleGraph.Reachable a b := by
    intro u v p
    induction p with
    | nil =>
      intro a b ha hb
      exact fiber a b (congrArg Subtype.val (ha.trans hb.symm))
    | @cons u v w huv p ih =>
      intro a b ha hb
      obtain ⟨_,e,he,z,t,hzt,hzu,htv⟩ := huv
      let z' : G.vertexSet := ⟨z,hzt.left_mem⟩
      let t' : G.vertexSet := ⟨t,hzt.right_mem⟩
      have haz : f a.val=f z := (congrArg Subtype.val ha).trans hzu.symm
      have hzt' := restricted_link_reachable G (A∪T) (x:=z') (y:=t') (Or.inl he) hzt
      have htv' : mapVertex G f t'=v := Subtype.ext htv
      exact (fiber a z' haz).trans (hzt'.trans (ih t' b htv' hb))
  obtain ⟨p⟩ := h
  exact liftWalk p x y rfl rfl
end LightEFTSpanners.EvenSplitting
