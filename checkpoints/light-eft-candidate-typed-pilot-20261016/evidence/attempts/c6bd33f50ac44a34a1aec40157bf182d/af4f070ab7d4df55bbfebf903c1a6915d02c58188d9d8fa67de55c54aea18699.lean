import LightEFTSpanners.NativeForestQuotient

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V W E : Type*}
attribute [local instance] Classical.propDecidable

/-- An actual input vertex gives an actual image vertex of the crossing
quotient, even when its fiber has no crossing edges. -/
def quotientVertex (G : Graph V E) (f : V → W) (a : G.vertexSet) :
    (crossingQuotient G f).vertexSet := ⟨f a,Set.mem_image_of_mem f a.property⟩

/-- Actual walks project to the crossing quotient. Internal steps are removed
by reflexivity; crossing steps retain their original edge identity. -/
theorem reachable_crossingQuotient (G : Graph V E) (f : V → W)
    {a b : G.vertexSet} (hr : G.toSimpleGraph.Reachable a b) :
    (crossingQuotient G f).toSimpleGraph.Reachable
      (quotientVertex G f a) (quotientVertex G f b) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.refl _
  | @cons x y z hxy p ih =>
    have hs : (crossingQuotient G f).toSimpleGraph.Reachable
        (quotientVertex G f x) (quotientVertex G f y) := by
      by_cases hf : f x=f y
      · have hq : quotientVertex G f x=quotientVertex G f y := Subtype.ext hf
        rw [hq]
      · obtain ⟨_,e,he⟩ := hxy
        apply Adj.reachable
        refine ⟨?_,e,⟨⟨x.val,y.val,he,hf⟩,he.map f⟩⟩
        exact fun h => hf (congrArg Subtype.val h)
    exact hs.trans ih

/-- Contraction and removal of internal loops preserve actual connectedness;
nonempty image vertices are constructed from an actual input vertex. -/
theorem connected_crossingQuotient (G : Graph V E) (f : V → W)
    (hc : G.toSimpleGraph.Connected) : (crossingQuotient G f).toSimpleGraph.Connected := by
  let : Nonempty (crossingQuotient G f).vertexSet :=
    hc.nonempty.map (quotientVertex G f)
  refine ⟨?_⟩
  intro a b
  obtain ⟨x,hx,hxa⟩ := a.property
  obtain ⟨y,hy,hyb⟩ := b.property
  have hr := reachable_crossingQuotient G f (hc.preconnected ⟨x,hx⟩ ⟨y,hy⟩)
  have ha : quotientVertex G f ⟨x,hx⟩=a := Subtype.ext hxa
  have hb : quotientVertex G f ⟨y,hy⟩=b := Subtype.ext hyb
  simpa only [ha,hb] using hr

/-- A native tree, contracted only along genuinely connected fibers, has one
fewer crossing original edge than actual image vertices. The target ambient
vertex type is finite; phantom target vertices do not enter the cardinality. -/
theorem tree_crossingQuotient_card [Finite W] (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    (hb : ∀ e∈G.edgeSet,G.IsBridge e) (hconn : G.toSimpleGraph.Connected) :
    Nat.card (crossingQuotient G f).edgeSet+1=Nat.card (f '' G.vertexSet) := by
  exact native_tree_card (crossingQuotient G f)
    (crossingQuotient_all_bridges G f hc hb) (connected_crossingQuotient G f hconn)
end LightEFTSpanners.MultigraphCuts
