import LightEFTSpanners.NativeQuotientCardinality

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V W E : Type*}
attribute [local instance] Classical.propDecidable

/-- If every fiber is genuinely connected in the input, any actual quotient
walk lifts to a connection between its chosen original endpoints. The proof
uses actual edge witnesses and within-fiber paths, not a connectivity oracle. -/
theorem reachable_of_crossingQuotient (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    {a b : G.vertexSet}
    (hr : (crossingQuotient G f).toSimpleGraph.Reachable
      (quotientVertex G f a) (quotientVertex G f b)) : G.toSimpleGraph.Reachable a b := by
  have hf : ∀ x y : G.vertexSet,f x=f y → G.toSimpleGraph.Reachable x y :=
    fun x y h => (hc x y h).mono (blockGraph_le _ _)
  have liftWalk : ∀ {u v : (crossingQuotient G f).vertexSet},
      (crossingQuotient G f).toSimpleGraph.Walk u v →
      ∀ x y : G.vertexSet,quotientVertex G f x=u → quotientVertex G f y=v →
      G.toSimpleGraph.Reachable x y := by
    intro u v p
    induction p with
    | nil =>
      intro x y hx hy
      exact hf x y (congrArg Subtype.val (hx.trans hy.symm))
    | @cons u v w huv p ih =>
      intro a b ha hb
      obtain ⟨hne,e,_,x,y,hxy,hxu,hyv⟩ := huv
      let x' : G.vertexSet := ⟨x,hxy.left_mem⟩
      let y' : G.vertexSet := ⟨y,hxy.right_mem⟩
      have hay : f a=f x := (congrArg Subtype.val ha).trans hxu.symm
      have hax : G.toSimpleGraph.Reachable a x' := hf a x' hay
      have hxy' : G.toSimpleGraph.Reachable x' y' := by
        by_cases heq : x'=y'
        · rw [heq]
        · exact (show G.toSimpleGraph.Adj x' y' from ⟨heq,e,hxy⟩).reachable
      have hyv' : quotientVertex G f y'=v := Subtype.ext hyv
      exact hax.trans (hxy'.trans (ih y' b hyv' hb))
  obtain ⟨p⟩ := hr
  exact liftWalk p a b rfl rfl

/-- In particular a disconnected pair stays disconnected after contraction
of connected fibers, with internal loops removed and all crossing IDs kept. -/
theorem not_reachable_crossingQuotient (G : Graph V E) (f : V → W)
    (hc : ∀ a b : G.vertexSet,f a=f b →
      (blockGraph G.toSimpleGraph (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    {a b : G.vertexSet} (hn : ¬G.toSimpleGraph.Reachable a b) :
    ¬(crossingQuotient G f).toSimpleGraph.Reachable
      (quotientVertex G f a) (quotientVertex G f b) :=
  fun h => hn (reachable_of_crossingQuotient G f hc h)
end LightEFTSpanners.MultigraphCuts
