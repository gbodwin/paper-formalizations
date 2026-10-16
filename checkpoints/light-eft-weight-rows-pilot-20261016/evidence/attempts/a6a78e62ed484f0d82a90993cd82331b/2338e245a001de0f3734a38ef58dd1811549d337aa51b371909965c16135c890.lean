import LightEFTSpanners.NativeBlockRefinement

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- Replace each actual edge of a walk by an actual surviving walk. -/
theorem reachable_of_edge_routes (H K : SimpleGraph V)
    (routes : ∀ u v,H.Adj u v → K.Reachable u v) {a b : V} (h : H.Reachable a b) :
    K.Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w he p ih => exact (routes u v he).trans ih

/-- A one-original-edge replacement preserves all within-block reachability
when its removed edge has a genuine replacement route in that block. This is
the local walk-substitution obligation in an exchange argument, not an assumed
forest-packing conclusion. All other original edge identities are retained. -/
theorem native_exchange_preserves_blocks (G : Graph V E) (F F' : Set E) (e : E)
    (R : Setoid G.vertexSet) (hkeep : F\{e}⊆F')
    (replace : ∀ u v : G.vertexSet,G.IsLink e u.val v.val → R.r u v →
      (blockGraph (G.restrict F').toSimpleGraph R).Reachable u v)
    {a b : G.vertexSet}
    (h : (blockGraph (G.restrict F).toSimpleGraph R).Reachable a b) :
    (blockGraph (G.restrict F').toSimpleGraph R).Reachable a b := by
  apply reachable_of_edge_routes _ _ (a:=a) (b:=b) ?_ h
  intro u v huv
  obtain ⟨⟨hne,f,hf,hlink⟩,hR⟩ := huv
  by_cases hfe : f=e
  · subst f
    exact replace u v hlink hR
  · exact (show (blockGraph (G.restrict F').toSimpleGraph R).Adj u v from
      ⟨⟨hne,f,⟨hkeep ⟨hf,by simpa using hfe⟩,hlink⟩⟩,hR⟩).reachable

/-- If the removed edge is never internal to a block, no replacement route is
needed: every within-block walk survives the edge exchange literally. -/
theorem native_exchange_preserves_blocks_of_external (G : Graph V E) (F F' : Set E)
    (e : E) (R : Setoid G.vertexSet) (hkeep : F\{e}⊆F')
    (hexternal : ∀ u v : G.vertexSet,G.IsLink e u.val v.val → ¬R.r u v)
    {a b : G.vertexSet}
    (h : (blockGraph (G.restrict F).toSimpleGraph R).Reachable a b) :
    (blockGraph (G.restrict F').toSimpleGraph R).Reachable a b :=
  native_exchange_preserves_blocks G F F' e R hkeep
    (fun u v he hR => False.elim (hexternal u v he hR)) h
end LightEFTSpanners.MultigraphCuts
