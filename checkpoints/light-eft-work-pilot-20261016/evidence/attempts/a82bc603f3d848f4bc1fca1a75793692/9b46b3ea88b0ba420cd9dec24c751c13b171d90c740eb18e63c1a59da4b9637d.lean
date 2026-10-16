import LightEFTSpanners.NativeExchangeConnectivity
import LightEFTSpanners.NativeEdgeLevels

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- A replacement route inside the removed edge's last internal block preserves
all old within-stage connections: earlier stages contain the route, and later
stages contain no occurrence of the removed edge. This is the actual
connectivity implication needed by the lexicographic refinement argument. -/
theorem native_level_exchange_preserves_all_stages (G : Graph V E)
    (F F' : Set E) (e : E) (R : ℕ → Setoid G.vertexSet) (hR : Antitone R)
    (m : ℕ) (hkeep : F\{e}⊆F')
    (hexternal : ¬edgeInside G (R (m+1)) e)
    (replace : ∀ u v : G.vertexSet,G.IsLink e u.val v.val →
      (blockGraph (G.restrict F').toSimpleGraph (R m)).Reachable u v)
    (i : ℕ) {a b : G.vertexSet}
    (hr : (blockGraph (G.restrict F).toSimpleGraph (R i)).Reachable a b) :
    (blockGraph (G.restrict F').toSimpleGraph (R i)).Reachable a b := by
  by_cases hi : i≤m
  · apply native_exchange_preserves_blocks G F F' e (R i) hkeep ?_ hr
    intro u v he _
    apply (replace u v he).mono
    intro x y hxy
    exact ⟨hxy.1,hR hi hxy.2⟩
  · apply native_exchange_preserves_blocks_of_external G F F' e (R i) hkeep ?_ hr
    intro u v he hRi
    apply hexternal
    exact ⟨u,v,he,hR (by omega) hRi⟩
end LightEFTSpanners.MultigraphCuts
