import MinorFreeSpanners.MinorRestriction
import MinorFreeSpanners.LowerBound

namespace MinorFreeSpanners
open SimpleGraph

/-- Injective graph homomorphisms preserve every actual cycle, so they
reflect lower bounds on girth. -/
theorem GirthAbove.of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {r : ℕ} (hH : GirthAbove H r) (f : G →g H) (hf : Function.Injective f) :
    GirthAbove G r := by
  intro a p hp
  have := hH (f a) (p.map f) (hp.map hf)
  simpa using this

/-- A cycle lies in one actual connected component. -/
theorem GirthAbove.of_components {V : Type*} (G : SimpleGraph V) (r : ℕ)
    (hC : ∀ C : G.ConnectedComponent, GirthAbove C.toSimpleGraph r) :
    GirthAbove G r := by
  classical
  intro a p hp
  let C := G.connectedComponentMk a
  have hS : ∀ x ∈ p.support, x ∈ C.supp := by
    intro x hx
    exact ConnectedComponent.eq.mpr (p.takeUntil x hx).reachable.symm
  let q := p.induce C.supp hS
  have hq : q.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce C.supp).toHom)
    simpa [q] using hp
  have hlen := hC C ⟨a,hS a p.start_mem_support⟩ q hq
  have he : q.length = p.length := by
    have hm : (q.map (Embedding.induce C.supp).toHom).length = q.length :=
      Walk.length_map _ _
    exact hm.symm.trans (congrArg (fun w : G.Walk a a => w.length) (p.map_induce hS))
  exact he ▸ hlen

end MinorFreeSpanners
