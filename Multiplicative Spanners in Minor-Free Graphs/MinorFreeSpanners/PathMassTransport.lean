import MinorFreeSpanners.ForestPathMass
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Exact path-mass transport along injective graph maps and induced walks.
The same distinct support vertices are counted, with their original weights. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem pathMass_map {I J : Type*} {H : SimpleGraph I} {K : SimpleGraph J}
    (f : H →g K) (hf : Function.Injective f) (d : J → ℝ) {x y : I} (p : H.Walk x y) :
    pathMass d (p.map f)=pathMass (fun i => d (f i)) p := by
  classical
  have hs : (List.map (⇑f) p.support).toFinset=p.support.toFinset.image f := by
    ext j
    simp
  simp only [pathMass,Walk.support_map,hs]
  exact Finset.sum_image (fun i _ j _ he => hf he)

 theorem pathMass_induce {I : Type*} {H : SimpleGraph I} (S : Set I)
    (d : I → ℝ) {x y : I} (p : H.Walk x y) (hs : ∀ i∈p.support,i∈S) :
    pathMass (fun i : S => d i.val) (p.induce S hs)=pathMass d p := by
  classical
  have h := pathMass_map (Embedding.induce (G:=H) S).toHom Subtype.val_injective d (p.induce S hs)
  change pathMass d ((p.induce S hs).map (Embedding.induce S).toHom)=
    pathMass (fun i : S => d i.val) (p.induce S hs) at h
  simpa [Embedding.induce,Embedding.toHom] using h.symm

end MinorFreeSpanners
