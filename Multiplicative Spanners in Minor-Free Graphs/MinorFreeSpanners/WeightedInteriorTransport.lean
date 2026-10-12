import MinorFreeSpanners.PathMassTransport
import MinorFreeSpanners.FourArmCore

/-! Weighted interiors are preserved by injective maps of actual simple paths.
The prefix and suffix are the same forest paths and retain exact support mass. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem weightedInterior_map_iff {I J : Type*} {H : SimpleGraph I} {K : SimpleGraph J}
    (hK : K.IsAcyclic) (f : H →g K) (hf : Function.Injective f)
    (d : J → ℝ) (L : ℝ) {a b x : I} (p : H.Walk a b) (hp : p.IsPath) :
    WeightedInterior d L (p.map f) (f x) ↔ WeightedInterior (fun i => d (f i)) L p x := by
  classical
  have hmem : f x∈(p.map f).support ↔ x∈p.support := by
    simp only [Walk.support_map,List.mem_map]
    constructor
    · rintro ⟨y,hy,he⟩
      exact hf he ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  have hp' := hp.map hf
  have heq (hx : x∈p.support) :
      (p.map f).takeUntil (f x) (hmem.mpr hx)=(p.takeUntil x hx).map f ∧
      (p.map f).dropUntil (f x) (hmem.mpr hx)=(p.dropUntil x hx).map f := by
    constructor
    · exact congrArg Subtype.val ((hK.subsingleton_path (f a) (f x)).elim
        ⟨_,hp'.takeUntil (hmem.mpr hx)⟩ ⟨_,(hp.takeUntil hx).map hf⟩)
    · exact congrArg Subtype.val ((hK.subsingleton_path (f x) (f b)).elim
        ⟨_,hp'.dropUntil (hmem.mpr hx)⟩ ⟨_,(hp.dropUntil hx).map hf⟩)
  constructor
  · rintro ⟨hx,hl,hr⟩
    have hx' := hmem.mp hx
    refine ⟨hx',?_,?_⟩
    · simpa only [(heq hx').1,pathMass_map f hf] using hl
    · simpa only [(heq hx').2,pathMass_map f hf] using hr
  · rintro ⟨hx,hl,hr⟩
    refine ⟨hmem.mpr hx,?_,?_⟩
    · simpa only [(heq hx).1,pathMass_map f hf] using hl
    · simpa only [(heq hx).2,pathMass_map f hf] using hr

end MinorFreeSpanners
