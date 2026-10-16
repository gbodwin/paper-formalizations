import LightEFTSpanners.NativeSteinerPackingReduction
import Mathlib.Logic.Equiv.Option

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- A literal vertex relabeling exposes a singleton connectivity island as the
proved distinguished center. The returned smaller graph's packing lifts back
through both the split trace and the injective relabeling. -/
theorem exists_native_isolated_island_reduction (G : Graph V E) (k : ℕ)
    (hall : G.vertexSet=Set.univ) (hdeg : ∀ x,Even (nativeDegree G x))
    (a : G.vertexSet) (ha : ¬∃ b : G.vertexSet,a≠b ∧ FaultConnected G (2*k) a b) :
    ∃ (F : Type v) (hF : Fintype F) (H : Graph {x : V // x≠a.val} F),
      H.vertexSet=Set.univ ∧ (letI := hF; ∀ x,Even (nativeDegree H x)) ∧
      (letI := hF; HasNativeForestPacking H k → HasNativeForestPacking G k) := by
  classical
  let f : V ≃ Option {x : V // x≠a.val} := (Equiv.optionSubtypeNe a.val).symm
  let J := G.map f
  have hfull : J.vertexSet=Set.univ := by
    change f '' G.vertexSet=Set.univ
    exact (congrArg (fun S : Set V => f '' S) hall).trans
      (Set.image_univ_of_surjective f.surjective)
  have hf0 : f a.val=none := Equiv.optionSubtypeNe_symm_self a.val
  have hinactive : ∀ x y : J.vertexSet,x.val=none → FaultConnected J (2*k) x y → x=y := by
    intro x y hx hxy
    obtain ⟨b,hb,hbx⟩ := x.property
    obtain ⟨c,hc,hcy⟩ := y.property
    have hb0 : b=a.val := f.injective (hbx.trans (hx.trans hf0.symm))
    have hxb : mapVertex G f ⟨b,hb⟩=x := Subtype.ext hbx
    have hyc : mapVertex G f ⟨c,hc⟩=y := Subtype.ext hcy
    have hconn : FaultConnected G (2*k) ⟨b,hb⟩ ⟨c,hc⟩ :=
      faultConnected_of_injective_map G f f.injective (by simpa only [hxb,hyc] using hxy)
    have hbA : (⟨b,hb⟩:G.vertexSet)=a := Subtype.ext hb0
    have hca : (⟨c,hc⟩:G.vertexSet)=a := by
      by_contra hn
      exact ha ⟨⟨c,hc⟩,Ne.symm hn,by simpa only [hbA] using hconn⟩
    apply Subtype.ext
    exact hbx.symm.trans ((congrArg (fun z : G.vertexSet => f z.val)
      (hbA.trans hca.symm)).trans hcy)
  obtain ⟨F,hF,H,hH,hd,hpack⟩ := exists_native_steiner_packing_reduction J k hfull
    (even_native_degrees_map G f hdeg) hinactive
  refine ⟨F,hF,H,hH,hd,?_⟩
  let := hF
  exact fun hp => forestPacking_of_injective_map G f f.injective k (hpack hp)
end LightEFTSpanners.EvenSplitting
