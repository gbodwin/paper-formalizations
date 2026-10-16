import LightEFTSpanners.NativePackingVertexTransport

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts SimpleGraph
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Eliminating a singleton connectivity island yields a smaller actual
Eulerian graph whose genuine forest packing lifts to the original graph.
The isolated island's reflexive demands are explicitly restored. -/
theorem exists_native_steiner_packing_reduction (G : Graph (Option V) E) (k : ℕ)
    (hall : G.vertexSet=Set.univ) (hdeg : ∀ x,Even (nativeDegree G x))
    (hinactive : ∀ x y : G.vertexSet,x.val=none → FaultConnected G (2*k) x y → x=y) :
    ∃ (F : Type v) (hF : Fintype F) (H : Graph V F),
      H.vertexSet=Set.univ ∧ (letI := hF; ∀ x,Even (nativeDegree H x)) ∧
      (letI := hF; HasNativeForestPacking H k → HasNativeForestPacking G k) := by
  classical
  have hm (a : V) : some a∈G.vertexSet := by rw [hall]; trivial
  let P : V → V → Prop := fun a b => FaultConnected G (2*k) ⟨some a,hm a⟩ ⟨some b,hm b⟩
  have hc : RequiredConnectivity G P k := fun a b h => ⟨hm a,hm b,h⟩
  obtain ⟨F,hF,H,hresult,hv,hd,hcH⟩ := exists_native_steiner_reduction G P k hdeg hc
  let := hF
  refine ⟨F,hF,centerCore H,?_,hd,?_⟩
  · rw [hv,hall]; rfl
  · rintro ⟨A,hA,hAd,hAj⟩
    obtain ⟨B,hB,hBd,hBj⟩ := hresult.1.lift_core_forests A (fun c => (hA c).1) hAd
    refine ⟨B,hB,hBd,?_⟩
    intro c x y hxy
    cases hx : x.val with
    | none =>
      have heq := hinactive x y hx hxy
      subst y; exact Reachable.rfl
    | some a =>
      cases hy : y.val with
      | none =>
        have hs : FaultConnected G (2*k) y x := fun S hS => (hxy S hS).symm
        have heq := hinactive y x hy hs
        subst x; exact Reachable.rfl
      | some b =>
        have hxa : x=⟨some a,hm a⟩ := Subtype.ext hx
        have hyb : y=⟨some b,hm b⟩ := Subtype.ext hy
        have hp : P a b := by simpa only [hxa,hyb] using hxy
        obtain ⟨haH,hbH,hfc⟩ := hcH a b hp
        have hj := hAj c ⟨a,haH⟩ ⟨b,hbH⟩ hfc
        obtain ⟨haG,hbG,hr⟩ := hBj c a b ⟨haH,hbH,hj⟩
        have hx' : x=(⟨some a,haG⟩:G.vertexSet) := Subtype.ext hx
        have hy' : y=(⟨some b,hbG⟩:G.vertexSet) := Subtype.ext hy
        rw [hx',hy']
        exact hr
end LightEFTSpanners.EvenSplitting
