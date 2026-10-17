import LightEFTSpanners.NativeCoreForestExpansion
import LightEFTSpanners.MultigraphContractionSize

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts
variable {V W E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Every required actual edge-fault connection survives a native vertex map,
by the exact original-ID preimage cut identity. -/
theorem faultConnected_map (G : Graph V E) (f : V → W) {k : ℕ}
    {x y : G.vertexSet} (h : FaultConnected G k x y) :
    FaultConnected (G.map f) k (mapVertex G f x) (mapVertex G f y) := by
  apply faultConnected_of_cut_lower
  intro S hx hy
  rw [edgeCut_map]
  exact faultConnected_le_cut G h (f ⁻¹' S) hx hy

/-- Even native degrees remain even after contraction. All original parallel
IDs and newly formed loops are retained; their cut contribution is exact. -/
theorem even_native_degrees_map [Fintype V] (G : Graph V E) (f : V → W)
    (hdeg : ∀ v,Even (nativeDegree G v)) : ∀ w,Even (nativeDegree (G.map f) w) := by
  apply even_degrees_of_even_cuts
  intro S
  have h := even_cut_of_even_degrees G hdeg (f ⁻¹' S)
  simpa only [cutSize,edgeCut_map] using h
end LightEFTSpanners.EvenSplitting
