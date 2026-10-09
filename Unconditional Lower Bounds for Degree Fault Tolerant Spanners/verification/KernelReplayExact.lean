import LeanChecker

/-!
Verification-only driver for the unmodified official Lean 4.34.0 checker.
The CLI enumerates all .olean files on LEAN_PATH and runs targets concurrently.
This driver invokes the identical replayFromImports implementation on an exact,
explicit list, sequentially, to bound memory and avoid unrelated directory scans.
It adds no theorem, axiom, or proof implementation to the paper library.
-/

#eval do
  for module in #[
    `DegreeFaultSpanners.SlopeAlgebra,
    `DegreeFaultSpanners.Incidence,
    `DegreeFaultSpanners.FaultSpanner,
    `DegreeFaultSpanners.ShortReach,
    `DegreeFaultSpanners.GeometryWalk,
    `DegreeFaultSpanners.PathStraightening,
    `DegreeFaultSpanners.Construction,
    `DegreeFaultSpanners.CycleObstruction,
    `DegreeFaultSpanners.Blowup,
    `DegreeFaultSpanners.ObstructionAssembly,
    `DegreeFaultSpanners.Parameters,
    `DegreeFaultSpanners.RealBound,
    `DegreeFaultSpanners.PaperTheorem,
    `DegreeFaultSpanners.Padding,
    `DegreeFaultSpanners.DenseWitness,
    `DegreeFaultSpanners.AllSizesParameters,
    `DegreeFaultSpanners.AllSizesRealBound,
    `DegreeFaultSpanners.AllSizesTheorem,
    `DegreeFaultSpanners
  ] do
    IO.println s!"BEGIN kernel replay {module}"
    replayFromImports module
    IO.println s!"PASS kernel replay {module}"
