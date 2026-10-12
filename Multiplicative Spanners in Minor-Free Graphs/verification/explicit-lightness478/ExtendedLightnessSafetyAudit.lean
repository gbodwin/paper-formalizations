import MinorFreeSpanners.ExplicitLightnessCoefficient
import MinorFreeSpanners.GreedyMinorPolylogLightness
import MinorFreeSpanners.EdgeWeightTransport
import MinorFreeSpanners.PositiveEdgeMinorLightness
import MinorFreeSpanners.DyadicStreamCover
import MinorFreeSpanners.FiniteCoverBudget
import MinorFreeSpanners.HeavyStreamsBudget
import MinorFreeSpanners.HeavyGraphBudget
import MinorFreeSpanners.NonnegativeWeightedGirth
import MinorFreeSpanners.LowGraphBudget
import MinorFreeSpanners.UnitTreeGraphBudget
import MinorFreeSpanners.CorrectedUnitTreeLightness
import MinorFreeSpanners.NormalizedMinorLightness
import MinorFreeSpanners.GreedyMinorLightness
import MinorFreeSpanners.CanonicalFiniteStream
import MinorFreeSpanners.CanonicalFreshPaidPhase
import MinorFreeSpanners.CanonicalFreshPhaseAlternative
import MinorFreeSpanners.CanonicalHistoryStep
import MinorFreeSpanners.CanonicalPrefixHistoryStep
import MinorFreeSpanners.CanonicalStreamBudget
import MinorFreeSpanners.ConstructedGeometricStream
import MinorFreeSpanners.FiniteGeometricStreamBound
import MinorFreeSpanners.FreshActualPhaseAlternative
import MinorFreeSpanners.FreshActualRetainedPhase
import MinorFreeSpanners.FreshRetainedPhaseCapTransport
import MinorFreeSpanners.InitialPrefixState
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "MINOR_STREAM_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`MinorFreeSpanners.CanonicalFiniteStream,
    `MinorFreeSpanners.CanonicalFreshPaidPhase,
    `MinorFreeSpanners.CanonicalFreshPhaseAlternative,
    `MinorFreeSpanners.CanonicalHistoryStep,
    `MinorFreeSpanners.CanonicalPrefixHistoryStep,
    `MinorFreeSpanners.CanonicalStreamBudget,
    `MinorFreeSpanners.ConstructedGeometricStream,
    `MinorFreeSpanners.FiniteGeometricStreamBound,
    `MinorFreeSpanners.FreshActualPhaseAlternative,
    `MinorFreeSpanners.FreshActualRetainedPhase,
    `MinorFreeSpanners.FreshRetainedPhaseCapTransport,
    `MinorFreeSpanners.InitialPrefixState,
    `MinorFreeSpanners.DyadicStreamCover,
    `MinorFreeSpanners.FiniteCoverBudget,
    `MinorFreeSpanners.HeavyStreamsBudget,
    `MinorFreeSpanners.HeavyGraphBudget,
    `MinorFreeSpanners.NonnegativeWeightedGirth,
    `MinorFreeSpanners.LowGraphBudget,
    `MinorFreeSpanners.UnitTreeGraphBudget,
    `MinorFreeSpanners.CorrectedUnitTreeLightness,
    `MinorFreeSpanners.NormalizedMinorLightness,
    `MinorFreeSpanners.GreedyMinorLightness,
    `MinorFreeSpanners.ExplicitLightnessCoefficient,
    `MinorFreeSpanners.GreedyMinorPolylogLightness,
    `MinorFreeSpanners.EdgeWeightTransport,
    `MinorFreeSpanners.PositiveEdgeMinorLightness]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe reconstructed Minor declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden reconstructed Minor axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"MINOR_STREAM_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"MINOR_STREAM_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`MinorFreeSpanners.canonical_fresh_paid_phase,
      `MinorFreeSpanners.canonical_finite_stream,
      `MinorFreeSpanners.exists_initial_prefix_state,
      `MinorFreeSpanners.finite_geometric_stream_bound,
      `MinorFreeSpanners.heavy_graph_budget,
      `MinorFreeSpanners.normalized_minor_lightness,
      `MinorFreeSpanners.greedy_minor_lightness,
      `MinorFreeSpanners.greedy_minor_polylog_lightness,
      `MinorFreeSpanners.positive_edge_minor_lightness] do
    IO.eprintln s!"MINOR_STREAM_CLOSURE_BEGIN {root}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name | throwError "Missing closure constant: {name}"
        if ci.isUnsafe then throwError "Unsafe closure constant: {root}: {name}"
        match ci with
        | .axiomInfo _ =>
          axioms := axioms.insert name
          unless allowed.contains name do throwError "Forbidden closure axiom: {root}: {name}"
        | _ => pure ()
        for dep in ci.getUsedConstantsAsSet.toList do
          unless seen.contains dep do todo := todo.push dep
    logInfo m!"MINOR_STREAM_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
