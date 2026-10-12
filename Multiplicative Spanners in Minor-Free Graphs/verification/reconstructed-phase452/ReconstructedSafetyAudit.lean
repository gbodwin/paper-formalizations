import MinorFreeSpanners.ActualPhaseAlternative
import MinorFreeSpanners.ActualRetainedPhase
import MinorFreeSpanners.ActualSelectedRadiusFloor
import MinorFreeSpanners.ActualShortRadiusFloor
import MinorFreeSpanners.ActualWeakRadiusFloor
import MinorFreeSpanners.CanonicalActualPhase
import MinorFreeSpanners.CanonicalCorrectedGirth
import MinorFreeSpanners.CanonicalPhaseNumerics
import MinorFreeSpanners.CanonicalPhaseParameterChoice
import MinorFreeSpanners.CanonicalScaleChoice
import MinorFreeSpanners.CoarsenedConnectorFreshness
import MinorFreeSpanners.EmptyRootStreamBudget
import MinorFreeSpanners.EmptySelectedTree
import MinorFreeSpanners.FiniteHistoryLedger
import MinorFreeSpanners.FreshFiniteRetainedPhaseOutput
import MinorFreeSpanners.FreshShortToRetainedFamily
import MinorFreeSpanners.GeometricScaleBudget
import MinorFreeSpanners.OriginalRootRadiusFloor
import MinorFreeSpanners.RetainedHistoryStep
import MinorFreeSpanners.RetainedPhaseCapTransport
import MinorFreeSpanners.RetainedScaleState
import MinorFreeSpanners.SelectedClassHeavyInputs
import MinorFreeSpanners.SelectedResidualCoarsening
import MinorFreeSpanners.SelectedSpendingRadiusFloor
import MinorFreeSpanners.SingletonAnchorCredit
import MinorFreeSpanners.SingletonAnchorEdges
import MinorFreeSpanners.SingletonAnchorPriorLedger
import MinorFreeSpanners.SingletonAnchorRetainedPhase
import MinorFreeSpanners.SingletonAnchorShortPhase
import MinorFreeSpanners.SingletonAnchorTransport
import MinorFreeSpanners.SingletonAnchorTree
import MinorFreeSpanners.SingletonClusterBase
import MinorFreeSpanners.UnitTreeHeavyScaleBound
import MinorFreeSpanners.WeightPrefixHost
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "MINOR_RECOVERED_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`MinorFreeSpanners.ActualPhaseAlternative,
    `MinorFreeSpanners.ActualRetainedPhase,
    `MinorFreeSpanners.ActualSelectedRadiusFloor,
    `MinorFreeSpanners.ActualShortRadiusFloor,
    `MinorFreeSpanners.ActualWeakRadiusFloor,
    `MinorFreeSpanners.CanonicalActualPhase,
    `MinorFreeSpanners.CanonicalCorrectedGirth,
    `MinorFreeSpanners.CanonicalPhaseNumerics,
    `MinorFreeSpanners.CanonicalPhaseParameterChoice,
    `MinorFreeSpanners.CanonicalScaleChoice,
    `MinorFreeSpanners.CoarsenedConnectorFreshness,
    `MinorFreeSpanners.EmptyRootStreamBudget,
    `MinorFreeSpanners.EmptySelectedTree,
    `MinorFreeSpanners.FiniteHistoryLedger,
    `MinorFreeSpanners.FreshFiniteRetainedPhaseOutput,
    `MinorFreeSpanners.FreshShortToRetainedFamily,
    `MinorFreeSpanners.GeometricScaleBudget,
    `MinorFreeSpanners.OriginalRootRadiusFloor,
    `MinorFreeSpanners.RetainedHistoryStep,
    `MinorFreeSpanners.RetainedPhaseCapTransport,
    `MinorFreeSpanners.RetainedScaleState,
    `MinorFreeSpanners.SelectedClassHeavyInputs,
    `MinorFreeSpanners.SelectedResidualCoarsening,
    `MinorFreeSpanners.SelectedSpendingRadiusFloor,
    `MinorFreeSpanners.SingletonAnchorCredit,
    `MinorFreeSpanners.SingletonAnchorEdges,
    `MinorFreeSpanners.SingletonAnchorPriorLedger,
    `MinorFreeSpanners.SingletonAnchorRetainedPhase,
    `MinorFreeSpanners.SingletonAnchorShortPhase,
    `MinorFreeSpanners.SingletonAnchorTransport,
    `MinorFreeSpanners.SingletonAnchorTree,
    `MinorFreeSpanners.SingletonClusterBase,
    `MinorFreeSpanners.UnitTreeHeavyScaleBound,
    `MinorFreeSpanners.WeightPrefixHost]
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
    logInfo m!"MINOR_RECOVERED_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"MINOR_RECOVERED_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`MinorFreeSpanners.exists_actual_retained_phase,
      `MinorFreeSpanners.canonical_actual_phase,
      `MinorFreeSpanners.fresh_retained_family_after_paid_short,
      `MinorFreeSpanners.fresh_retained_phase_to_history_step,
      `MinorFreeSpanners.singleton_anchor_retained_phase] do
    IO.eprintln s!"MINOR_RECOVERED_CLOSURE_BEGIN {root}"
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
    logInfo m!"MINOR_RECOVERED_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
