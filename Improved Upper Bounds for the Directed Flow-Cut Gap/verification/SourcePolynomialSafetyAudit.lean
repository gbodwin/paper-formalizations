import DirectedFlowCutGap.SourcePackingPolynomialCosts
import DirectedFlowCutGap.SourcePackingPolynomialBound
import DirectedFlowCutGap.SourcePackingPolynomialExecution
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "SOURCE_POLYNOMIAL_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.SourcePackingPolynomialCosts,`DirectedFlowCutGap.SourcePackingPolynomialBound,`DirectedFlowCutGap.SourcePackingPolynomialExecution]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe oracle component declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden oracle component axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"SOURCE_POLYNOMIAL_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"SOURCE_POLYNOMIAL_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.SourcePackingPolynomial.bound_EnumeratedPacking_instructionBound,`DirectedFlowCutGap.SourcePackingPolynomial.instruction_le_eval,`DirectedFlowCutGap.SourcePackingPolynomial.physical_eval,`DirectedFlowCutGap.SourcePackingPolynomial.physical_le_eval,`DirectedFlowCutGap.SourcePackingPolynomial.fixed_polynomial_bound,`DirectedFlowCutGap.SourcePacking.solve_source_polynomial_bit] do
    IO.eprintln s!"SOURCE_POLYNOMIAL_CLOSURE_BEGIN {root}"
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
    logInfo m!"SOURCE_POLYNOMIAL_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
