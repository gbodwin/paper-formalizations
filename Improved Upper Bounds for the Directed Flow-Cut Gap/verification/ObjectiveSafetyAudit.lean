import DirectedFlowCutGap.ActualObjectiveRow
import DirectedFlowCutGap.ActualRationalProduct
import DirectedFlowCutGap.CanonicalRationalProductProgram
import DirectedFlowCutGap.CanonicalRationalProductReturn
import DirectedFlowCutGap.ObjectiveProductListBounds
import DirectedFlowCutGap.ObjectiveProductListProgram
import DirectedFlowCutGap.ObjectiveProductListTrace
import DirectedFlowCutGap.ObjectiveRowExecution
import DirectedFlowCutGap.ObjectiveRowProgram
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "OBJECTIVE_COMPONENT_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualObjectiveRow,`DirectedFlowCutGap.ActualRationalProduct,`DirectedFlowCutGap.CanonicalRationalProductProgram,`DirectedFlowCutGap.CanonicalRationalProductReturn,`DirectedFlowCutGap.ObjectiveProductListBounds,`DirectedFlowCutGap.ObjectiveProductListProgram,`DirectedFlowCutGap.ObjectiveProductListTrace,`DirectedFlowCutGap.ObjectiveRowExecution,`DirectedFlowCutGap.ObjectiveRowProgram]
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
    logInfo m!"OBJECTIVE_COMPONENT_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"OBJECTIVE_COMPONENT_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.CanonicalRationalProduct.product_return,`DirectedFlowCutGap.CanonicalRationalProduct.product_bit,`DirectedFlowCutGap.ObjectiveProductList.products_return,`DirectedFlowCutGap.ObjectiveRow.objective_high,`DirectedFlowCutGap.ObjectiveRow.result_eq_objective,`DirectedFlowCutGap.ObjectiveRow.objective_bit] do
    IO.eprintln s!"OBJECTIVE_COMPONENT_CLOSURE_BEGIN {root}"
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
    logInfo m!"OBJECTIVE_COMPONENT_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
