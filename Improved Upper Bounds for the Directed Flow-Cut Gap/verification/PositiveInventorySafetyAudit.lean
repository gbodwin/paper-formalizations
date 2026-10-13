import DirectedFlowCutGap.ActualPositiveInventory
import DirectedFlowCutGap.PositiveInventoryBranches
import DirectedFlowCutGap.PositiveInventoryCall
import DirectedFlowCutGap.PositiveInventoryCallLift
import DirectedFlowCutGap.PositiveInventoryData
import DirectedFlowCutGap.PositiveInventoryExecution
import DirectedFlowCutGap.PositiveInventoryPrefix
import DirectedFlowCutGap.PositiveInventoryProgram
import DirectedFlowCutGap.PositiveInventoryRefinement
import DirectedFlowCutGap.PositiveInventoryTrace
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "POSITIVE_INVENTORY_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualPositiveInventory,`DirectedFlowCutGap.PositiveInventoryBranches,`DirectedFlowCutGap.PositiveInventoryCall,`DirectedFlowCutGap.PositiveInventoryCallLift,`DirectedFlowCutGap.PositiveInventoryData,`DirectedFlowCutGap.PositiveInventoryExecution,`DirectedFlowCutGap.PositiveInventoryPrefix,`DirectedFlowCutGap.PositiveInventoryProgram,`DirectedFlowCutGap.PositiveInventoryRefinement,`DirectedFlowCutGap.PositiveInventoryTrace]
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
    logInfo m!"POSITIVE_INVENTORY_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"POSITIVE_INVENTORY_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.PositiveInventory.program,`DirectedFlowCutGap.PositiveInventory.zero_return,`DirectedFlowCutGap.PositiveInventory.numerator_prefix,`DirectedFlowCutGap.PositiveInventory.zero_advance,`DirectedFlowCutGap.PositiveInventory.positive_advance,`DirectedFlowCutGap.PositiveInventory.inventory_return,`DirectedFlowCutGap.PositiveInventory.scan,`DirectedFlowCutGap.PositiveInventory.steps_bound,`DirectedFlowCutGap.PositiveInventory.cells_bound,`DirectedFlowCutGap.PositiveInventory.inventory_items,`DirectedFlowCutGap.PositiveInventory.inventory_bit,`DirectedFlowCutGap.PositiveInventory.selected_original] do
    IO.eprintln s!"POSITIVE_INVENTORY_CLOSURE_BEGIN {root}"
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
    logInfo m!"POSITIVE_INVENTORY_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
