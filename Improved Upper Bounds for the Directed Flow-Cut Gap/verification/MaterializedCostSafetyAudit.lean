import DirectedFlowCutGap.MaterializedGraphPath
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.IndexedRationalRead,
    `DirectedFlowCutGap.OutgoingCostProgram,
    `DirectedFlowCutGap.PathCostMaterialization,
    `DirectedFlowCutGap.MaterializedPathSum,
    `DirectedFlowCutGap.MaterializedGraphPath]
  let mut count : Nat := 0
  for module in wanted do
    let mut found : Nat := 0
    for (name, ci) in env.constants.toList do
      let owned := match env.getModuleIdxFor? name with
        | some idx => modules[idx.toNat]! == module
        | none => false
      if owned then
        found := found + 1
        if ci.isUnsafe then throwError "Unsafe materialized graph cost declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden materialized graph cost axiom: {name}: {ax}"
    if found == 0 then throwError "No declarations audited for {module}"
    count := count + found
    logInfo m!"MATERIALIZED_COST_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"MATERIALIZED_COST_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.IndexedRationalRead.read_return,
      `DirectedFlowCutGap.OutgoingCostProgram.outgoing_bit,
      `DirectedFlowCutGap.PathCostMaterialization.materialize_return,
      `DirectedFlowCutGap.MaterializedPathSum.sum_bit,
      `DirectedFlowCutGap.MaterializedGraphPath.path_cost_bit] do
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
    logInfo m!"MATERIALIZED_COST_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
