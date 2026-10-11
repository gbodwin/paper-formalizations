import DirectedFlowCutGap.PreparedRowEmit
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let fromCounter := match env.getModuleIdxFor? name with
      | some idx => #[`DirectedFlowCutGap.HeapWordEmit, `DirectedFlowCutGap.HeapPairEmit, `DirectedFlowCutGap.IndexedPairEmit, `DirectedFlowCutGap.PreparedRowEmit].contains (modules[idx.toNat]!)
      | none => false
    if fromCounter then
      count := count + 1
      if ci.isUnsafe then throwError "Unsafe counter declaration: {name}"
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do throwError "Forbidden counter axiom: {name}: {ax}"
  if count == 0 then throwError "Counter module was not audited"
  logInfo m!"ROW_EMISSION_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.HeapWordEmit.emit_bit,
      `DirectedFlowCutGap.HeapPairEmit.emit_bit,
      `DirectedFlowCutGap.IndexedPairEmit.emit_bit,
      `DirectedFlowCutGap.PreparedRowEmit.emit] do
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
    logInfo m!"ROW_EMISSION_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
