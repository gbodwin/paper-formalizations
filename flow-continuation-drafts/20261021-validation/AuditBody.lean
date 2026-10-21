import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Generated imports and exact expected/new module arrays precede this body.
Every owned declaration, including private/generated constants, is audited.
Every declaration owned by a new module is a type/body closure root. -/
set_option stderrAsMessages false
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let expected := flowExpectedModules
  let wanted := flowNewModules
  let actual := env.allImportedModuleNames.filter fun n => (`DirectedFlowCutGap).isPrefixOf n
  unless actual.size == expected.size do throwError "Flow module count mismatch"
  for module in actual do
    unless expected.contains module do throwError "Unexpected Flow module: {module}"
  for module in expected do
    unless actual.contains module do throwError "Missing Flow module: {module}"
    IO.eprintln s!"MODULE {module}"
  let mut owned : Array Name := #[]
  let mut counts : NameMap Nat := {}
  let mut fullCount := 0
  for (name, ci) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let some module := env.allImportedModuleNames[idx.toNat]? |
        throwError "Missing defining module for {name}"
      if expected.contains module then
        fullCount := fullCount + 1
        counts := counts.insert module ((counts.find? module).getD 0 + 1)
        if ci.isUnsafe then throwError "Unsafe owned declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
        IO.eprintln s!"ATTR {module}|{name}"
        if wanted.contains module then
          owned := owned.push name
          IO.eprintln s!"ROOT {module}|{name}"
  for module in expected do
    if (counts.find? module).getD 0 == 0 then
      throwError "No owned declarations found in {module}"
  let mut todo := owned
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing dependency: {name}"
      if ci.isUnsafe then throwError "Unsafe type/body dependency: {name}"
      match ci with
      | .axiomInfo _ =>
        unless allowed.contains name do throwError "Forbidden dependency axiom: {name}"
      | _ => pure ()
      for dep in ci.getUsedConstantsAsSet.toList do
        unless seen.contains dep do todo := todo.push dep
  for root in flowRequiredRoots do
    unless owned.contains root do throwError "Required new root absent: {root}"
  IO.eprintln s!"AUDIT_PASS modules={actual.size} declarations={fullCount} roots={owned.size} closure={seen.toList.length}"
