import SlackSparsification
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? name with
      | some idx => match moduleNames[idx.toNat]? with
        | some moduleName => (`SlackSparsification).isPrefixOf moduleName
        | none => false
      | none => false
    if isProject then
      count := count + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "No project declarations found"
  logInfo m!"Axiom audit passed: {count} project declarations"
#print axioms SlackSparsification.complete_of_slack
