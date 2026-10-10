import LinearDistancePreservers.NaturalBoundary
import Lean.Util.CollectAxioms

/-! Audit all declarations by defining module, including private/generated
ones and declarations whose namespace differs from their defining module. -/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[`LinearDistancePreservers.NaturalBoundary] do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      let fromProject := match env.getModuleIdxFor? name with
        | some idx => match moduleNames[idx.toNat]? with
          | some moduleName => root.isPrefixOf moduleName
          | none => false
        | none => false
      if fromProject then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Disallowed axiom {ax} in {name}"
    if count == 0 then
      throwError "No declarations found for {root}; the audit did not run"
    logInfo m!"Axiom audit passed: {count} declarations defined in {root} modules; allowed axioms: {allowed}"



#check @LinearDistancePreservers.NaturalBoundary.every_deficit_has_bounded_count_subsequence
