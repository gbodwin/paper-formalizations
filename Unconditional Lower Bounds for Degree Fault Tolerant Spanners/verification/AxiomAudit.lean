import DegreeFaultSpanners
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let root : Name := `DegreeFaultSpanners
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
    throwError "No project declarations audited"
  logInfo m!"Axiom audit passed for {count} DegreeFaultSpanners declarations."

#print axioms DegreeFaultSpanners.theorem_five_uniform_parameters
#print axioms DegreeFaultSpanners.isDegreeFaultSpanner_iff_edist
