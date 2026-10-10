import LightEFTSpanners
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? name with
      | some idx => match modules[idx.toNat]? with
        | some m => (`LightEFTSpanners).isPrefixOf m
        | none => false
      | none => false
    if ours then
      count := count + 1
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "No project declarations audited"
  logInfo m!"LightEFTSpanners: {count} declarations audited; only {allowed}"
