import LengthExpander
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let own := match env.getModuleIdxFor? name with
      | some i => match modules[i.toNat]? with
        | some m => (`LengthExpander).isPrefixOf m
        | none => false
      | none => false
    if own then
      count := count + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "Audit found no declarations"
  logInfo m!"PASS: {count} LengthExpander declarations; allowed axioms {allowed}"
#print axioms LengthExpander.increasing_walk_unique
#print axioms LengthExpander.exists_finite_maximal_sequence
#print axioms LengthExpander.SourceCorrections.asymmetric_demand_not_undirected_count
#print axioms LengthExpander.SourceCorrections.half_not_integral
