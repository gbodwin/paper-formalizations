import MinorFreeSpanners
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let root := `MinorFreeSpanners
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => match modules[idx.toNat]? with
        | some mod => root.isPrefixOf mod
        | none => false
      | none => false
    if fromProject then
      count := count + 1
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "No MinorFreeSpanners declarations found"
  logInfo m!"Axiom audit passed for {count} MinorFreeSpanners declarations; allowed axioms: {allowed}"

#print axioms MinorFreeSpanners.claim19_counterexample_with_source_hypotheses
#print axioms MinorFreeSpanners.claim19_corrected
#print axioms MinorFreeSpanners.cluster_threshold_repair
#print axioms MinorFreeSpanners.theorem11
#print axioms MinorFreeSpanners.high_girth_spanner_eq
#print axioms MinorFreeSpanners.cliqueMinorFree_two_iff
#print axioms MinorFreeSpanners.cliqueMinorFree_of_edges
#print axioms MinorFreeSpanners.density_increment_exponent
