import VFTSpanners
import Lean.Util.CollectAxioms

/-! Fail, rather than merely print a warning, if any project declaration has
an axiom dependency outside the three standard logical foundations. Selection
uses the defining module, so it includes private/generated
declarations and declarations added to namespaces outside `VFTSpanners`. -/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => match moduleNames[idx.toNat]? with
        | some moduleName => `VFTSpanners |>.isPrefixOf moduleName
        | none => false
      | none => false
    if fromProject then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then
    throwError "No project declarations found; the audit did not run"
  logInfo m!"Axiom audit passed: {count} declarations defined in VFTSpanners modules; allowed axioms: {allowed}"

#print axioms VFTSpanners.vft_greedy_theorem_one
#print axioms VFTSpanners.covered_iff_distance
#print axioms VFTSpanners.vft_greedy_zero_faults
#print axioms VFTSpanners.corollary_two_from_moore

#print axioms VFTSpanners.moore_edge_bound
#print axioms VFTSpanners.extremalEdges_moore
#print axioms VFTSpanners.corollary_two
