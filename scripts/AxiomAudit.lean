import BodwinPapers
import Lean.Util.CollectAxioms

/-! Fail, rather than merely print a warning, if any project declaration has
an axiom dependency outside the three standard logical foundations. This
includes compiler-generated declarations under the project namespace. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if `BodwinPapers |>.isPrefixOf name then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then
    throwError "No project declarations found; the audit did not run"
  logInfo m!"Axiom audit passed: {count} project declarations; allowed axioms: {allowed}"

#print axioms BodwinPapers.VFTSpanners.vft_greedy_theorem_one
#print axioms BodwinPapers.VFTSpanners.covered_iff_distance
#print axioms BodwinPapers.VFTSpanners.vft_greedy_zero_faults
#print axioms BodwinPapers.VFTSpanners.corollary_two_from_moore

#print axioms BodwinPapers.VFTSpanners.moore_edge_bound
#print axioms BodwinPapers.VFTSpanners.extremalEdges_moore
#print axioms BodwinPapers.VFTSpanners.corollary_two
