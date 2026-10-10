import GreedyShortcuts
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
        | some moduleName => (`GreedyShortcuts).isPrefixOf moduleName
        | none => false
      | none => false
    if ours then
      count := count + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then
    throwError "No GreedyShortcuts declarations were audited"
  logInfo m!"Audited {count} GreedyShortcuts declarations; only {allowed}"

#print axioms GreedyShortcuts.RecapArithmetic.rounds_bound
#print axioms GreedyShortcuts.FinitePotential.zero_after_blocks

#print axioms GreedyShortcuts.FiniteGreedy.System.run_terminates
#print axioms GreedyShortcuts.FiniteGreedy.System.final_card_of_relative_progress

#print axioms GreedyShortcuts.DirectedPaths.reachable_augment_iff
#print axioms GreedyShortcuts.GraphGreedy.output_hop_bound
#print axioms GreedyShortcuts.ShortcutWalk.repairEdges_repair

#print axioms GreedyShortcuts.WarmupUnweighted.output_card_bound

#print axioms GreedyShortcuts.CanonicalSegments.intersection_convex
#print axioms GreedyShortcuts.WarmupBound.output_card_bound_all
#print axioms GreedyShortcuts.FiniteWindows.exists_high_score
