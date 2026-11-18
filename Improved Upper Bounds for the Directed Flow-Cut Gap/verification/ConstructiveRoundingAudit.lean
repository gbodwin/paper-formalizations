import DirectedFlowCutGap.OptimalFlowCutBounds
import DirectedFlowCutGap.WeakDecompositionBounds
import DirectedFlowCutGap.SparsestVertexCorollary
import DirectedFlowCutGap.SparsestEdgeCorollary
import DirectedFlowCutGap.EncodedWeightedRounding
import DirectedFlowCutGap.EncodedVertexSolver
import DirectedFlowCutGap.EncodedVertexAmplification
import DirectedFlowCutGap.EncodedEdgeRounding
import DirectedFlowCutGap.EncodedEdgeSolver
import DirectedFlowCutGap.WeakDecompositionExactWeight
import Lean.Compiler.Old
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option stderrAsMessages false

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let selected := modules.filter fun name => (`DirectedFlowCutGap).isPrefixOf name
  let targets := #[
    `DirectedFlowCutGap.OptimalFlowCutBounds, `DirectedFlowCutGap.AdaptiveVertexBound,
    `DirectedFlowCutGap.AdaptiveEdgeBound, `DirectedFlowCutGap.WeakDecomposition,
    `DirectedFlowCutGap.WeakDecompositionBounds, `DirectedFlowCutGap.SparsestVertexCorollary,
    `DirectedFlowCutGap.SparsestEdgeCorollary, `DirectedFlowCutGap.IntegerClosureAsymptotic,
    `DirectedFlowCutGap.EncodedIntegerRounding, `DirectedFlowCutGap.EncodedUniformRounding,
    `DirectedFlowCutGap.EncodedWeightedRounding, `DirectedFlowCutGap.EncodedSizeRounding,
    `DirectedFlowCutGap.EncodedCutSelection, `DirectedFlowCutGap.EncodedVertexSolver,
    `DirectedFlowCutGap.FractionalCoverRawGuesses,
    `DirectedFlowCutGap.EncodedVertexInput, `DirectedFlowCutGap.EncodedAmplification,
    `DirectedFlowCutGap.EncodedVertexAmplification, `DirectedFlowCutGap.EncodedEdgeLabels,
    `DirectedFlowCutGap.EncodedEdgeGadget, `DirectedFlowCutGap.EncodedEdgeRounding,
    `DirectedFlowCutGap.EdgeLineReduction, `DirectedFlowCutGap.EncodedEdgeLineInput,
    `DirectedFlowCutGap.EncodedEdgeSolver, `DirectedFlowCutGap.WeakDecompositionExactWeight]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut counts : NameMap Nat := {}
  let mut compilerEntries : Nat := 0
  let mut declarations : Nat := 0
  let mut roots : Array Name := #[]
  let mut axioms : NameSet := {}
  for name in selected do
    IO.eprintln s!"MODULE {name}"
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing defining module of {name}"
    unless selected.contains mod do continue
    if info.isUnsafe || info.isPartial then
      let some parent := Compiler.isUnsafeRecName? name |
        throwError "Unexpected unsafe or partial declaration {name}"
      let some original := env.find? parent |
        throwError "Missing logical declaration for compiler recursion entry {name}"
      if original.isUnsafe || original.isPartial || env.getModuleIdxFor? parent != some idx then
        throwError "Unbound compiler recursion entry {name}"
      IO.eprintln s!"COMPILER_RECURSION {mod}|{name}|{parent}"
      compilerEntries := compilerEntries + 1
      continue
    declarations := declarations + 1
    counts := counts.insert mod ((counts.find? mod).getD 0 + 1)
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
      axioms := axioms.insert ax
    if targets.contains mod then roots := roots.push name
  for name in targets do
    if (counts.find? name).getD 0 == 0 then throwError "No logical declarations in {name}"
  for theoremName in #[
    `DirectedFlowCutGap.OptimalFlowCutBounds.main_theorems_attained_uniform,
    `DirectedFlowCutGap.WeakDecomposition.vertex_scaled_family,
    `DirectedFlowCutGap.WeakDecomposition.edge_family_of_preprocessed_factor,
    `DirectedFlowCutGap.EncodedIntegerRounding.law_eq,
    `DirectedFlowCutGap.EncodedUniformRounding.expected_size_uniform,
    `DirectedFlowCutGap.EncodedWeightedRounding.expected_cost_uniform,
    `DirectedFlowCutGap.EncodedSizeRounding.expected_cost_uniform,
    `DirectedFlowCutGap.EncodedVertexSolver.massBit_support_valid,
    `DirectedFlowCutGap.EncodedVertexSolver.sizeBit_support_valid,
    `DirectedFlowCutGap.EncodedVertexSolver.mass_expected_uniform,
    `DirectedFlowCutGap.EncodedVertexSolver.size_expected_uniform,
    `DirectedFlowCutGap.EncodedVertexSolver.bit_bad_cost_le,
    `DirectedFlowCutGap.EncodedVertexInput.parse_encode,
    `DirectedFlowCutGap.EncodedVertexAmplification.sourcePolynomialBitTree_encode,
    `DirectedFlowCutGap.EncodedVertexAmplification.polynomial_failure_le,
    `DirectedFlowCutGap.EncodedAmplification.samples_law,
    `DirectedFlowCutGap.EncodedAmplification.bitTree_within,
    `DirectedFlowCutGap.EncodedEdgeGadget.build_size_le,
    `DirectedFlowCutGap.EncodedEdgeGadget.threshold_transfer,
    `DirectedFlowCutGap.EncodedEdgeRounding.massBit_support_valid,
    `DirectedFlowCutGap.EncodedEdgeRounding.sizeBit_support_valid,
    `DirectedFlowCutGap.EncodedEdgeRounding.size_expected_uniform,
    `DirectedFlowCutGap.EncodedEdgeRounding.mass_expected_uniform,
    `DirectedFlowCutGap.EdgeLineReduction.distance_eq_arcWeight,
    `DirectedFlowCutGap.EncodedEdgeLineInput.feasible_lineInput,
    `DirectedFlowCutGap.EncodedEdgeLineInput.toEdges_cost,
    `DirectedFlowCutGap.EncodedEdgeSolver.mass_support_valid,
    `DirectedFlowCutGap.EncodedEdgeSolver.size_support_valid,
    `DirectedFlowCutGap.EncodedEdgeSolver.mass_expected_uniform,
    `DirectedFlowCutGap.EncodedEdgeSolver.size_expected_uniform,
    `DirectedFlowCutGap.EncodedEdgeSolver.polynomial_failure_le,
    `DirectedFlowCutGap.WeakDecomposition.edge_law_of_exact_weight_factor] do
    let some (.thmInfo _) := env.find? theoremName | throwError "Missing theorem {theoremName}"
    unless roots.contains theoremName do throwError "Unselected theorem {theoremName}"
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing dependency {name}"
      if info.isUnsafe || info.isPartial then throwError "Unsafe or partial proof dependency {name}"
      match info with
      | .axiomInfo _ =>
        unless allowed.contains name do throwError "Disallowed dependency axiom {name}"
      | _ => pure ()
      for dep in info.getUsedConstantsAsSet.toList do
        unless seen.contains dep do todo := todo.push dep
  IO.eprintln s!"PASS constructive logical audit modules={selected.size} declarations={declarations} roots={roots.size} closure={seen.toList.length} compiler_entries={compilerEntries} axioms={axioms.toList}"
