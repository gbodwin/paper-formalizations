import DirectedFlowCutGap.MedianShortcuts
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option stderrAsMessages false
open Lean in
run_cmd do
  let env ← getEnv
  let target := `DirectedFlowCutGap.MedianShortcuts
  let matcher := `DirectedFlowCutGap.MedianShortcuts.Tree.vertices.match_1
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut roots : Array Name := #[]
  let mut axioms : NameSet := {}
  for (name, ci) in env.constants.toList do
    if (env.getModuleIdxFor? name).bind (fun i => env.allImportedModuleNames[i.toNat]?) == some target then
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial declaration {name}"
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
        axioms := axioms.insert ax
      roots := roots.push name
  unless roots.size > 0 do throwError "No declarations audited"
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut edges := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let some ci := env.find? name | throwError "Unknown dependency {name}"
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial dependency {name}"
      match ci with
      | .axiomInfo _ => unless allowed.contains name do throwError "Disallowed axiom {name}"
      | _ => pure ()
      let dependencies := ci.getUsedConstantsAsSet.toList
      edges := edges + dependencies.length
      for dep in dependencies do
        unless seen.contains dep do todo := todo.push dep
  let some basePath ← IO.getEnv "FLOW_MEDIAN_BASE_OBJECT" |
    throwError "FLOW_MEDIAN_BASE_OBJECT must name a strictly compiled public baseline object"
  let (old, _region) ← Lean.readModuleData basePath
  let some oldMatcher := old.constants.find? (fun ci => ci.name == matcher) | throwError "Baseline matcher missing"
  let some actualMatcher := env.find? matcher | throwError "Replacement matcher missing"
  unless oldMatcher.type == actualMatcher.type && oldMatcher.value? == actualMatcher.value? &&
      oldMatcher.levelParams == actualMatcher.levelParams do
    throwError "Matcher type, value or universe parameters changed"
  let some matcherInfo := Lean.Meta.getMatcherInfoCore? env matcher | throwError "Matcher metadata missing"
  unless matcherInfo.numParams == 1 && matcherInfo.numDiscrs == 1 &&
      matcherInfo.uElimPos? == some 1 && matcherInfo.getNumDiscrEqs == 0 &&
      matcherInfo.altInfos == #[⟨0, 0, true⟩, ⟨3, 0, false⟩] && matcherInfo.overlaps.isEmpty do
    throwError "Retained matcher metadata changed"
  IO.eprintln "MATCHER exact type, value, universe parameters, and metadata"
  let (currentModule, _currentRegion) ← Lean.readModuleData (← Lean.findOLean target)
  let compilerEntries := currentModule.extraConstNames.filter fun name => !(env.constants.contains name)
  IO.eprintln s!"COMPILER_ONLY entries={compilerEntries.size} names={compilerEntries}"
  let mut consumers := 0
  let mut retainedTypes := 0
  for oldInfo in old.constants do
    if !oldInfo.isPartial then
      -- Generated subproofs can change shape independently of their enclosing
      -- theorem. They still participate in the current type-and-body audit.
      let name := oldInfo.name.toString
      if name.contains "._simp_" || name.contains "._proof_" then continue
      let some current := env.find? oldInfo.name | throwError "Missing declaration {oldInfo.name}"
      unless oldInfo.type == current.type && oldInfo.levelParams == current.levelParams do
        throwError "Changed retained type or universe parameters for {oldInfo.name}"
      retainedTypes := retainedTypes + 1
      if oldInfo.isTheorem && oldInfo.type.getUsedConstantsAsSet.contains matcher then
        unless current.isTheorem && current.value? == oldInfo.value? do
          throwError "Retained theorem kind or value changed for {oldInfo.name}"
        consumers := consumers + 1
        IO.eprintln s!"RETAINED exact theorem {oldInfo.name}"
  unless consumers == 5 do throwError "Expected all five retained matcher-consumer theorems"
  IO.eprintln s!"PASS median audit roots={roots.size} closure={seen.toList.length} edges={edges} axioms={axioms.toList} retained_types={retainedTypes} retained_theorems={consumers}"

#eval do
  let t : DirectedFlowCutGap.MedianShortcuts.Tree Nat := .node (.node .empty 1 .empty) 2 (.node .empty 3 .empty)
  let emptyTree : DirectedFlowCutGap.MedianShortcuts.Tree Nat := .empty
  let skewed := DirectedFlowCutGap.MedianShortcuts.Tree.node t 4 .empty
  if emptyTree.vertices != [] || emptyTree.height != 0 || t.vertices != [1, 2, 3] || t.height != 2 ||
      skewed.vertices != [1, 2, 3, 4] || skewed.height != 3 then
    throw <| IO.userError "Median implementation fixture failed"
  IO.println "PASS compiled inorder traversal and height"
