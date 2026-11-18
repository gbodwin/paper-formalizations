import DirectedFlowCutGap.MedianShortcuts
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option stderrAsMessages false
open Lean in
private def unnamedBinders (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun term => pure (.done (match term with
    | .lam _ type body info => .lam .anonymous type body info
    | .forallE _ type body info => .forallE .anonymous type body info
    | .letE _ type value body dependent => .letE .anonymous type value body dependent
    | rest => rest)))

open Lean in
run_cmd Elab.Command.liftTermElabM do
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
  let some (.defnInfo oldMatcher) := old.constants.find? (fun ci => ci.name == matcher) |
    throwError "Baseline matcher definition missing"
  let some (.defnInfo actualMatcher) := env.find? matcher | throwError "Replacement matcher definition missing"
  unless Expr.equal (← unnamedBinders oldMatcher.type) (← unnamedBinders actualMatcher.type) &&
      Expr.equal (← unnamedBinders oldMatcher.value) (← unnamedBinders actualMatcher.value) &&
      oldMatcher.levelParams == actualMatcher.levelParams && oldMatcher.hints == actualMatcher.hints do
    throwError "Changed matcher interface, body, universe parameters or reducibility hints"
  let some matcherInfo := Lean.Meta.getMatcherInfoCore? env matcher | throwError "Matcher metadata missing"
  unless matcherInfo.numParams == 1 && matcherInfo.numDiscrs == 1 &&
      matcherInfo.uElimPos? == some 1 && matcherInfo.getNumDiscrEqs == 0 &&
      matcherInfo.altInfos == #[⟨0, 0, true⟩, ⟨3, 0, false⟩] && matcherInfo.overlaps.isEmpty do
    throwError "Retained matcher metadata changed"
  for suffix in #[`vertices._f, `height._f, `Balanced._f, `edges._f] do
    let name := (target ++ `Tree) ++ suffix
    let some ci := env.find? name | throwError "Missing matcher consumer {name}"
    unless ci.getUsedConstantsAsSet.contains matcher do
      throwError "Did not reuse retained matcher in {name}"
    IO.eprintln s!"MATCHER_REUSE {name}"
  IO.eprintln "MATCHER exact except binder names, with matching universes and metadata"
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
      if let .thmInfo before := oldInfo then
        if before.type.getUsedConstantsAsSet.contains matcher then
          let .thmInfo after := current | throwError "Retained declaration is not a theorem {before.name}"
          unless Expr.equal (← unnamedBinders before.type) (← unnamedBinders after.type) &&
              Expr.equal (← unnamedBinders before.value) (← unnamedBinders after.value) do
            throwError "Retained theorem type or proof value changed for {before.name}"
          consumers := consumers + 1
          IO.eprintln s!"RETAINED theorem exact except binder names {before.name}"
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
