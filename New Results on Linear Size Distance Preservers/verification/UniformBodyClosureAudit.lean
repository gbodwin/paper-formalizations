import LinearDistancePreservers.UniformDimension
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option maxHeartbeats 4000000
#check @LinearDistancePreservers.TheoremFourGeneral.uniform_dimension_lower_bound
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let paper := match env.getModuleIdxFor? name with
      | some idx => match modules[idx.toNat]? with
        | some m => (`LinearDistancePreservers).isPrefixOf m
        | none => false
      | none => false
    if paper then
      count := count + 1
      if ci.isUnsafe then throwError "Unsafe paper declaration: {name}"
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do throwError "Forbidden axiom: {name}: {ax}"
  logInfo m!"AUTHOR_IMPORTED_PAPER_AUDIT declarations={count}"
  let roots : Array Name := #[`LinearDistancePreservers.TheoremFourGeneral.uniform_dimension_lower_bound]
  for root in roots do
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    let mut projectBodies : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name | throwError "Missing closure constant {name}"
        if ci.isUnsafe then throwError "Unsafe closure constant {root}: {name}"
        match ci with
        | .axiomInfo _ =>
          axioms := axioms.insert name
          unless allowed.contains name do throwError "Forbidden closure axiom {root}: {name}"
        | _ => pure ()
        let paper := match env.getModuleIdxFor? name with
          | some idx => match modules[idx.toNat]? with
            | some m => (`LinearDistancePreservers).isPrefixOf m
            | none => false
          | none => false
        if paper then projectBodies := projectBodies.insert name
        for dependency in ci.getUsedConstantsAsSet.toList do
          unless seen.contains dependency do todo := todo.push dependency
    logInfo m!"BODY_CLOSURE root={root} constants={seen.toList.length} paper={projectBodies.toList.length} axioms={axioms.toList}"
