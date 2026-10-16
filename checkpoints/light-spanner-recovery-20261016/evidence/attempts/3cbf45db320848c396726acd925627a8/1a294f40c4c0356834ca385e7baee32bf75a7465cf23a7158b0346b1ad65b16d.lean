import LightSpanners

/-! Exhaustive actual-owner inventory and recursive type/body audit.
Does not use cached collectAxioms results. Imported opaque values are traversed.
This is verification code, not a mathematical premise. -/
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  let newModules : Array Name := #[`LightSpanners.Basic, `LightSpanners.BridgeWords, `LightSpanners.BucketBudgets, `LightSpanners.BucketCycles, `LightSpanners.BucketDispersion, `LightSpanners.BucketPadding, `LightSpanners.BucketPaths, `LightSpanners.BucketPrefix, `LightSpanners.BucketRestriction, `LightSpanners.BucketUniqueness, `LightSpanners.ChordPrefix, `LightSpanners.ChordWords, `LightSpanners.Construction, `LightSpanners.CopyWeights, `LightSpanners.Counting, `LightSpanners.CycleBalance, `LightSpanners.CycleOrder, `LightSpanners.CycleProjection, `LightSpanners.CycleReduction, `LightSpanners.CycleSegments, `LightSpanners.Distance, `LightSpanners.DyadicEnumeration, `LightSpanners.EdgeSubdivision, `LightSpanners.EndpointCounting, `LightSpanners.EndpointSampling, `LightSpanners.EpsilonDomain, `LightSpanners.FiniteSampling, `LightSpanners.Girth, `LightSpanners.Greedy, `LightSpanners.HikerCompletion, `LightSpanners.HikerDay, `LightSpanners.HikerLayers, `LightSpanners.HikerSquads, `LightSpanners.HikerTour, `LightSpanners.Kruskal, `LightSpanners.LightnessBound, `LightSpanners.MainTheorem, `LightSpanners.MediumCounting, `LightSpanners.MinimumTree, `LightSpanners.MonotonePadding, `LightSpanners.PaddingPositions, `LightSpanners.RetainedGraph, `LightSpanners.RoundingTree, `LightSpanners.SamplingCounting, `LightSpanners.Subdivision, `LightSpanners.SubdivisionCycles, `LightSpanners.SubdivisionGirth, `LightSpanners.SubdivisionTree, `LightSpanners.TourCycle, `LightSpanners.TreeCycle, `LightSpanners.TreeReduction, `LightSpanners.TreeTour, `LightSpanners.UnitCycle, `LightSpanners.UnitCycleWeight, `LightSpanners.UsefulFamily, `LightSpanners.VertexCopies, `LightSpanners.WeakCounting, `LightSpanners.Weight, `LightSpanners.WeightExtension]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => modules[i.toNat]?.getD Name.anonymous
    | none => Name.anonymous
  let isProject := fun n => (`LightSpanners).isPrefixOf (owner n)
  let roots := (env.constants.toList.filter fun (n, _) => isProject n).map Prod.fst
    |>.toArray.qsort Name.lt
  let kind := fun c => match c with
    | ConstantInfo.axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  let mut inventory := "owner\tname\tkind\tunsafe\n"
  let mut newCount : Nat := 0
  for n in roots do
    let some c := env.find? n | throwError "Missing inventoried declaration {n}"
    inventory := inventory ++ s!"{owner n}\t{n}\t{kind c}\t{c.isUnsafe}\n"
    if newModules.contains (owner n) then
      newCount := newCount + 1
      if c.isUnsafe then throwError "Unsafe new declaration {n}"
      if c.isPartial then throwError "Partial new declaration {n}"
      if let .axiomInfo _ := c then throwError "New axiom {n}"
  for m in newModules do
    unless roots.any (fun n => owner n == m) do
      throwError "No actual-owner declarations found for {m}"
  let mut visited : NameSet := {}
  let mut todo := roots.toList
  let mut dependencies := "name\towner\tkind\ttypeDependencies\tbodyDependencies\n"
  let mut axioms : NameSet := {}
  let mut opaqueCount : Nat := 0
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if visited.contains n then continue
    visited := visited.insert n
    let some c := env.find? n | throwError "Unresolved recursive dependency {n}"
    if c.isUnsafe then throwError "Unsafe recursive dependency {n}"
    if c.isPartial then throwError "Partial recursive dependency {n}"
    if let .axiomInfo _ := c then
      unless allowed.contains n do throwError "Disallowed axiom {n}"
      axioms := axioms.insert n
    let typeDeps := c.type.getUsedConstants
    let bodyDeps := match c with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    if let .opaqueInfo _ := c then opaqueCount := opaqueCount + 1
    let fmt := fun (ns : Array Name) => String.intercalate "," (ns.toList.map toString)
    dependencies := dependencies ++ s!"{n}\t{owner n}\t{kind c}\t{fmt typeDeps}\t{fmt bodyDeps}\n"
    todo := typeDeps.toList ++ bodyDeps.toList ++ todo
  IO.FS.writeFile "checkpoints/light-spanner-recovery-20261016/evidence/actual-owner-inventory.tsv" inventory
  IO.FS.writeFile "checkpoints/light-spanner-recovery-20261016/evidence/recursive-dependencies.tsv" dependencies
  IO.FS.writeFile "checkpoints/light-spanner-recovery-20261016/evidence/import-closure-loaded.txt"
    (String.intercalate "\n" (modules.toList.map toString) ++ "\n")
  logInfo m!"PASS: {roots.size} actual-owner project declarations, {newCount} covered declarations; {visited.size} recursively visited constants, {opaqueCount} opaque bodies; axioms {axioms.toArray}"
