import LightEFTJointFlagSamplingStage.JointAssignmentLaw

/- Unexecuted focused audit draft. Reuses the accepted recursive traversal.
Inventories every declaration owned by the new module, then follows all types,
definition/theorem/opaque bodies and inductive/recursor links into imports. -/
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  let target := "LightEFTJointFlagSamplingStage.JointAssignmentLaw".toName
  unless modules.contains target do throwError "Missing new target module"
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => modules[i.toNat]?.getD Name.anonymous
    | none => Name.anonymous
  let roots := (env.constants.toList.filter fun (n, _) => owner n == target).map Prod.fst
    |>.toArray.qsort Name.lt
  unless roots.contains ("LightEFTSpanners.JointFlagSampling.decoded_assignment_probability".toName) do
    throwError "Missing joint assignment probability theorem"
  let requiredRoots : Array Name := #["LightEFTSpanners.JointFlagSampling.Transport.mass_ext".toName, "LightEFTSpanners.JointFlagSampling.Transport.eq_of_prob_eq".toName, "LightEFTSpanners.JointFlagSampling.Transport.product_map".toName, "LightEFTSpanners.JointFlagSampling.Transport.batch_eq_product".toName, "LightEFTSpanners.JointFlagSampling.Transport.fin_cons_probability".toName, "LightEFTSpanners.JointFlagSampling.samplingSchedule_nodup".toName, "LightEFTSpanners.JointFlagSampling.mem_samplingSchedule".toName, "LightEFTSpanners.JointFlagSampling.samplingSchedule_length".toName, "LightEFTSpanners.JointFlagSampling.jointSourceLaw_mass".toName, "LightEFTSpanners.JointFlagSampling.decodeHost_typed".toName, "LightEFTSpanners.JointFlagSampling.decodeAssignment_head".toName, "LightEFTSpanners.JointFlagSampling.decodeAssignment_outside".toName, "LightEFTSpanners.JointFlagSampling.batch_decode_law".toName, "LightEFTSpanners.JointFlagSampling.host_decode_law".toName, "LightEFTSpanners.JointFlagSampling.decoded_assignment_probability".toName, "LightEFTSpanners.JointFlagSampling.decoded_assignment_law".toName]
  for n in requiredRoots do
    unless roots.contains n do throwError "Missing joint-law root {n}"
  -- Private helper names are generated; discover their actual owner names.
  let helperUserName := "LightEFTSpanners.JointFlagSampling.retainInstanceArguments".toName
  let helperRoots := roots.filter (fun n => privateToUserName n == helperUserName)
  unless helperRoots.size == 1 do
    throwError "Expected exactly one private retainInstanceArguments actual-owner root"
  let helperName := helperRoots[0]!
  unless isPrivateName helperName do
    throwError "retainInstanceArguments must remain private"
  let some (.thmInfo _) := env.find? helperName |
    throwError "retainInstanceArguments must be a theorem"
  let kind := fun c => match c with
    | ConstantInfo.axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  let mut inventory := "owner\tname\tkind\tunsafe\tpartial\n"
  let mut issues : Array String := #[]
  for n in roots do
    let some c := env.find? n | throwError "Missing inventoried declaration {n}"
    inventory := inventory ++ s!"{owner n}\t{n}\t{kind c}\t{c.isUnsafe}\t{c.isPartial}\n"
    if c.isUnsafe then issues := issues.push s!"root unsafe: {n}"
    if c.isPartial then issues := issues.push s!"root partial: {n}"
    if let .axiomInfo _ := c then issues := issues.push s!"root axiom: {n}"
  let mut visited : NameSet := {}
  let mut todo := roots.toList
  let mut dependencies := "name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n"
  let mut axioms : NameSet := {}
  let mut opaqueCount : Nat := 0
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if visited.contains n then continue
    visited := visited.insert n
    let some c := env.find? n | throwError "Unresolved recursive dependency {n}"
    if c.isUnsafe then issues := issues.push s!"recursive unsafe: {n}"
    if c.isPartial then issues := issues.push s!"recursive partial: {n}"
    if let .axiomInfo _ := c then
      unless allowed.contains n do issues := issues.push s!"recursive disallowed axiom: {n}"
      axioms := axioms.insert n
    let typeDeps := c.type.getUsedConstants
    let bodyDeps := match c with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | .inductInfo v => (v.all ++ v.ctors).toArray
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.rules.foldl (fun acc r => (acc.push r.ctor) ++ r.rhs.getUsedConstants) v.all.toArray
      | _ => #[]
    if let .opaqueInfo _ := c then opaqueCount := opaqueCount + 1
    let fmt := fun (ns : Array Name) => String.intercalate "," (ns.toList.map toString)
    dependencies := dependencies ++ s!"{n}\t{owner n}\t{kind c}\t{fmt typeDeps}\t{fmt bodyDeps}\t{c.isUnsafe}\t{c.isPartial}\n"
    todo := typeDeps.toList ++ bodyDeps.toList ++ todo
  -- Require the exact reviewed deterministic and probability interfaces.
  let required : Array Name := #["LightEFTSpanners.StoredFlagBatch.original_probability".toName, "LightEFTSpanners.StoredFlagSample.typed_edgeSet".toName, "LightEFTSpanners.FiniteProbability.productLaw".toName, "LightEFTSpanners.FiniteProbability.productLaw_measure".toName, "LightEFTSpanners.FiniteProbability.Law.prob_map".toName, "LightEFTSpanners.FiniteProbability.Law.prob_bind".toName, "LightEFTSpanners.SampledGreedy.freshBatchLaw".toName, "LightEFTSpanners.SampledGreedy.executionLaw".toName]
  for n in required do
    unless visited.contains n do issues := issues.push s!"Missing required reachable interface: {n}"
  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory
  IO.FS.writeFile "ci-evidence/recursive-dependencies.tsv" dependencies
  IO.FS.writeFile "ci-evidence/import-closure-loaded.txt"
    (String.intercalate "\n" (modules.toList.map toString) ++ "\n")
  IO.FS.writeFile "ci-evidence/strict-violations.txt"
    (String.intercalate "\n" issues.toList ++ "\n")
  if !issues.isEmpty then throwError "Strict focused audit rejected {issues.size} findings"
  logInfo m!"PASS: {roots.size} new-module actual-owner declarations; {visited.size} recursive constants, {opaqueCount} opaque bodies; axioms {axioms.toArray}"
