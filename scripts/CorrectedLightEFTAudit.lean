import CorrectedLightEFTSpanners

/-! Source-derived actual-owner inventory and recursive type/body audit.
This is a verification program, never an imported mathematical premise.
The Python driver supplies the exact import closure and output directory. -/
open Lean in
run_cmd do
  let some expectedPath ← IO.getEnv "CORRECTED_LIGHT_EFT_MODULES"
    | throwError "Missing source-derived module inventory"
  let some outputPath ← IO.getEnv "CORRECTED_LIGHT_EFT_AUDIT_OUTPUT"
    | throwError "Missing audit output directory"
  let expectedText ← IO.FS.readFile expectedPath
  let expected := (expectedText.splitOn "\n" |>.filter (· != "")).toArray.map String.toName
  unless expected.size > 0 do throwError "Empty source-derived module inventory"
  let output : System.FilePath := outputPath
  IO.FS.createDirAll output
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  for m in expected do
    unless modules.contains m do throwError "Expected module was not imported: {m}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => modules[i.toNat]?.getD Name.anonymous
    | none => Name.anonymous
  let expectedSet := expected.foldl (fun s n => s.insert n) ({} : NameSet)
  let isProject := fun n => expectedSet.contains (owner n)
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
  let inventory ← IO.FS.Handle.mk (output / "actual-owner-inventory.tsv") .write
  inventory.putStr "owner\tname\tkind\tunsafe\tpartial\n"
  let mut issues : Array String := #[]
  for n in roots do
    let some c := env.find? n | throwError "Missing inventoried declaration {n}"
    inventory.putStr s!"{owner n}\t{n}\t{kind c}\t{c.isUnsafe}\t{c.isPartial}\n"
    if c.isUnsafe then issues := issues.push s!"project unsafe: {n}"
    if c.isPartial then issues := issues.push s!"project partial: {n}"
    if let .axiomInfo _ := c then issues := issues.push s!"project axiom: {n}"
  let mut visited : NameSet := {}
  let mut todo := roots.toList
  let mut queued := roots.foldl (fun s n => s.insert n) ({} : NameSet)
  let dependencies ← IO.FS.Handle.mk (output / "recursive-dependencies.tsv") .write
  dependencies.putStr "name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n"
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
    dependencies.putStr s!"{n}\t{owner n}\t{kind c}\t{fmt typeDeps}\t{fmt bodyDeps}\t{c.isUnsafe}\t{c.isPartial}\n"
    for d in typeDeps ++ bodyDeps do
      unless queued.contains d do
        queued := queued.insert d
        todo := d :: todo
    if visited.size % 10000 == 0 then
      IO.println s!"audit visited {visited.size} constants"
  inventory.flush
  dependencies.flush
  IO.FS.writeFile (output / "import-closure-loaded.txt")
    (String.intercalate "\n" (modules.toList.map toString) ++ "\n")
  IO.FS.writeFile (output / "strict-violations.txt")
    (String.intercalate "\n" issues.toList ++ if issues.isEmpty then "" else "\n")
  let result := Json.mkObj [
    ("project_modules",toJson expected.size),
    ("project_declarations",toJson roots.size),
    ("recursive_constants",toJson visited.size),
    ("opaque_bodies",toJson opaqueCount),
    ("allowed_axioms",toJson (allowed.map toString)),
    ("observed_axioms",toJson (axioms.toArray.map toString)),
    ("findings",toJson issues.size)]
  IO.FS.writeFile (output / "summary.json") (result.pretty ++ "\n")
  logInfo m!"{result.compress}"
  unless issues.isEmpty do throwError "Strict audit rejected {issues.size} findings"
