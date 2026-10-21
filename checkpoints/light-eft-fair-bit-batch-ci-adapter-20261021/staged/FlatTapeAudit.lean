import Lean
import LightEFTFlatTapeStage.FlatTapeLaw

/- Verification helper only. No declaration in this namespace is a paper premise.
Keys contain fresh scalar bytes, never borrowed Names/Strings from loaded parts.
Only regions explicitly returned by this helper's reads are ever freed.
-/
namespace LightEFTAuditCollision
open Lean

private partial def appendNat (out : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then out.push (UInt8.ofNat n)
  else appendNat (out.push (UInt8.ofNat (n % 128 + 128))) (n / 128)

private partial def appendName (out : ByteArray) (name : Name) : ByteArray :=
  match name with
  | .anonymous => out.push 0
  | .str pre text =>
    let out := (appendName out pre).push 1
    let bytes := text.toUTF8
    bytes.foldl (fun dst byte => dst.push byte) (appendNat out bytes.size)
  | .num pre number => appendNat ((appendName out pre).push 2) number

@[noinline] def ownedKey (name : Name) : ByteArray :=
  appendName (ByteArray.emptyWithCapacity 64) name

private def hexKey (key : ByteArray) : String :=
  let digits := "0123456789abcdef".toList.toArray
  key.foldl (fun text byte => (text.push digits[byte.toNat / 16]!).push digits[byte.toNat % 16]!) ""

def marker (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn text
  out.flush

/- Only fresh keys and scalar locations escape a reader frame. Locations refer
to the pre-existing environment's selected ModuleData, whose regions remain
owned by that environment for the entire scan. No newly read ConstantInfo,
Expr, Name, String or ModuleData is retained by State. -/
structure Location where
  owner : Nat
  slot : Nat

structure RawClaim where
  owner : Nat
  auxiliary : Bool

structure State where
  claims : Std.HashMap ByteArray RawClaim := {}
  declarations : Std.HashMap ByteArray Location := {}
  issues : Array String := #[]
  modules : Nat := 0
  constNames : Nat := 0
  extraConstNames : Nat := 0
  parts : Nat := 0
  freed : Nat := 0
  peakRegions : Nat := 0
  repetitions : Nat := 0
  collisions : Nat := 0
  metadataOverlaps : Nat := 0
  auxiliaryOverlaps : Nat := 0
  actualDeclarations : Nat := 0
  actualNames : Nat := 0
  duplicateDeclarations : Nat := 0
  compatible : Nat := 0
  incompatible : Nat := 0
  unclassified : Nat := 0

/- Same predicate as the pinned Environment.subsumesInfo. Expr BEq is Lean's
alpha-equivalence (not definitional equality); proof values are intentionally
absent from this theorem-compatibility rule. No name-pattern exceptions. -/
def isPropCheap (lookup : Name → Option ConstantInfo) (ty : Expr) : Bool := Id.run do
  let mut body := ty
  while body.isForall do
    let .forallE (body := next) .. := body | return false
    body := next
  let .const name .. := body.getAppFn | return false
  let some decl := lookup name | return false
  let mut result := decl.type
  for _ in 0...body.getAppNumArgs do
    let .forallE (body := next) .. := result | return false
    result := next
  return result.isProp

def subsumesInfo (lookup : Name → Option ConstantInfo) (new prior : ConstantInfo) : Bool :=
  new.name == prior.name && new.type == prior.type &&
    new.levelParams == prior.levelParams &&
    match new, prior with
    | .thmInfo a, .thmInfo b => a.all == b.all
    | .thmInfo a, .axiomInfo b => a.all == [b.name] && !b.isUnsafe
    | .axiomInfo a, .axiomInfo b =>
      a.isUnsafe == b.isUnsafe && isPropCheap lookup a.type
    | _, _ => false

private def infoAt (data : Array ModuleData) (loc : Location) : Option ConstantInfo := do
  let mod ← data[loc.owner]?
  mod.constants[loc.slot]?

private def lookupDeclaration (data : Array ModuleData) (state : State)
    (name : Name) : Option ConstantInfo := do
  let loc ← state.declarations.get? (ownedKey name)
  infoAt data loc

private def unclassified (state : State) (owner : Nat) (scope : String) : IO State := do
  marker s!"COLLISION-UNCLASSIFIED: {state.unclassified} owner={owner} scope={scope}"
  return { state with
    unclassified := state.unclassified + 1
    issues := state.issues.push s!"unclassified collision metadata: owner={owner} scope={scope}" }

private structure OwnedParts where
  data : IO.Ref (Array ModuleData)
  regions : IO.Ref (Array CompactedRegion)

@[noinline] private unsafe def readPart (parts : OwnedParts) (file : System.FilePath) : IO Unit := do
  let dependencies ← parts.regions.get
  let part ← CompactedRegion.read (α := ModuleData) file dependencies
  parts.regions.modify (·.push part.2)
  parts.data.modify (·.push part.1)
  -- part/dependencies do not escape this call; only the two cells own them.

@[noinline] private def usesParts (parts : OwnedParts) : IO Bool := do
  return (← parts.data.get)[0]!.isModule

@[noinline] private unsafe def loadParts (parts : OwnedParts) (file : System.FilePath) : IO Unit := do
  readPart parts file
  if ← usesParts parts then
    readPart parts (OLeanLevel.server.adjustFileName file)
    readPart parts (OLeanLevel.private.adjustFileName file)

private def addClaim (state : State) (owner : Nat) (key : ByteArray)
    (auxiliary : Bool) : IO State := do
  if let some prior := state.claims.get? key then
    if prior.owner == owner then
      return { state with repetitions := state.repetitions + 1 }
    else
      let category := if auxiliary || prior.auxiliary then "auxiliary-ownership" else "constant-name-metadata"
      marker s!"COLLISION-CLAIM: {state.collisions} key={hexKey key} prior={prior.owner} owner={owner} class={category}"
      return { state with
        collisions := state.collisions + 1
        metadataOverlaps := state.metadataOverlaps + (if auxiliary || prior.auxiliary then 0 else 1)
        auxiliaryOverlaps := state.auxiliaryOverlaps + (if auxiliary || prior.auxiliary then 1 else 0) }
  else
    return { state with claims := state.claims.insert key { owner, auxiliary } }

@[noinline] private def consumeNames (parts : OwnedParts) (owner : Nat) (initial : State) : IO State := do
  let data ← parts.data.get
  let mut state := initial
  for part in data do
    if part.constNames.size != part.constants.size then
      state ← unclassified state owner "raw-shape"
    for slot in [:part.constants.size] do
      if part.constNames[slot]? != some part.constants[slot]!.name then
        state ← unclassified state owner "raw-name"
    for name in part.constNames do
      state ← addClaim state owner (ownedKey name) false
      state := { state with constNames := state.constNames + 1 }
    for name in part.extraConstNames do
      state ← addClaim state owner (ownedKey name) true
      state := { state with extraConstNames := state.extraConstNames + 1 }
  return state
  -- Only independently allocated keys, scalar counts/owners and strings built
  -- from them escape. Reader frames return before data clearing or release.

@[noinline] private def consumeDeclarations (data : Array ModuleData) (owner : Nat)
    (initial : State) : IO State := do
  let some mod := data[owner]? | return ← unclassified initial owner "module-count"
  let mut state := initial
  if mod.constNames.size != mod.constants.size then
    state ← unclassified state owner "effective-shape"
  state := { state with actualNames := state.actualNames + mod.constNames.size }
  for slot in [:mod.constants.size] do
    let info := mod.constants[slot]!
    state := { state with actualDeclarations := state.actualDeclarations + 1 }
    if mod.constNames[slot]? != some info.name then
      state ← unclassified state owner "effective-name"
    let freshKey := ownedKey info.name
    let key := (state.claims.getKey? freshKey).getD freshKey
    if let some loc := state.declarations.get? key then
      let some prior := infoAt data loc |
        state ← unclassified state owner "location"
        continue
      -- Just as finalizeImport, duplicate processing sees the old map; update
      -- only if the new representation subsumes the previous representative.
      let lookup := lookupDeclaration data state
      let replace := subsumesInfo lookup info prior
      let retain := if replace then false else subsumesInfo lookup prior info
      let result := if replace then "compatible-update" else if retain then "compatible-retain" else "incompatible"
      marker s!"COLLISION-DECL: {state.duplicateDeclarations} key={hexKey key} prior={loc.owner} owner={owner} result={result}"
      state := { state with duplicateDeclarations := state.duplicateDeclarations + 1 }
      if replace || retain then
        state := { state with compatible := state.compatible + 1 }
        if replace then
          state := { state with declarations := state.declarations.insert key { owner, slot } }
      else
        state := { state with
          incompatible := state.incompatible + 1
          issues := state.issues.push s!"incompatible imported declaration: key={hexKey key} module indices {loc.owner}, {owner}" }
    else
      state := { state with declarations := state.declarations.insert key { owner, slot } }
  return state
  -- ConstantInfo/Expr/Name values here belong to the still-live input
  -- environment, not newly read parts. Only owned keys and Nat locations escape.

@[noinline] private def countRegions (parts : OwnedParts) : IO Nat := do
  return (← parts.regions.get).size

@[noinline] private def discardData (parts : OwnedParts) : IO Unit :=
  parts.data.set #[]

@[noinline] private def takeLast (regions : IO.Ref (Array CompactedRegion)) : IO (Option CompactedRegion) :=
  regions.modifyGet fun stack =>
    match stack.back? with
    | none => (none, stack)
    | some region => (some region, stack.pop)

@[noinline] private unsafe def freeLast (regions : IO.Ref (Array CompactedRegion)) : IO Bool := do
  match ← takeLast regions with
  | none => return false
  | some region =>
    region.free
    return true

@[noinline] private unsafe def releaseParts (parts : OwnedParts) : IO Nat := do
  discardData parts
  -- All data-reader frames have returned. Pop removes the region handle from
  -- the owning cell before free: private, server, main (reverse dependencies).
  let mut freed := 0
  while (← freeLast parts.regions) do
    freed := freed + 1
  return freed

@[noinline] private unsafe def scanOne (data : Array ModuleData)
    (owner : Nat) (file : System.FilePath) (initial : State) : IO State := do
  let parts : OwnedParts := { data := (← IO.mkRef #[]), regions := (← IO.mkRef #[]) }
  let beforeConst := initial.constNames
  let beforeExtra := initial.extraConstNames
  let beforeActual := initial.actualDeclarations
  let beforeNames := initial.actualNames
  let beforeDuplicates := initial.duplicateDeclarations
  let beforeCompatible := initial.compatible
  let beforeIncompatible := initial.incompatible
  let beforeUnclassified := initial.unclassified
  let result : Except IO.Error State ← try
    loadParts parts file
    let state ← consumeNames parts owner initial
    pure (.ok (← consumeDeclarations data owner state))
  catch error => pure (.error error)
  let read ← countRegions parts
  let freed ← releaseParts parts
  unless read == freed do throw <| IO.userError "Owned collision regions were not all freed"
  match result with
  | .error error =>
    marker s!"AUDIT-PHASE: collision-incomplete index={owner} parts-read={read} regions-freed={freed}"
    throw error
  | .ok state =>
    let constCount := state.constNames - beforeConst
    let extraCount := state.extraConstNames - beforeExtra
    marker s!"COLLISION-MODULE: {owner} {read} parts, {constCount} constNames, {extraCount} extraConstNames, {freed} regions freed"
    marker s!"COLLISION-ACTUAL: {owner} {state.actualDeclarations - beforeActual} declarations, {state.actualNames - beforeNames} constNames, {state.duplicateDeclarations - beforeDuplicates} duplicates, {state.compatible - beforeCompatible} compatible, {state.incompatible - beforeIncompatible} incompatible, {state.unclassified - beforeUnclassified} unclassified"
    return { state with
      modules := state.modules + 1
      parts := state.parts + read
      freed := state.freed + freed
      peakRegions := max state.peakRegions read }

structure Report where
  issues : Array String

@[noinline] unsafe def scan (env : Environment) : IO Report := do
  let modules := env.allImportedModuleNames
  let data := env.header.moduleData
  marker s!"AUDIT-PHASE: collision-start modules={modules.size}"
  let mut state : State := {}
  if data.size != modules.size then
    state ← unclassified state 0 "module-count"
  for index in [:modules.size] do
    state ← scanOne data index (← findOLean modules[index]!) state
  let count := state.constNames + state.extraConstNames
  marker s!"COLLISION-COVERAGE: {state.modules} modules, {count} declarations/extra-name claims, {state.parts} parts read, {state.freed} regions freed, {state.peakRegions} peak owned regions, {state.claims.size} independent keys, {state.constNames} constNames, {state.extraConstNames} extraConstNames, {state.repetitions} same-module repetitions, {state.collisions} cross-module collisions"
  marker s!"COLLISION-CLASSIFICATION: {state.metadataOverlaps} constant-name metadata overlaps, {state.auxiliaryOverlaps} auxiliary ownership overlaps, {state.actualDeclarations} effective declarations, {state.actualNames} effective constNames, {state.duplicateDeclarations} duplicate declarations, {state.compatible} compatible, {state.incompatible} incompatible, {state.unclassified} unclassified, {state.declarations.size} effective keys"
  return { issues := state.issues }
  -- The original imported environment stays alive throughout this call. Its
  -- regions are never freed here. Only independently owned scan state is dropped.

end LightEFTAuditCollision


/- Unexecuted focused audit draft. Reuses the accepted recursive traversal.
Inventories every declaration owned by the new module, then follows all types,
definition/theorem/opaque bodies and inductive/recursor links into imports. -/
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  let collisionReport ← LightEFTAuditCollision.scan env
  let target := "LightEFTFlatTapeStage.FlatTapeLaw".toName
  unless modules.contains target do throwError "Missing new target module"
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => modules[i.toNat]?.getD Name.anonymous
    | none => Name.anonymous
  let roots := (env.constants.toList.filter fun (n, _) => owner n == target).map Prod.fst
    |>.toArray.qsort Name.lt
  unless !roots.isEmpty do throwError "No actual-owner corollary declarations"
  let requiredRoots : Array Name := #["LightEFTSpanners.FlatTape.tapeLength_eq".toName, "LightEFTSpanners.FlatTape.coordinateEquiv_apply".toName, "LightEFTSpanners.FlatTape.distinct_occurrence_indices".toName, "LightEFTSpanners.FlatTape.tapeEquiv_apply".toName, "LightEFTSpanners.FlatTape.tapeEquiv_at_position".toName, "LightEFTSpanners.FlatTape.idealTapeLaw_mass".toName, "LightEFTSpanners.FlatTape.tape_mass_eq_joint_mass".toName, "LightEFTSpanners.FlatTape.tape_event_probability".toName, "LightEFTSpanners.FlatTape.tape_joint_law".toName, "LightEFTSpanners.FlatTape.tape_supplied_assignment_probability".toName]
  for n in requiredRoots do
    unless roots.contains n do throwError "Missing canonical actual-output root {n}"
    let some (.thmInfo _) := env.find? n | throwError "Required corollary root is not a theorem: {n}"
    pure ()
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
  let mut issues : Array String := collisionReport.issues
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
  let required : Array Name := #["LightEFTSpanners.PaidFlagSerialization.execute_eq".toName, "LightEFTSpanners.PaidFlagSampleComposition.full_trace".toName, "LightEFTSpanners.PaidFlagSampleComposition.execute_eq".toName, "LightEFTSpanners.StoredFlagSample.execute_encoded".toName, "LightEFTSpanners.StoredFlagSample.typed_edgeSet".toName, "LightEFTSpanners.JointFlagSampling.decoded_assignment_probability".toName]
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
