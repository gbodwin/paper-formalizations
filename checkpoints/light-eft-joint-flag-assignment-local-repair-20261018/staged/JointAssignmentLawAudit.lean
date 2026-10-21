import Lean
import LightEFTJointFlagSamplingStage.JointAssignmentLaw

section LightEFTAuditDiagnosticChannel
set_option stderrAsMessages false

/- Diagnostic only: fixed labels and a monotonic-millisecond clock modulo2^64.
No imported names, paths, expressions, payloads or environment variables are logged.
Each marker is flushed; all existing limits/checks and four exports are unchanged. -/
open Lean in
run_cmd do
  let now := (← IO.monoMsNow) % 18446744073709551616
  let out ← IO.getStderr
  out.putStrLn s!"AUDIT-TIMING: phase=frontend-ready mono-ms-mod64={now}"
  out.flush

namespace LightEFTAuditTiming
def mark (phase : String) : IO Unit := do
  let now := (← IO.monoMsNow) % 18446744073709551616
  let out ← IO.getStderr
  out.putStrLn s!"AUDIT-TIMING: phase={phase} mono-ms-mod64={now}"
  out.flush
end LightEFTAuditTiming

open Lean in
run_cmd do
  LightEFTAuditTiming.mark "timing-helper-ready"

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

open Lean in
run_cmd do
  LightEFTAuditTiming.mark "scan-helper-ready"


/- Serialization-only memoization. Keys are full imported-environment Names,
not their display strings. The imported environment stays alive for this entire
run_cmd; no Name from collision-reader-owned regions enters this cache. -/
namespace LightEFTAuditText
open Lean

abbrev Cache := Std.HashMap Name String

@[inline] def renderName (cache : Cache) (name : Name) : String × Cache :=
  match cache.get? name with
  | some text => (text, cache)
  | none =>
    let text := toString name
    (text, cache.insert name text)

def renderNames (initial : Cache) (names : Array Name) : String × Cache := Id.run do
  let mut cache := initial
  let mut texts : Array String := #[]
  for name in names do
    let (text, next) := renderName cache name
    cache := next
    texts := texts.push text
  return (String.intercalate "," texts.toList, cache)

end LightEFTAuditText

open Lean in
run_cmd do
  LightEFTAuditTiming.mark "serialization-helper-ready"

/- Unexecuted focused audit draft. Reuses the accepted recursive traversal.
Inventories every declaration owned by the new module, then follows all types,
definition/theorem/opaque bodies and inductive/recursor links into imports. -/
open Lean in
run_cmd do
  LightEFTAuditTiming.mark "audit-run-start"
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  LightEFTAuditTiming.mark "environment-ready"
  let collisionReport ← LightEFTAuditCollision.scan env
  LightEFTAuditTiming.mark "scan-complete"
  let target := "LightEFTJointFlagSamplingStage.JointAssignmentLaw".toName
  unless modules.contains target do throwError "Missing new target module"
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let owner := fun n => match env.getModuleIdxFor? n with
    | some i => modules[i.toNat]?.getD Name.anonymous
    | none => Name.anonymous
  let roots := (env.constants.toList.filter fun (n, _) => owner n == target).map Prod.fst
    |>.toArray.qsort Name.lt
  unless roots.size == 43 do
    throwError "Expected exactly 43 actual-owner declarations, got {roots.size}"
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
  LightEFTAuditTiming.mark "roots-complete"
  let mut textCache : LightEFTAuditText.Cache := {}
  let mut inventory := "owner\tname\tkind\tunsafe\tpartial\n"
  let mut issues : Array String := collisionReport.issues
  for n in roots do
    let some c := env.find? n | throwError "Missing inventoried declaration {n}"
    let (ownerText, afterOwner) := LightEFTAuditText.renderName textCache (owner n)
    let (nameText, afterName) := LightEFTAuditText.renderName afterOwner n
    textCache := afterName
    inventory := inventory ++ s!"{ownerText}\t{nameText}\t{kind c}\t{c.isUnsafe}\t{c.isPartial}\n"
    if c.isUnsafe then issues := issues.push s!"root unsafe: {n}"
    if c.isPartial then issues := issues.push s!"root partial: {n}"
    if let .axiomInfo _ := c then issues := issues.push s!"root axiom: {n}"
  LightEFTAuditTiming.mark "inventory-complete"
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
    let (nameText, afterName) := LightEFTAuditText.renderName textCache n
    let (ownerText, afterOwner) := LightEFTAuditText.renderName afterName (owner n)
    let (typeText, afterType) := LightEFTAuditText.renderNames afterOwner typeDeps
    let (bodyText, afterBody) := LightEFTAuditText.renderNames afterType bodyDeps
    textCache := afterBody
    dependencies := dependencies ++ s!"{nameText}\t{ownerText}\t{kind c}\t{typeText}\t{bodyText}\t{c.isUnsafe}\t{c.isPartial}\n"
    todo := typeDeps.toList ++ bodyDeps.toList ++ todo
  LightEFTAuditTiming.mark "recursive-complete"
  -- Require the exact reviewed deterministic and probability interfaces.
  let required : Array Name := #["LightEFTSpanners.StoredFlagBatch.original_probability".toName, "LightEFTSpanners.StoredFlagSample.typed_edgeSet".toName, "LightEFTSpanners.FiniteProbability.productLaw".toName, "LightEFTSpanners.FiniteProbability.productLaw_measure".toName, "LightEFTSpanners.FiniteProbability.Law.prob_map".toName, "LightEFTSpanners.FiniteProbability.Law.prob_bind".toName, "LightEFTSpanners.SampledGreedy.freshBatchLaw".toName, "LightEFTSpanners.SampledGreedy.executionLaw".toName]
  for n in required do
    unless visited.contains n do issues := issues.push s!"Missing required reachable interface: {n}"
  LightEFTAuditTiming.mark "interfaces-complete"
  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory
  LightEFTAuditTiming.mark "inventory-written"
  IO.FS.writeFile "ci-evidence/recursive-dependencies.tsv" dependencies
  LightEFTAuditTiming.mark "dependencies-written"
  IO.FS.writeFile "ci-evidence/import-closure-loaded.txt"
    (String.intercalate "\n" (modules.toList.map toString) ++ "\n")
  LightEFTAuditTiming.mark "imports-written"
  IO.FS.writeFile "ci-evidence/strict-violations.txt"
    (String.intercalate "\n" issues.toList ++ "\n")
  LightEFTAuditTiming.mark "findings-written"
  if !issues.isEmpty then throwError "Strict focused audit rejected {issues.size} findings"
  LightEFTAuditTiming.mark "strict-checks-complete"
  logInfo m!"PASS: {roots.size} new-module actual-owner declarations; {visited.size} recursive constants, {opaqueCount} opaque bodies; axioms {axioms.toArray}"

end LightEFTAuditDiagnosticChannel
