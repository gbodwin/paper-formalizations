import Lean
import LightEFTJointFlagSamplingStage.JointAssignmentLaw

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

structure State where
  claims : Std.HashMap ByteArray Nat := {}
  issues : Array String := #[]
  modules : Nat := 0
  constNames : Nat := 0
  extraConstNames : Nat := 0
  parts : Nat := 0
  freed : Nat := 0
  peakRegions : Nat := 0
  repetitions : Nat := 0
  collisions : Nat := 0

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

private def addClaim (state : State) (owner : Nat) (key : ByteArray) : State := Id.run do
  let mut state := state
  if let some prior := state.claims.get? key then
    if prior == owner then
      state := { state with repetitions := state.repetitions + 1 }
    else
      state := { state with
        collisions := state.collisions + 1
        issues := state.issues.push s!"imported-name collision: key={hexKey key}: module indices {prior}, {owner}" }
  else
    state := { state with claims := state.claims.insert key owner }
  return state

@[noinline] private def consumeNames (parts : OwnedParts) (owner : Nat) (initial : State) : IO State := do
  let data ← parts.data.get
  let mut state := initial
  for part in data do
    for name in part.constNames do
      state := addClaim state owner (ownedKey name)
      state := { state with constNames := state.constNames + 1 }
    for name in part.extraConstNames do
      state := addClaim state owner (ownedKey name)
      state := { state with extraConstNames := state.extraConstNames + 1 }
  return state
  -- The non-inlined call ends before data.set #[] and any free operation.
  -- Only independently allocated ByteArray keys, scalar counts/owners and
  -- strings built from those keys escape; no ModuleData/Name/borrowed UTF8 does.

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

@[noinline] private unsafe def scanOne (owner : Nat) (file : System.FilePath) (initial : State) : IO State := do
  let parts : OwnedParts := { data := (← IO.mkRef #[]), regions := (← IO.mkRef #[]) }
  let beforeConst := initial.constNames
  let beforeExtra := initial.extraConstNames
  let result : Except IO.Error State ← try
    loadParts parts file
    pure (.ok (← consumeNames parts owner initial))
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
    return { state with
      modules := state.modules + 1
      parts := state.parts + read
      freed := state.freed + freed
      peakRegions := max state.peakRegions read }

structure Report where
  issues : Array String

@[noinline] unsafe def scan (modules : Array Name) : IO Report := do
  marker s!"AUDIT-PHASE: collision-start modules={modules.size}"
  let mut state : State := {}
  for index in [:modules.size] do
    state ← scanOne index (← findOLean modules[index]!) state
  let count := state.constNames + state.extraConstNames
  marker s!"COLLISION-COVERAGE: {state.modules} modules, {count} declarations/extra-name claims, {state.parts} parts read, {state.freed} regions freed, {state.peakRegions} peak owned regions, {state.claims.size} independent keys, {state.constNames} constNames, {state.extraConstNames} extraConstNames, {state.repetitions} same-module repetitions, {state.collisions} cross-module collisions"
  return { issues := state.issues }
  -- The hash table is ordinary owned memory and is dropped at this boundary,
  -- before the independent owner/recursive audit phases start.

end LightEFTAuditCollision


/- Unexecuted focused audit draft. Reuses the accepted recursive traversal.
Inventories every declaration owned by the new module, then follows all types,
definition/theorem/opaque bodies and inductive/recursor links into imports. -/
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.allImportedModuleNames
  let collisionReport ← LightEFTAuditCollision.scan modules
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
