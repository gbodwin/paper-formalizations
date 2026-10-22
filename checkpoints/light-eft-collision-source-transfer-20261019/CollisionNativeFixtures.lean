import Lean

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
      state := { state with collisions := state.collisions + 1,
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
    return { state with modules := state.modules + 1, parts := state.parts + read,
      freed := state.freed + freed, peakRegions := max state.peakRegions read }

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


/- Native fixture source only: NOT EXECUTED during this source-only preparation.
   A future authorized fixture run must use the common exclusive compiler lock,
   source-bound receipts and unchanged resource limits. Never a paper audit. -/
namespace LightEFTAuditCollision
open Lean

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def payload (isModule : Bool) (names extras : Array Name) : ModuleData :=
  { default with isModule := isModule, constNames := names, extraConstNames := extras }

@[noinline] private def saveLegacyFixture (file : System.FilePath) (names extras : Array Name) : IO Unit :=
  saveModuleData file `CollisionSynthetic (payload false names extras)

@[noinline] private def savePartsFixture (file : System.FilePath) (count : Nat) (names extras : Array Name) : IO Unit :=
  saveModuleDataParts `CollisionSynthetic
    ((#[(file,payload true names extras),
        (OLeanLevel.server.adjustFileName file,payload true #[] #[]),
        (OLeanLevel.private.adjustFileName file,payload true #[] #[])]).extract 0 count)

unsafe def fixtureMain (args : List String) : IO Unit := do
  let some path := args.head? | throw <| IO.userError "A fresh fixture directory is required"
  let root : System.FilePath := path
  if ← root.pathExists then throw <| IO.userError "Fixture directory must not exist"
  IO.FS.createDirAll root
  let name := Name.str .anonymous "same"
  let file := root / "same.olean"
  saveLegacyFixture file #[name,name] #[name]
  let same ← scanOne 0 file {}
  ensure (same.repetitions == 2 && same.collisions == 0 && same.claims.size == 1 &&
          same.constNames == 2 && same.extraConstNames == 1 && same.parts == same.freed)
    "same-module repetition"
  marker "NATIVE-FIXTURE: same-module repetition passed"

  let first := root / "cross-a.olean"
  let second := root / "cross-b.olean"
  saveLegacyFixture first #[name] #[]
  savePartsFixture second 3 #[name] #[]
  let initial ← scanOne 0 first {}
  let cross ← scanOne 1 second initial
  ensure (cross.collisions == 1 && cross.parts == 4 && cross.freed == 4 && cross.peakRegions == 3)
    "cross-module collision/reverse release"
  marker "NATIVE-FIXTURE: cross-module collision passed"

  let extraA := root / "extra-a.olean"
  let extraB := root / "extra-b.olean"
  saveLegacyFixture extraA #[] #[name]
  saveLegacyFixture extraB #[] #[name]
  let initial ← scanOne 0 extraA {}
  let extra ← scanOne 1 extraB initial
  ensure (extra.collisions == 1 && extra.constNames == 0 && extra.extraConstNames == 2)
    "extra-name-only collision"
  marker "NATIVE-FIXTURE: extra-name-only collision passed"

  for count in [1,2] do
    let missing := root / s!"missing-{count}.olean"
    savePartsFixture missing count #[name] #[]
    let mut rejected := false
    try
      let _ ← scanOne 0 missing {}
      pure ()
    catch _ => rejected := true
    ensure rejected "missing required part was accepted"
  marker "NATIVE-FIXTURE: missing server/private parts rejected"

  let complex := Name.num (Name.str (Name.str .anonymous "α.β") "") (2^200+17)
  let ownedFile := root / "owned.olean"
  savePartsFixture ownedFile 3 #[complex] #[complex]
  let owned ← scanOne 0 ownedFile {}
  -- All new regions have been freed. Load/free another image before using
  -- the saved key again; a borrowed UTF8/Name key would be invalid here.
  let replacement := root / "replacement.olean"
  savePartsFixture replacement 3 #[name] #[]
  let after ← scanOne 1 replacement owned
  ensure (after.claims.get? (ownedKey complex) == some 0 && after.claims.get? (ownedKey name) == some 1)
    "key did not survive release/reuse independently"
  ensure (ownedKey (Name.num .anonymous 123) != ownedKey (Name.str .anonymous "123"))
    "numeric/string name-key conflation"
  ensure (ownedKey (Name.str (Name.str .anonymous "a") "b") != ownedKey (Name.str .anonymous "a.b"))
    "component-boundary conflation"
  marker "NATIVE-FIXTURE: independent key ownership and lossless distinctions passed"
  marker "NATIVE-FIXTURES: passed"

end LightEFTAuditCollision

unsafe def main (args : List String) : IO Unit :=
  LightEFTAuditCollision.fixtureMain args
