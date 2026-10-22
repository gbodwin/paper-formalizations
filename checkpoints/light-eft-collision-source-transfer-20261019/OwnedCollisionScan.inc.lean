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
