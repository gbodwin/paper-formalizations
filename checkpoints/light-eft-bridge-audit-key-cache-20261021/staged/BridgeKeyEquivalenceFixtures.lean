import Lean

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

/- Per-module keys are seeded exclusively from the still-live environment,
before reading any new part. Raw-reader Names are lookup arguments only, never
inserted. Values are independently allocated bytes from the unchanged encoder.
This cache never enters State, so it cannot retain a newly read region. -/
abbrev KeyCache := Std.HashMap Name ByteArray

@[inline] def rememberKey (cache : KeyCache) (name : Name) : KeyCache :=
  if cache.contains name then cache
  else cache.insert name (ownedKey name)

@[inline] def keyFor (cache : KeyCache) (name : Name) : ByteArray :=
  match cache.get? name with
  | some key => key
  | none => ownedKey name

end LightEFTAuditCollision

open Lean in
run_cmd do
  let base : Array Name := #[.anonymous, .str .anonymous "", .str .anonymous "alpha",
    .num .anonymous 0, .str .anonymous "0", .num (.str .anonymous "alpha") 123456789012345678901234567890,
    .str (.str .anonymous "odd name") "日本語", .str .anonymous "é", .str .anonymous "é",
    .str .anonymous "a\tb\nc", .str (.num (.str .anonymous "_private") 42) "helper",
    .str .anonymous "a.»", .str (.str .anonymous "a") "»"]
  let mut deep : Name := .anonymous
  for i in [:128] do deep := .num (.str deep "段") i
  let names := base.push deep
  for seeds in #[#[], names, names ++ names, #[names[0]!, names[2]!, names[3]!]] do
    let mut cache : LightEFTAuditCollision.KeyCache := {}
    for name in seeds do cache := LightEFTAuditCollision.rememberKey cache name
    let expected := seeds.foldl (fun (s : NameSet) n => s.insert n) {}
    unless cache.size == expected.size do throwError "Owned-key cache merged distinct Names"
    for name in names ++ names do
      let direct := LightEFTAuditCollision.ownedKey name
      unless LightEFTAuditCollision.keyFor cache name == direct do
        throwError "Owned-key cache differs from direct lossless encoding"
      if let some stored := cache.get? name then
        unless stored == direct do throwError "Owned-key cache invariant differs"
    unless (LightEFTAuditCollision.keyFor cache (.num .anonymous 0)) !=
        (LightEFTAuditCollision.keyFor cache (.str .anonymous "0")) do
      throwError "Owned-key cache confused numeric and string components"
  logInfo "PASS: bridge owned-key serialization differential fixtures"
