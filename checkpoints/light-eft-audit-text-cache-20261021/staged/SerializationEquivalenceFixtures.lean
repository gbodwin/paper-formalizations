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

/- Source-only fixture for future reviewed bounded validation. Unelaborated. -/
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
  let base : Array Name := #[.anonymous, .str .anonymous "", .str .anonymous "alpha",
    .num .anonymous 0, .str .anonymous "0", .num (.str .anonymous "alpha") 123456789012345678901234567890,
    .str (.str .anonymous "odd name") "日本語", .str .anonymous "é", .str .anonymous "é",
    .str .anonymous "a\tb\nc", .str (.num (.str .anonymous "_private") 42) "helper",
    .str .anonymous "a.»", .str (.str .anonymous "a") "»",
    .str .anonymous "_", .str .anonymous "#0", .str .anonymous "?u"]
  let cases : Array (Array Name) := #[#[], base, base ++ base, #[base[2]!, base[0]!, base[2]!], #[]]
  let mut cache : LightEFTAuditText.Cache := {}
  for names in cases do
    let (actual, next) := LightEFTAuditText.renderNames cache names
    unless actual == String.intercalate "," (names.toList.map toString) do
      throwError "Cached name-list serialization differs"
    cache := next
    let n := base[2]!
    let owner := base[0]!
    let (nameText, afterName) := LightEFTAuditText.renderName cache n
    let (ownerText, afterOwner) := LightEFTAuditText.renderName afterName owner
    let (bodyText, afterBody) := LightEFTAuditText.renderNames afterOwner names
    let direct := String.intercalate "," (names.toList.map toString)
    unless s!"{nameText}\t{ownerText}\ttheorem\t{actual}\t{bodyText}\t{false}\t{true}\n" ==
        s!"{n}\t{owner}\ttheorem\t{direct}\t{direct}\t{false}\t{true}\n" do
      throwError "Cached TSV row serialization differs"
    cache := afterBody
    for name in names do
      let (actual, next) := LightEFTAuditText.renderName cache name
      unless actual == toString name do throwError "Cached name serialization differs"
      unless next.get? name == some (toString name) do throwError "Cache invariant differs"
      cache := next
  logInfo "PASS: pure name-text serialization differential fixtures"
