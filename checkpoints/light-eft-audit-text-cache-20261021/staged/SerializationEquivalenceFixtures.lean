import Lean

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
