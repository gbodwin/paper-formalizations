/-
SOURCE ONLY. This metadata program has not been elaborated or executed.
It reads serialized headers through the pinned Lean API; it never imports a
target environment, initializes its extensions, or replays its declarations.
The separately bound Python caller must establish genuine CI/source authority.
-/
import Lean

open Lean

private def fail {α : Type} (s : String) : IO α := throw <| IO.userError s

private def stringArray (xs : Array String) : Json :=
  Json.arr <| xs.map Json.str

private def importJson (i : Import) : Json := Json.mkObj [
  ("module", Json.str <| i.module.toString (escape := false)),
  ("is_exported", Json.bool i.isExported),
  ("is_meta", Json.bool i.isMeta),
  ("import_all", Json.bool i.importAll)]

def main (args : List String) : IO UInt32 := do
  let [requestName, outputName] := args
    | fail "Expected an owned request path and fresh output path"
  let requestText ← IO.FS.readFile (System.FilePath.mk requestName)
  if requestText.utf8ByteSize > 1024 * 1024 then fail "Request exceeds bound"
  let request ← match Json.parse requestText with
    | .ok x => pure x
    | .error e => fail e
  let targets ← match request.getObjValAs? (Array String) "targets" with
    | .ok x => pure x
    | .error e => fail e
  if targets.size != 567 && targets.size != 189 then
    fail "Only the complete producer census or one source-bound batch is supported"
  initSearchPath (← findSysroot)
  let searchPath ← searchPathRef.get
  let sourcePath ← getSrcSearchPath
  -- This is the same discovery API used by the pinned leanchecker, once here
  -- rather than changing the checker's actual future per-target invocation.
  let paths ← SearchPath.findAllWithExt searchPath "olean"
  if paths.size > 200000 then fail "Object-name census exceeds reviewed bound"
  let mut census : Array Json := #[]
  let mut names : Array Name := #[]
  for path in paths do
    if let some name ← searchModuleNameOfFileName path searchPath then
      census := census.push <| Json.mkObj [
        ("module", Json.str <| name.toString (escape := false)),
        ("file", Json.str path.toString)]
      names := names.push name
  let mut expansions : Array Json := #[]
  let mut queue : Array Name := #[]
  for targetText in targets do
    let target := targetText.toName
    if target.isAnonymous then fail "Anonymous target"
    let mut expanded : List Name := []
    for name in names do
      if target.isPrefixOf name then expanded := expanded.insert name
    if expanded.isEmpty then fail s!"No object discovered for {targetText}"
    expansions := expansions.push <| Json.mkObj [
      ("target", Json.str targetText),
      ("modules", stringArray <| expanded.toArray.map fun n => n.toString (escape := false))]
    queue := queue ++ expanded.toArray
  let mut seen : Std.HashMap Name Bool := {}
  let mut nodes : Array Json := #[]
  -- A reference keeps regions alive through serialization and the output IO.
  -- There is no unsafe manual unmapping while names may refer into a region.
  let regions ← IO.mkRef (#[] : Array CompactedRegion)
  let mut cursor := 0
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    if seen.contains name then continue
    if seen.size >= 32768 then fail "Import closure exceeds reviewed bound"
    seen := seen.insert name true
    let file ← findOLean name
    let mut fnames := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if (← server.pathExists) then
      fnames := fnames.push server
      let priv := OLeanLevel.private.adjustFileName file
      if (← priv.pathExists) then fnames := fnames.push priv
    let parts ← readModuleDataParts fnames
    let some first := parts[0]? | fail s!"Missing module data for {name}"
    let data := first.1
    let imports := Json.arr <| data.imports.map importJson
    let mut headers : Array Json := #[]
    let mut partIndex := 0
    for part in parts do
      let (partData, region) := part
      regions.modify fun rs => rs.push region
      if partData.isModule != data.isModule ||
          (Json.arr <| partData.imports.map importJson).compress != imports.compress then
        fail s!"Companion headers disagree for {name}"
      let suffix := (#["", ".server", ".private"] : Array String)[partIndex]!
      headers := headers.push <| Json.mkObj [
        ("suffix", Json.str suffix), ("is_module", Json.bool partData.isModule),
        ("imports", Json.arr <| partData.imports.map importJson)]
      partIndex := partIndex + 1
    let source ← findLean sourcePath name
    if !(← source.pathExists) then fail s!"Missing source for {name}: {source}"
    nodes := nodes.push <| Json.mkObj [
      ("module", Json.str <| name.toString (escape := false)),
      ("file", Json.str file.toString),
      ("source", Json.str source.toString),
      ("is_module", Json.bool data.isModule),
      ("imports", imports), ("header_parts", Json.arr headers)]
    queue := queue ++ data.imports.map (·.module)
  let retainedCount := (← regions.get).size
  let result := Json.mkObj [
    ("schema", Json.str "LEAN_4_34_SERIALIZED_HEADER_GRAPH_V1"),
    ("target_count", toJson targets.size),
    ("search_path", stringArray <| searchPath.toArray.map (·.toString)),
    ("source_search_path", stringArray <| sourcePath.toArray.map (·.toString)),
    ("census", Json.arr census), ("expansions", Json.arr expansions),
    ("nodes", Json.arr nodes), ("regions_retained", toJson retainedCount)]
  let encoded := result.compress
  if encoded.utf8ByteSize > 16 * 1024 * 1024 then fail "Header graph exceeds bound"
  IO.FS.writeFile (System.FilePath.mk outputName) encoded
  -- This effectful read is after output; the ref owns every mapped region
  -- throughout header extraction, JSON construction and serialization.
  if (← regions.get).size != retainedCount then fail "Region retention changed"
  return 0
