import Lean

/- Uses the pinned official checker's target-selection operations, without launching a checker. -/
open Lean in
run_cmd do
  let some arg ← IO.getEnv "LIGHTEFT_CHECKER_TARGET" | throwError "Missing target"
  let some output ← IO.getEnv "LIGHTEFT_CHECKER_RESOLUTION_FILE" | throwError "Missing output path"
  initSearchPath (← findSysroot)
  let target := arg.toName
  let sp ← searchPathRef.get
  let mut matches : List Name := []
  for path in (← SearchPath.findAllWithExt sp "olean") do
    if let some m ← searchModuleNameOfFileName path sp then
      if target.isPrefixOf m then matches := matches.insert m
  let mut objects : Array Json := #[]
  for m in matches do
    objects := objects.push (Json.mkObj [("module", toJson m.toString),
      ("object", toJson (← findOLean m).toString)])
  let result := Json.mkObj [("target", toJson arg), ("resolved", Json.arr objects),
    ("count", toJson matches.length), ("search_path", toJson (sp.map (·.toString)))]
  IO.FS.writeFile output (result.pretty ++ "\n")
  if target == `LightEFTSpanners || target == `LightSpanners || matches != [target] then
    throwError "REFUSED checker target {target}: {matches.length} actual modules; only exact singleton non-aggregate targets are allowed"
  logInfo m!"PASS: official checker resolution is exactly [{target}]"
