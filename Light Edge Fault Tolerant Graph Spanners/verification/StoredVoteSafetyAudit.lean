import LightEFTSpanners.StoredVoteMachine
import LightEFTSpanners.StoredVoteTrace
import LightEFTSpanners.StoredVoteEncoding
import LightEFTSpanners.StoredVoteBound
import LightEFTSpanners.StoredVoteExecutable
import LightEFTSpanners.StoredEdgeMembership
import LightEFTSpanners.StoredSampleEntry
import LightEFTSpanners.StoredSampleEncoding
import LightEFTSpanners.StoredRecordMachine
import LightEFTSpanners.StoredRecordTrace
import LightEFTSpanners.StoredRecordEncoding
import LightEFTSpanners.StoredRecordExecutable
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "LIGHT_STORED_VOTE_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`LightEFTSpanners.StoredEdgeMembership,
    `LightEFTSpanners.StoredSampleEntry,
    `LightEFTSpanners.StoredSampleEncoding,
    `LightEFTSpanners.StoredRecordMachine,
    `LightEFTSpanners.StoredRecordTrace,
    `LightEFTSpanners.StoredRecordEncoding,
    `LightEFTSpanners.StoredRecordExecutable,
    `LightEFTSpanners.StoredVoteMachine,
    `LightEFTSpanners.StoredVoteTrace,
    `LightEFTSpanners.StoredVoteEncoding,
    `LightEFTSpanners.StoredVoteBound,
    `LightEFTSpanners.StoredVoteExecutable]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe stored record declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden stored record axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"LIGHT_STORED_VOTE_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"LIGHT_STORED_VOTE_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`LightEFTSpanners.StoredEdges.scan_trace,
      `LightEFTSpanners.StoredEdges.contains_encode,
      `LightEFTSpanners.StoredSample.entry_trace,
      `LightEFTSpanners.StoredRecords.materialize_trace,
      `LightEFTSpanners.StoredRecords.construct_encoded,
      `LightEFTSpanners.StoredRecords.execute_encode,
      `LightEFTSpanners.StoredVote.construct_trace,
      `LightEFTSpanners.StoredVote.encoded_vote_trace,
      `LightEFTSpanners.StoredVote.encoded_bound,
      `LightEFTSpanners.StoredVote.run_encoded,
      `LightEFTSpanners.StoredVote.execute_iff_estimate] do
    IO.eprintln s!"LIGHT_STORED_VOTE_CLOSURE_BEGIN {root}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name | throwError "Missing closure constant: {name}"
        if ci.isUnsafe then throwError "Unsafe closure constant: {root}: {name}"
        match ci with
        | .axiomInfo _ =>
          axioms := axioms.insert name
          unless allowed.contains name do throwError "Forbidden closure axiom: {root}: {name}"
        | _ => pure ()
        for dep in ci.getUsedConstantsAsSet.toList do
          unless seen.contains dep do todo := todo.push dep
    logInfo m!"LIGHT_STORED_VOTE_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
