import LightEFTSpanners.PreparedOutputLaw
import LightEFTSpanners.PreparedProbabilityGuarantee
import LightEFTSpanners.PreparedGreedyGuarantee
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "LIGHT_PREPARED_GUARANTEE_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`LightEFTSpanners.PreparedOutputLaw,
    `LightEFTSpanners.PreparedProbabilityGuarantee,
    `LightEFTSpanners.PreparedGreedyGuarantee]
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
    logInfo m!"LIGHT_PREPARED_GUARANTEE_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"LIGHT_PREPARED_GUARANTEE_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`LightEFTSpanners.StoredPreparedCandidates.assignment_failure_le,
      `LightEFTSpanners.StoredPreparedCandidates.actual_output_failure_probability,
      `LightEFTSpanners.StoredPreparedCandidates.exists_prepared_optimum_high_probability] do
    IO.eprintln s!"LIGHT_PREPARED_GUARANTEE_CLOSURE_BEGIN {root}"
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
    logInfo m!"LIGHT_PREPARED_GUARANTEE_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
