import LightEFTSpanners.StoredForestComponentIndices
import LightEFTSpanners.StoredForestHosts
import LightEFTSpanners.StoredForestHostsCoverage
import LightEFTSpanners.StoredForestHostsExecutable
import LightEFTSpanners.StoredForestHostsOriginal
import LightEFTSpanners.StoredForestHostsTrace
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "LIGHT_FOREST_HOSTS_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`LightEFTSpanners.StoredForestComponentIndices,
    `LightEFTSpanners.StoredForestHosts,
    `LightEFTSpanners.StoredForestHostsCoverage,
    `LightEFTSpanners.StoredForestHostsExecutable,
    `LightEFTSpanners.StoredForestHostsOriginal,
    `LightEFTSpanners.StoredForestHostsTrace]
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
    logInfo m!"LIGHT_FOREST_HOSTS_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"LIGHT_FOREST_HOSTS_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`LightEFTSpanners.StoredForestHosts.scan_trace,
      `LightEFTSpanners.StoredForestHosts.full_trace,
      `LightEFTSpanners.StoredForestHosts.execute_eq,
      `LightEFTSpanners.StoredForestHosts.mem_value,
      `LightEFTSpanners.StoredForestHosts.mem_execute_family,
      `LightEFTSpanners.StoredForestHosts.component_coverage,
      `LightEFTSpanners.StoredForestHosts.indices_nodup,
      `LightEFTSpanners.StoredForestHosts.indices_univ,
      `LightEFTSpanners.StoredForestHosts.label_injective] do
    IO.eprintln s!"LIGHT_FOREST_HOSTS_CLOSURE_BEGIN {root}"
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
    logInfo m!"LIGHT_FOREST_HOSTS_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
