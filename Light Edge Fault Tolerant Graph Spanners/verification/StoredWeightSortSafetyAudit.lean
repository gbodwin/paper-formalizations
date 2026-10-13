import LightEFTSpanners.StoredSortSplit
import LightEFTSpanners.StoredSortSplitExecutable
import LightEFTSpanners.StoredWeightSort
import LightEFTSpanners.StoredWeightSortBounded
import LightEFTSpanners.StoredWeightSortBudget
import LightEFTSpanners.StoredWeightSortEncoding
import LightEFTSpanners.StoredWeightSortExecutable
import LightEFTSpanners.StoredWeightSortTrace
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "LIGHT_WEIGHT_SORT_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`LightEFTSpanners.StoredSortSplit,
    `LightEFTSpanners.StoredSortSplitExecutable,
    `LightEFTSpanners.StoredWeightSort,
    `LightEFTSpanners.StoredWeightSortBounded,
    `LightEFTSpanners.StoredWeightSortBudget,
    `LightEFTSpanners.StoredWeightSortEncoding,
    `LightEFTSpanners.StoredWeightSortExecutable,
    `LightEFTSpanners.StoredWeightSortTrace]
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
    logInfo m!"LIGHT_WEIGHT_SORT_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"LIGHT_WEIGHT_SORT_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`LightEFTSpanners.StoredSortSplit.full_trace,
    `LightEFTSpanners.StoredSortSplit.execute_eq,
    `LightEFTSpanners.StoredWeightSort.sort_trace,
    `LightEFTSpanners.StoredWeightSort.split_budget,
    `LightEFTSpanners.StoredWeightSort.bounded_sort_trace,
    `LightEFTSpanners.StoredWeightSort.full_trace,
    `LightEFTSpanners.StoredWeightSort.execute_encoded] do
    IO.eprintln s!"LIGHT_WEIGHT_SORT_CLOSURE_BEGIN {root}"
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
    logInfo m!"LIGHT_WEIGHT_SORT_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
