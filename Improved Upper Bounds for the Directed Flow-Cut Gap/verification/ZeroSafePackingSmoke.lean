import DirectedFlowCutGap.BinaryWeightedPacking

/-! Finite regressions for the literal zero-avoiding provider and its packing
composition. The toy provider always reports no cut; the real support fallback,
bottleneck scan, cached controller and final sampler must still execute. -/
open DirectedFlowCutGap
open BinaryArithmetic
set_option synthInstance.maxSize 10000

private def columns (m : Nat) : Set (FractionalCover.Column m) := {S | S.Nonempty}
private theorem emptyExcluded (m : Nat) : (∅ : FractionalCover.Column m) ∉ columns m := by
  simp [columns]
private def oneRow : BinaryFractionalRows.Row 1 := Vector.replicate 1 BinaryRational.one
private def mixedRow : BinaryFractionalRows.Row 2 := #v[BinaryRational.zero,BinaryRational.one]
private theorem oneSupport : BinaryZeroAvoidingProvider.SupportValid oneRow (columns 1) := by
  change (ZeroAvoidingSelector.positiveSupport (BinaryZeroAvoidingSelector.tableValue oneRow)).Nonempty
  rw [← BinaryZeroAvoidingSelector.support_correct]
  exact ⟨0,by decide⟩
private theorem mixedSupport : BinaryZeroAvoidingProvider.SupportValid mixedRow (columns 2) := by
  change (ZeroAvoidingSelector.positiveSupport (BinaryZeroAvoidingSelector.tableValue mixedRow)).Nonempty
  rw [← BinaryZeroAvoidingSelector.support_correct]
  exact ⟨1,by decide⟩
private def absent (m : Nat) : BinaryZeroAvoidingProvider.CutAnswer (columns m) :=
  { mask := none, operations := 17, failed := true, trials := [false,true,false],
    consumed := [true,true,false], valid := by intro x hx; cases hx }
private structure Effects where
  queries : Nat := 0
  bits : Nat := 0
private def draw (m : Nat) : BinaryZeroAvoidingProvider.CutProvider (StateM Effects) (columns m) :=
  fun _ => do
    modify fun s => {s with queries := s.queries+1}
    pure (absent m)
private def bit : StateM Effects Bool := do
  modify fun s => {s with bits := s.bits+1}
  pure false
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def selectorCases : IO Unit := do
  let costs : BinaryFractionalRows.Row 2 := Vector.replicate 2 BinaryRational.one
  let q := BinaryZeroAvoidingSelector.prepare mixedRow costs
  check (q.fallback.toList == [false,true]) "positive support excludes exact zero"
  check (value q.budget.num == 1 && value q.budget.den == 1) "original support budget"
  check (value (BinaryFractionalRows.get q.costs 0).num == 2 &&
    value (BinaryFractionalRows.get q.costs 0).den == 1) "retained off-support penalty"
  let missing := BinaryZeroAvoidingSelector.select q (none,17)
  check (missing.1.toList == [false,true] && missing.2 == 21) "absent-provider fallback retains charge"
  let expensive := BinaryZeroAvoidingSelector.select q (some #v[true,false],17)
  check (expensive.1.toList == [false,true] && decide (17 < expensive.2)) "expensive candidate replaced by support"
  let cheap := BinaryZeroAvoidingSelector.select q (some #v[false,false],17)
  check (cheap.1.toList == [false,false] && decide (17 < cheap.2)) "literal cheap-candidate branch"
  IO.println s!"PASS zero-safe selector branches; operations={q.work},{missing.2},{expensive.2},{cheap.2}"

private def providerCases : IO Unit := do
  let costs : BinaryFractionalRows.Row 2 := Vector.replicate 2 BinaryRational.one
  let (answer,effects) := (BinaryZeroAvoidingProvider.provider mixedRow (columns 2)
    mixedSupport (emptyExcluded 2) (draw 2) costs).run {}
  check (effects.queries == 1 && effects.bits == 0) "one actual query, no bit effect"
  check (answer.1.choice.mask.toList == [false,true] && answer.1.choice.bottleneck.val == 1)
    "fallback and fresh original-capacity bottleneck"
  check (answer.1.failed && answer.1.trials == [false,true,false] && answer.1.consumed == [true,true,false])
    "physical failure and padded metadata preserved verbatim"
  let prepared := BinaryZeroAvoidingSelector.prepare mixedRow costs
  let selected := BinaryZeroAvoidingSelector.select prepared (none,17)
  let bottleneck := BinaryFractionalGraphOracle.bottleneck mixedRow selected.1
  check (answer.1.operations == prepared.work+selected.2+bottleneck.2+20) "provider charge composition"
  IO.println s!"PASS zero-safe provider metadata and bottleneck; operations={answer.1.operations}"

private def packingCases : IO Unit := do
  let (out,effects) := (BinaryWeightedPacking.run oneRow (columns 1) oneSupport
    (emptyExcluded 1) (draw 1) bit [true]).run {}
  check (effects.queries == 1 && out.history.answers.length == 1) "startup choice cached without duplicate provider call"
  check (out.history.rest.state.events.length == 1 && out.history.rest.stopTests == 3 &&
    out.history.rest.guardTests == 4) "one active update and two stopped scans"
  check (out.history.answers.all fun a => a.failed && a.trials == [false,true,false] &&
    a.consumed == [true,true,false]) "all provider metadata retained in chronological history"
  check (out.selected.label == (some [true] : Option Bits) && !out.selected.failed && !out.selected.zeroTotal)
    "final selected nonempty original cut"
  check (value out.selected.trials == 1 && value out.selected.consumed == effects.bits && effects.bits == 1)
    "final sampler actual bit effects"
  let filled := BinaryPositiveCapacities.prepare oneRow
  check (out.operations == filled.2+out.history.operations+out.selected.operations+8)
    "full wrapper adds preparation, history, sampler and result charges"
  IO.println s!"PASS zero-safe cached packing and final draw; operations={out.operations}; calls={effects.queries}; bits={effects.bits}"

def main : IO Unit := do
  selectorCases
  providerCases
  packingCases
  IO.println "PASS all three zero-safe packing execution groups"
