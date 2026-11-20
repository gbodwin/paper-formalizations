import DirectedFlowCutGap.GuardedFuelFreeRounding
import DirectedFlowCutGap.BinaryGuardedCacheExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

private def asksTwice : Program 3 := fun pc =>
  match pc.val with
  | 0 => .request .r0 1
  | 1 => .request .r1 2
  | _ => .halt

private def entry (source : Bits) : BitState 3 := ⟨[], [], ⟨[], [], [], []⟩, [], 0, source⟩

private theorem ready (source : Bits) :
    Acc (TotalGuardedPackedExecution.Next asksTwice)
      (CachedReferenceExecution.FastState.ofReference (entry source)) := by
  let before := entry source
  let first := allocate { before with source := source.tail } .r0 (.flag (source.headD false)) 1
    [.request (source.headD false)]
  let second := allocate { first.state with source := source.tail.tail } .r1
    (.flag (source.tail.headD false)) 2 [.request (source.tail.headD false)]
  have takesFirst : tick asksTwice before = some first := rfl
  have takesSecond : tick asksTwice first.state = some second := rfl
  have stopped : (attempt asksTwice second.state).result = none := rfl
  exact TotalGuardedPackedExecution.ready_of_run
    (Run.step takesFirst (Run.step takesSecond (Run.done _))) (Or.inl stopped)
    (CachedReferenceExecution.freeze_ofReference before)

private def run (source : Bits) :=
  BinaryGuardedCacheExecution.execute asksTwice
    ⟨CachedReferenceExecution.FastState.ofReference (entry source), ready source⟩ 0

private def checkGuard : IO Unit := do
  let failed := run [true]
  let passed := run [true, false, true, false]
  let some result := passed.1.1 | throw (IO.userError "binary guard rejected a complete tape")
  unless failed.1.1.isNone && failed.1.2 == 71 && passed.1.2 == 154 &&
      result.source == [true, false] && failed.2 == 6607 && passed.2 == 15038 do
    throw (IO.userError "binary guard changed its observation or measured work")
  IO.println s!"PASS binary cached guard, legacy exhaustion {failed.1.2}, success {passed.1.2}, suffix {result.source}, scalar work {failed.2}/{passed.2}"

def main : IO Unit := do
  checkGuard
  let adjacency : RetainedGridState.PairFlags 1 := #v[#v[true]]
  let tape : Bits := [true, false, true, true, false]
  let ((legacy, readback), cache) := GuardedFuelFreeRounding.hardWithWork 0 adjacency 1 (by decide) tape
  let some cut := legacy.1 | throw (IO.userError "packed scalar execution did not return a cut")
  unless cut.mask.toList == [false] && cut.suffix == tape && cut.paid == 70312016 &&
      legacy.2 == cut.paid && readback == 41293 && cache == 35401218 do
    throw (IO.userError "packed scalar execution changed its observation or measured work")
  IO.println s!"PASS packed binary scalar execution, cut {cut.mask.toList}, suffix {cut.suffix}, retained charge {legacy.2}, readback {readback}, cache {cache}"
