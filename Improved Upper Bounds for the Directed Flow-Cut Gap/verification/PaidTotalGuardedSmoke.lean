import DirectedFlowCutGap.PaidTotalGuardedExecution
open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

private def asksTwice : Program 3 := fun pc =>
  match pc.val with
  | 0 => .request .r0 1
  | 1 => .request .r1 2
  | _ => .halt

private def entry (source : Bits) : BitState 3 := ⟨[],[],⟨[],[],[],[]⟩,[],0,source⟩

private theorem ready (source : Bits) :
    Acc (TotalGuardedPackedExecution.Next asksTwice) (CachedReferenceExecution.FastState.ofReference (entry source)) := by
  let before := entry source
  let a := allocate { before with source := source.tail } .r0 (.flag (source.headD false)) 1 [.request (source.headD false)]
  let b := allocate { a.state with source := source.tail.tail } .r1 (.flag (source.tail.headD false)) 2
    [.request (source.tail.headD false)]
  have first : tick asksTwice before=some a := rfl
  have second : tick asksTwice a.state=some b := rfl
  have stopped : (attempt asksTwice b.state).result=none := rfl
  exact TotalGuardedPackedExecution.ready_of_run (Run.step first (Run.step second (Run.done _)))
    (Or.inl stopped) (CachedReferenceExecution.freeze_ofReference before)

private def run (source : Bits) :=
  PaidTotalGuardedExecution.execute asksTwice ⟨CachedReferenceExecution.FastState.ofReference (entry source),ready source⟩ 0

def main : IO Unit := do
  let failed := run [true]
  let passed := run [true,false,true,false]
  let some result := passed.1 | throw (IO.userError "fuel-free guard rejected a complete tape")
  unless failed.1.isNone && failed.2 == 71 && passed.2 == 154 && result.source == [true,false] do
    throw (IO.userError "fuel-free guard changed its exact charge or suffix")
  IO.println s!"PASS fuel-free guard retained tape exhaustion charge {failed.2}, successful charge {passed.2}, and suffix {result.source}"
