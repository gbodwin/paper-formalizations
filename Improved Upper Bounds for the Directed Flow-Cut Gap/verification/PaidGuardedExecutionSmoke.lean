import DirectedFlowCutGap.PaidGuardedExecution
open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def asksTwice : Program 3 := fun pc =>
  match pc.val with
  | 0 => .request .r0 1
  | 1 => .request .r1 2
  | _ => .halt

private def initial (source : Bits) : CachedReferenceExecution.FastState 3 :=
  .ofReference ⟨[],[],⟨[],[],[],[]⟩,[],0,source⟩

def main : IO Unit := do
  let program := asksTwice
  let fuel := (3 : ℕ).bits
  let short := PaidGuardedExecution.executeBinary program fuel (initial [true]) 0
  let zero := PaidGuardedExecution.executeBinary program [] (initial [true,false]) 0
  let limited := PaidGuardedExecution.executeBinary program (1 : ℕ).bits (initial [true,false]) 0
  unless short.1.1.isNone && 0 < short.1.2 && 0 < short.2 &&
      zero.1.1.isNone && zero.1.2 == 0 && 0 < zero.2 &&
      limited.1.1.isNone && 0 < limited.1.2 && 0 < limited.2 do
    throw (IO.userError "tape or fuel exhaustion lost incurred work")
  let tape : Bits := [true,false,true,false]
  let complete := PaidGuardedExecution.executeBinary program fuel (initial tape) 0
  let some final := complete.1.1 | throw (IO.userError "guarded run failed on a complete tape")
  let some (old,oldPaid) := CachedGuardedReferenceExecution.execute program 3 (initial tape) 0
    | throw (IO.userError "the existing guarded run failed")
  unless final.source == [true,false] && final.source == old.source && complete.1.2 == oldPaid && 0 < complete.2 do
    throw (IO.userError "the counted guard changed the prior successful run")
  IO.println s!"PASS paid tape exhaustion {short.1.2}, paid fuel exhaustion {limited.1.2}, unchanged successful charge {complete.1.2} and suffix {final.source}"
