import DirectedFlowCutGap.GuardedIntegerRoundingWorkBounds
open DirectedFlowCutGap BinaryArithmetic RetainedGridState

private def checkSingleton : IO Unit := do
  let adj : PairFlags 1 := #v[#v[true]]
  let tape : Bits := [true,false,true,true,false]
  let counted := GuardedIntegerRoundingWork.hard 0 adj 1 tape
  let some cut := counted.1 | throw (IO.userError "packed singleton did not produce a cut")
  let some previous := PhysicalIntegerRounding.hardRun 0 adj 1 tape
    | throw (IO.userError "prior packed singleton did not produce a cut")
  unless cut.mask.toList == [false] && cut.suffix == tape && cut.mask == previous.mask &&
      cut.suffix == previous.suffix && cut.paid == previous.paid && cut.paid < counted.2 do
    throw (IO.userError "packed singleton changed the prior output or failed to charge the driver")
  IO.println s!"PASS original packed singleton cut {cut.mask.toList}, exact suffix {cut.suffix}, previous charge {cut.paid}, with binary fuel {counted.2}"


def main : IO Unit := checkSingleton
