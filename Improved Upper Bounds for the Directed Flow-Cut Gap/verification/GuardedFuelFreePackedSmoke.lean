import DirectedFlowCutGap.GuardedFuelFreeRounding
open DirectedFlowCutGap BinaryArithmetic RetainedGridState

def main : IO Unit := do
  let adjacency : PairFlags 1 := #v[#v[true]]
  let tape : Bits := [true,false,true,true,false]
  let counted := GuardedFuelFreeRounding.hard 0 adjacency 1 (by decide) tape
  let some cut := counted.1 | throw (IO.userError "fuel-free packed singleton failed")
  unless cut.mask.toList == [false] && cut.suffix == tape && cut.paid == 70312016 && counted.2 == cut.paid do
    throw (IO.userError "fuel-free packed singleton changed the cut, suffix or interpreter work")
  IO.println s!"PASS fuel-free original packed singleton, cut {cut.mask.toList}, exact suffix {cut.suffix}, charge {counted.2}"
