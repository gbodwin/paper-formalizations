import DirectedFlowCutGap.GuardedFuelFreeRounding

open DirectedFlowCutGap BinaryArithmetic RetainedGridState ImmutableReferenceSimulation

private def checkAddresses : IO Unit := do
  let heap := CachedReferenceHeap.ofList [.nil,.flag true,.pair [true] []]
  let addresses : List Bits := [[],[true,false,false],[false,true],[true,true]]
  let counted := addresses.map (CachedScalarRead.read heap)
  let old := addresses.map (CachedReferenceHeap.read heap)
  unless (counted.map Prod.fst) == old && (counted.map Prod.snd).all (0 < ·) do
    throw (IO.userError "the scalar reader changed the cached observation")
  IO.println s!"PASS binary cached indexes preserve four read observations, metadata charges {counted.map Prod.snd}"

def main : IO Unit := do
  checkAddresses
  let adjacency : PairFlags 1 := #v[#v[true]]
  let tape : Bits := [true,false,true,true,false]
  let (legacy,metadata) := GuardedFuelFreeRounding.hardMeasured 0 adjacency 1 (by decide) tape
  let some cut := legacy.1 | throw (IO.userError "the measured packed core did not return a mask")
  unless cut.mask.toList == [false] && cut.suffix == tape && cut.paid == 70312016 &&
      legacy.2 == cut.paid && metadata > 0 do
    throw (IO.userError "the measured readback changed the packed result")
  IO.println s!"PASS original packed mask {cut.mask.toList}, suffix {cut.suffix}, retained charge {legacy.2}, measured readback {metadata}"
