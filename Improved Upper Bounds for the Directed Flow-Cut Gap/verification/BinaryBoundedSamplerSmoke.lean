import DirectedFlowCutGap.BinaryBoundedSampler
open DirectedFlowCutGap BinaryArithmetic BinaryBoundedSampler

private def nextBit : StateM (Nat × Nat) Bool := do
  let (code,used) ← get
  set (code/2,used+1)
  pure (code%2 == 1)

#eval do
  for n in [1:9] do
    for trials in [0:4] do
      for padding in [0:3] do
        let bound := Nat.bits n ++ List.replicate padding false
        let fuel := Nat.bits trials ++ List.replicate padding false
        for code in [0:2^(FairBitWords.width n*trials)] do
          let actual : Option (Output bound) × (Nat × Nat) :=
            (checkedDraw nextBit bound fuel).run (code,0)
          let reference : Option (BitSamplerCoupling.DefaultOutput (value bound)) × (Nat × Nat) :=
            ((if h : 0<value bound then
              some <$> MonadicBitSampler.draw (BinaryRandomWord.bitIndex <$> nextBit)
                (value bound) h trials
            else pure none) : StateM (Nat × Nat) _).run (code,0)
          unless actual.1.map observe == reference.1 && actual.2 == reference.2 do
            throw <| IO.userError "binary bounded rejection disagrees with whole state reference"
  let zero : Option (Output [false,false]) × (Nat × Nat) :=
    (checkedDraw nextBit [false,false] [true,true]).run (123,0)
  unless zero.1.isNone && zero.2 == (123,0) do
    throw <| IO.userError "zero bound guard consumed randomness"
  IO.println "PASS binary bounds and trial fuel, padded representations, success/rejection/failure flags, exact stored counters and complete source-state equality"
