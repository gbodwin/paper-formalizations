import DirectedFlowCutGap.BinaryRandomWord
open DirectedFlowCutGap BinaryArithmetic BinaryRandomWord
private def nextBit : StateM (Nat × Nat) Bool := do
  let (code,used) ← get
  set (code/2,used+1)
  pure (code%2 == 1)
#eval do
  for count in [0:10] do
    for padding in [0:4] do
      let bs := Nat.bits count ++ List.replicate padding false
      for code in [0:2^count] do
        let (r,(_,used)) := (word nextBit bs).run (code,0)
        unless value r.bits == code && r.bits.length == count && used == count &&
            r.steps ≤ 64*(count+1)*(bs.length+1) do
          throw <| IO.userError "binary-controlled random word mismatch"
  let (empty,(_,used)) := (word nextBit [false,false,false]).run (123,0)
  unless empty.bits.isEmpty && used == 0 do
    throw <| IO.userError "padded zero counter requested a random bit"
  IO.println "PASS actual binary-controlled bit requests, padded counters, exact word values, state consumption and instruction bounds"
