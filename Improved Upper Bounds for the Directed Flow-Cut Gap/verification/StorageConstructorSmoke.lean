import DirectedFlowCutGap.EncodedArrayStorage
open DirectedFlowCutGap EncodedRoundingInput EncodedArrayStorage

#eval do
  let words : List (List Bool × Nat) :=
    [([],3),([false,false],4),([true,false,false],5),([false,true],6)]
  let out := collect words
  unless out.1.toList == words.map Prod.fst do
    throw (IO.userError "collect changed a stored representation")
  let trace := collectTrace words
  unless trace.length == 120 && fresh trace == 40 && out.2 == 63 do
    throw (IO.userError "four-slot storage trace/charge mismatch")
  let heap := allocateTrace 100 trace
  unless heap.1 == 140 && heap.2.length == 13 &&
      heap.2.all (fun block => 100≤block.1 && block.1+block.2≤140) do
    throw (IO.userError "input-inclusive allocation extent mismatch")
  unless (collectTrace ([] : List (Bool × Nat))).length == 4 &&
      fresh (collectTrace ([] : List (Bool × Nat))) == 2 do
    throw (IO.userError "empty allocation/branch mismatch")
  let table := tabulate fun i : Fin 4 => (words[i.val]!.1,7)
  unless table.1.toList == words.map Prod.fst && table.2 == 106 do
    throw (IO.userError "tabulate result or callback charge mismatch")
  unless enumerationIndices 4 == [3,2,1,0] do
    throw (IO.userError "ofFn callback order mismatch")
  IO.println "PASS actual collect/tabulate values and charges, explicit copy/allocation traces, empty case, padded word representations, descending callback indices"
