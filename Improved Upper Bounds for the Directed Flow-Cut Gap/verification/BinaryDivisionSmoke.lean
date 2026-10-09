import DirectedFlowCutGap.BinaryDivision

open DirectedFlowCutGap.BinaryArithmetic
open DirectedFlowCutGap.BinaryDivision

private def assertBit (ok : Bool) (message : String) : IO Unit :=
  if ok then pure () else throw (IO.userError message)

private def testPair (xs ys : Bits) : IO Unit := do
  let n := value xs
  let d := value ys
  let r := divide xs ys
  assertBit (value r.quotient == n/d) "quotient mismatch"
  assertBit (value r.remainder == n%d) "remainder mismatch"
  assertBit (r.quotient.length == (n/d).size) "quotient not canonical"
  assertBit (r.remainder.length == (n%d).size) "remainder not canonical"
  assertBit (decide (r.steps ≤ 256*(xs.length+ys.length+2)^2)) "division charge"
  let s := sub xs ys
  assertBit (value s.1 == n-d) "subtraction mismatch"
  assertBit (s.1.length == (n-d).size) "subtraction not canonical"
  assertBit (decide (s.2 ≤ 64*(xs.length+ys.length+1))) "subtraction charge"

#eval do
  let mut pairs := 0
  for n in List.range 128 do
    for d in List.range 64 do
      testPair (n.bits ++ [false,false]) (d.bits ++ [false,false,false])
      pairs := pairs+1
  for pair in [(2^160-1,2^80+1),(2^128,3),(2^160,0),(0,2^160),(2^99+13,2^99+13)] do
    testPair (pair.1.bits ++ List.replicate 9 false)
      (pair.2.bits ++ List.replicate 11 false)
  testPair [] []
  testPair [false,false] []
  IO.println s!"PASS {pairs} noncanonical division/subtraction pairs, 5 wide cases, and empty/zero cases"
