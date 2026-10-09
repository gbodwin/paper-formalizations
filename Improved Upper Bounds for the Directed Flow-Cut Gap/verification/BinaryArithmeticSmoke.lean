import DirectedFlowCutGap.BinaryCounters
open DirectedFlowCutGap BinaryArithmetic BinaryCounters

private def check (x y : Nat) (xs ys : Bits) : IO Unit := do
  for c in [false,true] do
    let a := add c xs ys
    unless value a.1 == x+y+c.toNat && a.1.length ≤ max xs.length ys.length+1 &&
        a.2 ≤ 16*(max xs.length ys.length+1) do
      throw <| IO.userError "binary carry addition mismatch"
  let m := mul xs ys
  let cmp := BinaryArithmetic.compare xs ys
  unless value m.1 == x*y && m.2 ≤ 64*(xs.length+1)*(xs.length+ys.length+2) &&
      cmp.less == decide (x<y) && cmp.equal == decide (x=y) do
    throw <| IO.userError "binary multiplication or comparison mismatch"
  let a := addCanonical xs ys
  let p := mulCanonical xs ys
  let b := max xs.length ys.length
  unless value a.1 == x+y && value p.1 == x*y &&
      a.1.length == Nat.size (x+y) && p.1.length == Nat.size (x*y) &&
      a.2 ≤ 32*(b+2) && p.2 ≤ 512*(b+1)^2 do
    throw <| IO.userError "canonical binary arithmetic mismatch"
  let t := trim xs
  let pred := predecessor xs
  let len := lengthBits xs
  let sz := sizeBits xs
  unless value t.1 == x && t.1.length == Nat.size x &&
      value pred.1 == x-1 && pred.1.length == Nat.size (x-1) &&
      pred.2 ≤ 32*(xs.length+1) && value len.1 == xs.length &&
      len.2 ≤ 16*(xs.length+1)^2 && value sz.1 == Nat.size x &&
      sz.2 ≤ 32*(xs.length+1)^2 do
    throw <| IO.userError "binary normalization, predecessor, or size mismatch"

#eval do
  for x in [0:96] do
    for y in [0:96] do
      check x y x.bits y.bits
  for b in [0,1,8,32,80,128,256] do
    for d in [0:12] do
      let x := 2^b+d
      let y := 2^b-1
      check x y (x.bits ++ List.replicate (d%5) false)
        (y.bits ++ List.replicate ((d+2)%7) false)
    let p := powerOfTwo b
    unless value p.1 == 2^b && p.1.length == b+1 && p.2 ≤ 32*(b+1)^2 do
      throw <| IO.userError "binary power-of-two mismatch"
    let k := b.bits ++ [false,false]
    let p := powerOfTwoBinary k
    unless value p.1 == 2^b && p.1.length == b+1 && p.2 ≤ 64*(b+1)*(k.length+1) do
      throw <| IO.userError "binary-controlled power-of-two mismatch"
  IO.println "PASS 9216 exact binary pairs, both carries, canonicalization, predecessor and width; padded cases through 256 bits and bounded shifts"
