import DirectedFlowCutGap.BinarySigned
open DirectedFlowCutGap BinaryArithmetic BinarySigned

#eval do
  for negA in [false,true] do
    for negB in [false,true] do
      for x in [0:17] do
        for y in [0:17] do
          for padding in [0:4] do
            let a : Signed := ⟨negA,Nat.bits x ++ List.replicate padding false⟩
            let b : Signed := ⟨negB,Nat.bits y ++ List.replicate (3-padding) false⟩
            let av : Int := if negA then -(Int.ofNat x) else Int.ofNat x
            let bv : Int := if negB then -(Int.ofNat y) else Int.ofNat y
            let c := BinarySigned.add a b
            let d := BinarySigned.sub a b
            let n := normalize negA a.magnitude
            let B := max a.magnitude.length b.magnitude.length
            unless decode c.1 == av+bv && decode d.1 == av-bv &&
                (less a b).1 == decide (av<bv) &&
                value (magnitude a).1 == av.natAbs && value (toNat a).1 == av.toNat do
              throw <| IO.userError "signed binary arithmetic or comparison changed"
            unless c.1.magnitude.length ≤ B+1 && c.2 ≤ 256*(B+2) &&
                d.1.magnitude.length ≤ B+1 && d.2 ≤ 512*(B+2) do
              throw <| IO.userError "actual signed stored width or charge bound failed"
            unless decode n.1 == av &&
                (value n.1.magnitude != 0 || n.1.negative == false) do
              throw <| IO.userError "signed normalization or negative-zero handling failed"
  let a : Signed := ⟨true,Nat.bits (2^160+31) ++ [false,false]⟩
  let b : Signed := ⟨false,Nat.bits (2^160+29)⟩
  unless decode (BinarySigned.add a b).1 == -2 &&
      decode (BinarySigned.sub a b).1 == -(2^(161:Nat)+60:Int) do
    throw <| IO.userError "wide signed cancellation failed"
  IO.println "PASS 4,624 padded signed pairs including negative zero, all scalar projections and actual charges; 160-bit cancellation"
