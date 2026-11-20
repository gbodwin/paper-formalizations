import DirectedFlowCutGap.EdgeGadgetArrayStorage

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage RawNonnegativeRational EncodedEdgeGadget

def main : IO Unit := do
  let adjacency : Vector (Vector Bool 3) 3 :=
    #v[#v[true,true,false],#v[false,false,true],#v[true,false,false]]
  let small : RawNonnegativeRational.Code := ⟨3,8,by decide⟩
  let weights := #v[#v[Code.zero,small,Code.one],#v[Code.zero,Code.zero,small],#v[Code.one,Code.zero,Code.zero]]
  let prices := #v[#v[Code.ofNat 2,⟨7,3,by decide⟩,Code.ofNat 42],#v[Code.zero,Code.zero,Code.ofNat 5],
    #v[Code.ofNat 9,Code.zero,Code.zero]]
  let input : Input 3 := ⟨adjacency,weights,prices⟩
  let built := BinaryEdgeGadget.buildWithControl input
  let g := built.1.1
  let start := 19
  let code := EdgeGadgetArrayStorage.codeFor 3 g.size
  let model := allocateTrace start code
  let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  let blocks := binary.blocks.map fun (base,count) => (value base,value count)
  unless g.size == 14 && built.1.2 == 32893 && code.length == 7609 && fresh code == 2617 &&
      blocks.length == 272 && value binary.stop == 2636 && value binary.stop == model.1 && blocks == model.2 do
    throw (IO.userError "the measured gadget or its array reservation schedule changed")
  IO.println s!"PASS measured 14-node gadget kept fee {built.1.2}; modeled arrays used {code.length} instructions, {fresh code} cells and {blocks.length} reservations"
