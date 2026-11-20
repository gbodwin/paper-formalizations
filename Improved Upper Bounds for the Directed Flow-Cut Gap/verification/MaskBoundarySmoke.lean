import DirectedFlowCutGap.MaskBoundaryAssembly

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let extended := MaskBoundaryAssembly.run 3 [true]
  let kept := MaskBoundaryAssembly.run 2 [false,true,true,false]
  let empty := MaskBoundaryAssembly.run 0 [true,false]
  unless extended.1.toList == [true,false,false] && kept.1.toList == [false,true] && empty.1.toList.isEmpty &&
      extended.2 == 185 && kept.2 == 145 && empty.2 == 11 do
    throw (IO.userError "the boundary copy changed bit order, extension or truncation")
  IO.println s!"PASS mask boundary padded {extended.1.toList} with {extended.2}, truncated {kept.1.toList} with {kept.2}, and assembled the empty mask with {empty.2} recorded operations"
