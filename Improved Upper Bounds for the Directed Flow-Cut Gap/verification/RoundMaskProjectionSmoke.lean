import DirectedFlowCutGap.FramedProjectedRoundWork

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage EncodedUnitCostReplication
open RawNonnegativeRational (Code)

private def input2 (cost : Code) : Input 2 :=
  ⟨#v[#v[false,true],#v[false,false]],#v[Code.one,Code.one],#v[cost,cost]⟩
private def input1 (weight : Code) : Input 1 :=
  ⟨#v[#v[false]],#v[weight],#v[Code.one]⟩

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  let d := input2 Code.zero
  let some m := (PaidVertexRounding.runner .mass 0 d tape).1 | throw (IO.userError "weighted pullback failed")
  let p := RunnerProjectionLayout.code .mass 0 d tape
  unless m.mask.toList == [true,true] && m.suffix == tape && p.length == 17 do
    throw (IO.userError "zero-objective pullback changed the mask, tape or projection layout")
  IO.println s!"PASS zero-objective weighted pullback retained {m.mask.toList} and {m.suffix}, with {p.length} modeled instructions"
  let d := input2 Code.one
  let some s := (PaidVertexRounding.runner .size 0 d tape).1 | throw (IO.userError "heavy pullback failed")
  let p := RunnerProjectionLayout.code .size 0 d tape
  unless s.mask.toList == [true,true] && s.suffix == tape && p.length == 40 do
    throw (IO.userError "heavy pullback changed the mask, tape or projection layout")
  IO.println s!"PASS heavy union restored {s.mask.toList} and retained {s.suffix}, with {p.length} modeled instructions"
  let weak := input1 Code.zero
  let strong := input1 Code.one
  let some a := (PaidVertexRounding.uniform 0 weak tape).1 | throw (IO.userError "subunit uniform cut failed")
  let some b := (PaidVertexRounding.uniform 0 strong tape).1 | throw (IO.userError "reached uniform cut failed")
  let p := RunnerProjectionLayout.uniformCode 0 strong tape
  let (last,blocks) := allocateTrace 31 p
  let binary := BinaryAllocationTrace.allocate (31 : ℕ).bits (p.map BinaryAllocationTrace.reservation)
  unless a.cut.mask.toList == [false] && b.cut.mask.toList == [true] &&
      a.cut.suffix == tape && b.cut.suffix == tape &&
      (RunnerProjectionLayout.uniformCode 0 weak tape).isEmpty && p.length == 76 && fresh p == 38 &&
      value binary.stop == last && binary.blocks.map (fun (start,size) => (value start,value size)) == blocks do
    throw (IO.userError "uniform projection changed its branch, mask, tape or reservations")
  IO.println s!"PASS uniform subunit cut skipped the pullback, and the reached cut kept {b.cut.suffix} with {p.length} instructions and {fresh p} cells"
