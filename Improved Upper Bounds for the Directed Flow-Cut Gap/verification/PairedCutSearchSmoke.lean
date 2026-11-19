import DirectedFlowCutGap.PhysicalPairedVertex
import DirectedFlowCutGap.PhysicalPairedEdge

open DirectedFlowCutGap
open BinaryArithmetic

private def read (expected output : Bool) : Bits → Option (PairedCutSearch.Result Bool)
  | bit::rest => if bit == expected then some ⟨output,rest,7⟩ else none
  | [] => none

private def price (cut : Bool) : BinaryRational.Fraction × ℕ :=
  if cut then (BinaryRational.one,2)
  else (⟨[false,true],[true],by decide⟩,3)

def main : IO Unit := do
  let suffix : Bits := [false,false,true]
  let some chosen := PairedCutSearch.run price (read true false) (read false true) (true::false::suffix) |
    throw (IO.userError "the second run did not receive the exact first suffix")
  unless chosen.output && chosen.suffix == suffix && chosen.paid > 14 do
    throw (IO.userError "the combined cut selected the wrong price or lost tape/cost")
  IO.println s!"PASS the cheaper second cut used the first unread bit and preserved the tail, paid {chosen.paid}"
  let q : BinaryRational.Fraction := ⟨[true,false,false],[true,false,false,false],by decide⟩
  let vertex : BinaryFractionalGuesses.Input 2 := ⟨#v[#v[false,true],#v[false,false]],[],#v[q,q]⟩
  let wire := PhysicalSourceDispatch.input vertex
  let observed := PhysicalPairedVertex.withCost 0 wire suffix
  let some ⟨n,cut⟩ := observed.1 | throw (IO.userError "the paired vertex wire failed")
  let .cut mask := cut.output | throw (IO.userError "the paired vertex wire returned the wrong tag")
  let trailing := PhysicalPairedVertex.withCost 0 (wire++[true]) suffix
  unless n == 2 && mask.toList == [false,false] && cut.suffix == suffix &&
      0 < cut.paid && 0 < observed.2 && trailing.1.isNone && 0 < trailing.2 do
    throw (IO.userError "the paired vertex wire changed the mask, suffix, or parsing charge")
  IO.println s!"PASS both vertex modes on a padded wire, with the exact empty mask and counted rejection, paid {cut.paid}"
  let edge : EncodedEdgeInput.Input 1 := ⟨#v[#v[false]],[(0,0)],#v[q]⟩
  let e := PhysicalPairedEdge.withCost 0 (EncodedEdgeInput.encode edge) suffix
  let some ⟨m,witness⟩ := e.1 | throw (IO.userError "the paired edge wire failed")
  let .infeasible (some (s,t)) := witness.output | throw (IO.userError "the original edge witness was lost")
  unless m == 1 && s.val == 0 && t.val == 0 && witness.suffix == suffix && 0 < witness.paid && 0 < e.2 do
    throw (IO.userError "the paired edge wire changed the self-demand, suffix or charge")
  IO.println s!"PASS both edge modes on a padded wire retained the original self-demand witness, paid {witness.paid}"
