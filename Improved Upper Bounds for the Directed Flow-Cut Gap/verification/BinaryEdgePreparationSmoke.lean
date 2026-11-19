import DirectedFlowCutGap.PhysicalBinaryEdgeWire

open DirectedFlowCutGap BinaryArithmetic RawNonnegativeRational

private def a : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def w : Code := ⟨3,8,by decide⟩
private def c : Code := ⟨7,3,by decide⟩
private def costs : Vector (Vector Code 2) 2 := #v[#v[Code.zero,c],#v[Code.zero,Code.zero]]
private def D : EncodedEdgeLineInput.Input 2 := ⟨a,[(0,1)],costs⟩

private def fields {n : ℕ} (row : Vector Code n) := row.toList.map fun q => (q.num,q.den)

private def gadget : IO Unit := do
  let input : EncodedEdgeGadget.Input 2 := ⟨a,#v[#v[Code.zero,w],#v[Code.zero,Code.zero]],costs⟩
  let out := BinaryEdgeGadget.build input
  let ref := EncodedEdgeGadget.build input
  unless out.1.size == ref.size && out.1.labels[0][1].map Fin.val == some 1 &&
      fields out.1.data.weights == fields ref.data.weights && fields out.1.data.costs == fields ref.data.costs &&
      out.1.data.adjacency.toList.map Vector.toList == ref.data.adjacency.toList.map Vector.toList &&
      0 < out.2 && out.2 ≤ BinaryEdgeGadget.budget 2 (4 : ℕ) do
    throw (IO.userError "binary gadget changed its dyadic label, graph, or raw prices")
  IO.println s!"PASS binary edge gadget matched {out.1.size} retained vertices, half label, adjacency and exact rational fields, paid {out.2}"

private def lineAndRound : IO Unit := do
  let line := EncodedEdgeLineInput.lineInput D
  let i := EncodedEdgeLineInput.edgeIndex (n:=2) (0,1)
  let weights := Vector.ofFn fun j => if i=j then Code.one else Code.zero
  let input : EncodedVertexSolver.RoundingInput (EncodedEdgeLineInput.lineSize 2) :=
    ⟨line.adjacency,weights,line.costs⟩
  let tape := [true,false,true]
  let some result := PhysicalAmplifiedBinaryEdge.round D .mass 2 input tape
    | throw (IO.userError "binary edge round failed on a positive line row")
  let some ref := PhysicalAmplifiedEdgeSolver.round D .mass 2 input tape
    | throw (IO.userError "retained edge round failed on a positive line row")
  unless result.mask.toList == ref.mask.toList && result.mask[i.val] && result.suffix == ref.suffix &&
      result.paid > ref.paid do
    throw (IO.userError "binary edge round changed the cut or tape")
  IO.println s!"PASS positive binary edge round selected the original edge, preserved the tape and paid {result.paid}"

private def literalInput : IO Unit := do
  let padded : BinaryRational.Fraction := ⟨[true,false,false],[true,false,false],by decide⟩
  let noDemand : EncodedEdgeInput.Input 1 := ⟨#v[#v[false]],[],#v[padded]⟩
  let self : EncodedEdgeInput.Input 1 := { noDemand with demands := [(0,0)] }
  let tape := [true,false,true]
  let wire := EncodedEdgeInput.encode noDemand
  let first := PhysicalBinaryEdgeWire.edgeWithCost 0 .size wire tape
  let some ⟨n,cut⟩ := first.1 | throw (IO.userError "binary edge entry rejected the padded price")
  let .cut mask := cut.output | throw (IO.userError "binary edge entry returned the wrong tag")
  unless n == 1 && mask.toList.map Vector.toList == [[false]] && cut.suffix == tape &&
      0 < first.2 && 0 < cut.dispatch && 0 < cut.readback && 0 < cut.roundingAndSelection do
    throw (IO.userError "padded binary edge source lost the empty result or a phase charge")
  let second := PhysicalBinaryEdgeWire.edgeWithCost 0 .mass (EncodedEdgeInput.encode self) tape
  let some ⟨_,invalid⟩ := second.1 | throw (IO.userError "binary edge entry lost the self-demand witness")
  let .infeasible (some (s,t)) := invalid.output | throw (IO.userError "binary edge entry returned the wrong witness tag")
  unless s.val == 0 && t.val == 0 && invalid.suffix == tape &&
      (PhysicalBinaryEdgeWire.edgeWithCost 0 .size (wire ++ [true]) tape).1.isNone do
    throw (IO.userError "binary edge source lost the original witness or accepted trailing data")
  IO.println "PASS padded original edge source, original self-demand witness, and counted malformed input rejection"

def main : IO Unit := do
  gadget
  lineAndRound
  literalInput
