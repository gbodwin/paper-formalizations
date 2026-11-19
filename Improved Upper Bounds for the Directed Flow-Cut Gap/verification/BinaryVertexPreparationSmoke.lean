import DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex

open DirectedFlowCutGap
open RawNonnegativeRational BinaryArithmetic

private def weight (a b : ℕ) (positive : 0 < b) : Code := ⟨a,b,positive⟩

private def adjacency : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]

private def positive : EncodedUnitCostReplication.Input 3 :=
  ⟨adjacency,#v[weight 1 32 (by decide),weight 1 1 (by decide),weight 1 16 (by decide)],#v[Code.one,Code.one,Code.one]⟩

private def compareRound (name : String)
    (old : ℕ → EncodedUnitCostReplication.Input 3 → Bits → Option (PhysicalIntegerRounding.Result 3))
    (binary : ℕ → EncodedUnitCostReplication.Input 3 → Bits → Option (PhysicalBinaryVertexRounding.Result 3))
    (D : EncodedUnitCostReplication.Input 3) : IO Unit := do
  let tape : Bits := [true,false,true,false]
  let some result := binary 3 D tape | throw (IO.userError s!"{name} binary preparation failed")
  let some ref := old 3 D tape | throw (IO.userError s!"{name} retained preparation failed")
  unless result.cut.mask.toList == ref.mask.toList && result.cut.suffix == ref.suffix &&
      result.cut.paid == ref.paid && 0 < result.arithmetic &&
      result.arithmetic ≤ PhysicalBinaryVertexRounding.sizeBudget 3 (5 : ℕ) do
    throw (IO.userError s!"{name} differed in cut, tape or charge")
  IO.println s!"PASS {name} preserves mask {result.cut.mask.toList}, suffix {result.cut.suffix}, and recorded word charge {ref.paid}, binary arithmetic {result.arithmetic}"

private def original : BinaryFractionalGuesses.Input 3 :=
  ⟨adjacency,[(0,2)],#v[BinaryRational.one,BinaryRational.one,BinaryRational.one]⟩

private def positiveSource : IO Unit := do
  let tape : Bits := [true,false,true]
  let wire := PhysicalSourceDispatch.input original
  let out := PhysicalAmplifiedBinaryVertex.vertexWithCost 0 .mass wire tape
  let some ⟨n,r⟩ := out.1 | throw (IO.userError "positive binary-prepared original source failed")
  let .cut mask := r.output | throw (IO.userError "positive binary-prepared original source returned a non-cut")
  unless n == 3 && mask.toList == [false,true,false] && r.suffix == tape && 0 < out.2 &&
      0 < r.dispatch && 0 < r.readback && 0 < r.roundingAndSelection do
    throw (IO.userError "positive binary-prepared original source changed the cut, tape, or charge")
  IO.println s!"PASS positive original wire through binary preparation, parse {out.2}, dispatch {r.dispatch}, readback {r.readback}, rounding and selection {r.roundingAndSelection}"

def main (args : List String) : IO Unit := do
  compareRound "positive mass" PhysicalVertexRounding.weighted PhysicalBinaryVertexRounding.weighted positive
  compareRound "zero objective" PhysicalVertexRounding.weighted PhysicalBinaryVertexRounding.weighted
    { positive with costs := #v[Code.zero,Code.zero,Code.zero] }
  compareRound "heavy vertex" PhysicalVertexRounding.size PhysicalBinaryVertexRounding.size positive
  let wire := PhysicalSourceDispatch.input original
  let truncated := PhysicalAmplifiedBinaryVertex.vertexWithCost 0 .mass (wire.take 1) []
  unless truncated.1.isNone && 0 < truncated.2 do
    throw (IO.userError "binary-prepared entry lost the counted parse rejection")
  IO.println "PASS binary-prepared original entry rejects truncated source with a measured parse charge"
  if args.contains "--positive-source" then positiveSource
