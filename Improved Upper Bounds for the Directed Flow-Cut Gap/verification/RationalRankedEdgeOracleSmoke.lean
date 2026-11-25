import DirectedFlowCutGap.RationalRankedEdgeWire

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero)
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open RationalExactEdgeOracle (Edge)

private def denominatorTwo : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩
private def denominatorThree : BinaryRational.Fraction := ⟨[true],[true,true],by decide⟩

private def layered : IO Unit := do
  let layer (v : Fin 6) := v.val / 2
  let A : Adjacency 6 := Vector.ofFn fun s => Vector.ofFn fun t =>
    (layer s == layer t && s != t) || layer s + 1 == layer t
  let w : Weights 6 := Vector.ofFn fun s => Vector.ofFn fun t =>
    if layer s + 1 = layer t then denominatorTwo else zero
  let first := (RationalExactEdgeOracle.arcSet A).filter fun e => layer e.1 = 0 ∧ layer e.2 = 1
  let second := (RationalExactEdgeOracle.arcSet A).filter fun e => layer e.1 = 1 ∧ layer e.2 = 2
  let price (a b : ℚ≥0) (e : Edge 6) :=
    if e ∈ first then a else if e ∈ second then b else 100
  let tape := [true,false,true]
  unless RationalInstanceEdgeFactor.endpointCap A w == 4 &&
      RationalRankedEdgeOracle.recognizes A w &&
      RationalTwoLayerCertificate.assign A w == #v[0,0,1,1,2,2] &&
      decide (first.card = 4 ∧ second.card = 4 ∧
        RationalRankedEdgeOracle.priceCut A w (price 1 8) = some first ∧
        RationalRankedEdgeOracle.priceCut A w (price 8 1) = some second ∧
        RationalRankedEdgeOracle.family A w = some [first ∪ second] ∧
        RationalRankedEdgeOracle.draw A w tape = some (first ∪ second,tape)) do
    throw (IO.userError "the dense layered graph failed rank, price, family or tape verification")
  IO.println "PASS four positive sources and destinations, opposite prices choose opposite layers, eight-arc singleton cut reads zero bits"
  let source := MeasuredRescaleWire.encode A w
  let some ⟨6,some (cut,rest)⟩ := RationalRankedEdgeWire.draw source tape |
    throw (IO.userError "the dense layered graph failed binary decoding or rank validation")
  unless decide (cut = first ∪ second ∧ rest = tape) do
    throw (IO.userError "the binary sampler changed the cut or tape")
  IO.println s!"PASS the {source.length}-bit layered frame returned the same eight-arc cut and untouched tape"

private def invalid : IO Unit := do
  let A : Adjacency 4 :=
    #v[#v[false,true,false,false],#v[false,false,true,false],
       #v[false,false,false,true],#v[false,false,false,false]]
  let w : Weights 4 :=
    #v[#v[zero,denominatorThree,zero,zero],#v[zero,zero,denominatorThree,zero],
       #v[zero,zero,zero,denominatorThree],#v[zero,zero,zero,zero]]
  unless !RationalRankedEdgeOracle.recognizes A w &&
      (RationalRankedEdgeOracle.priceCut A w (fun _ => 1)).isNone &&
      (RationalRankedEdgeOracle.draw A w [true]).isNone do
    throw (IO.userError "the rank guard admitted three positive arcs on one path")
  IO.println "PASS the rank guard rejects a three-positive-arc path of length one"
  let source := MeasuredRescaleWire.encode A w
  let some ⟨4,none⟩ := RationalRankedEdgeWire.draw source [true] |
    throw (IO.userError "the valid unrankable frame was mistaken for a malformed frame or a cut")
  let explicit : EncodedEdgeInput.Input 4 := ⟨A,[(0,3)],Vector.replicate 16 zero⟩
  unless (RationalRankedEdgeWire.draw (source ++ [false]) [true]).isNone &&
      (RationalRankedEdgeWire.draw (EncodedEdgeInput.encode explicit) [true]).isNone do
    throw (IO.userError "the ranked wire accepted trailing bits or explicit demands")
  IO.println "PASS the binary entry distinguishes a valid unrankable graph from trailing bits and explicit demands"

private def zeroFactor : IO Unit := do
  let A : Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let w : Weights 2 := #v[#v[zero,denominatorTwo],#v[zero,zero]]
  unless RationalRankedEdgeOracle.recognizes A w &&
      decide (RationalRankedEdgeOracle.priceCut A w (fun _ => 1) = some ∅ ∧
        RationalRankedEdgeOracle.draw A w [false,true] = some (∅,[false,true])) do
    throw (IO.userError "the zero-factor case used a nonempty cut or read the tape")
  IO.println "PASS the recognized subunit graph returns the exact zero-factor empty cut with the entire tape"

def main : IO Unit := do
  layered
  invalid
  zeroFactor
