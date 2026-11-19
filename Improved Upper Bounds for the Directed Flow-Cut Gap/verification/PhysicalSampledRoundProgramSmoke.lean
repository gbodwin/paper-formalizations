import DirectedFlowCutGap.PhysicalSampledRoundProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState
open IntegralNetworkFlow

private abbrev Store := PackedWordPairTable.Prepared

private def storeList {α : Type} (item : α → Store → Store) : List α → Store → Store
  | [], p => PackedWordPairTable.allocate .nil p
  | x :: xs, p =>
    let tail := storeList item xs p
    let head := item x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def index (emptyRoot : Bits) : ℕ → Store → Store
  | 0, s => { s with root := emptyRoot }
  | k+1, s =>
    let tail := index emptyRoot k s
    PackedWordPairTable.allocate (.pair emptyRoot tail.root) tail

def main : IO Unit := do
  let adjacency : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let order := ResidualSearch.Enumeration.fin 3
  let label := fun i : Fin 3 => i.val.bits ++ [false]
  let z : Row 3 := #v[0,0,0]
  let weights : Family 3 := #v[#v[z,z,#v[0,3,0]],#v[z,z,z],#v[#v[8,17,5],z,z]]
  let d : Data 3 := ⟨#v[#v[false,false,true],#v[false,false,false],#v[true,false,false]],#v[true,false,false],weights,1,25⟩
  let selected : Pair 3 := (0,2)
  let selectedRow := row weights selected
  let rows := (IntegerDistanceFromPhysical.encodedRow selectedRow).toList
  let padded := fun i : ℕ => i.bits ++ [false]
  let level := padded 1
  let costs := PackedWordPairTable.construct (rows.map fun f => (f.num,f.den))
  let matrix := storeList PackedWordPairTable.word (GraphRelaxationRefinement.matrix adjacency) costs
  let vertices := storeList PackedWordPairTable.word (order.vertices.map label) matrix
  let source := PackedWordPairTable.word (label selected.1) vertices
  let levelRoot := PackedWordPairTable.word level source
  let costContext := PackedWordPairTable.allocate (.pair costs.root source.root) levelRoot
  let matrixContext := PackedWordPairTable.allocate (.pair matrix.root costContext.root) costContext
  let bundle := PackedWordPairTable.allocate (.pair vertices.root matrixContext.root) matrixContext
  let sourceLevel := PackedWordPairTable.allocate (.pair source.root levelRoot.root) bundle
  let scanContext := PackedWordPairTable.allocate (.pair bundle.root sourceLevel.root) sourceLevel
  let targetFields := IntegerLevelCutProgram.fields selectedRow label (List.finRange 3)
  let targets := targetFields.foldr PackedWordPairTable.prepend (PackedWordPairTable.allocate .nil scanContext)
  let active := storeList PackedWordPairTable.word (d.remaining.toList.map Vector.toList) targets
  let priorCut := PackedWordPairTable.word d.cut.toList active
  let masks := PackedWordPairTable.allocate (.pair active.root priorCut.root) priorCut
  let emptyList := PackedWordPairTable.allocate .nil masks
  let si := index emptyList.root selected.1.val emptyList
  let ti := index emptyList.root selected.2.val si
  let indices := PackedWordPairTable.allocate (.pair si.root ti.root) ti
  let words := (RetainedMassTableProgram.pairOrder 3).map fun p => (row weights p).toList.map padded
  let table := storeList (storeList PackedWordPairTable.word) words indices
  let free := PackedWordPairTable.allocate (.flag false) table
  let weightsAndFree := PackedWordPairTable.allocate (.pair table.root free.root) free
  let rest := PackedWordPairTable.allocate (.pair indices.root weightsAndFree.root) weightsAndFree
  let args := PackedWordPairTable.allocate (.pair masks.root rest.root) rest
  let tape := [true,false,false,true]
  let initial : BitState 1982 := ⟨args.heap,args.next,⟨vertices.root,targets.root,scanContext.root,args.root⟩,[],0,tape⟩
  let k := PhysicalSampledRoundProgram.steps order adjacency d selected (label selected.1) label level words
  let run := fun fuel => PhysicalCoverExecution.executeCached PhysicalSampledRoundProgram.program fuel initial 0
  let some (out, paid) := run (k+1)
    | throw (IO.userError "the sampled round did not reach its paid stop")
  let stop := eraseState out
  let some (.pair outMasks mass) := stop.heap[stop.registers.d]?
    | throw (IO.userError "the sampled round did not return its masks and mass")
  let some (.pair outRemaining outCut) := stop.heap[outMasks]?
    | throw (IO.userError "the sampled round did not return a demand matrix and cut")
  let y := PhysicalSampledRoundProgram.cut order adjacency d selected level
  let expected := (EncodedRoundingState.roundData d selected y).1
  let demands := PhysicalCoverReader.readList stop.heap (PhysicalCoverReader.readWord stop.heap) stop.heap.length outRemaining
  let seenCut := PhysicalCoverReader.readWord stop.heap outCut
  let seenMass := PhysicalCoverReader.readWord stop.heap mass
  unless y.toList == [false,true,false] && expected.current == 5 &&
      demands == some (expected.remaining.toList.map Vector.toList) && seenCut == some [true,true,false] &&
      seenMass == some expected.current.bits && out.pc == PhysicalSampledRoundProgram.updateLabel 5 &&
      out.stack.isEmpty && out.source == tape && out.heap.take args.heap.length == args.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "the physical sampled round returned unexpected fields")
  IO.println s!"PASS physical midpoint and state update, mass 5, {k} successful instructions, paid {paid}"
