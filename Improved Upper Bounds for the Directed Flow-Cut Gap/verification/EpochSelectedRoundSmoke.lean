import DirectedFlowCutGap.EpochSelectedRoundProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private abbrev Store := PackedWordPairTable.Prepared
private abbrev allocate := PackedWordPairTable.allocate
private abbrev word := PackedWordPairTable.word

private def storeList {α : Type} (item : α→Store→Store) : List α→Store→Store
  | [], s => allocate .nil s
  | x::xs, s =>
    let tail := storeList item xs s
    let head := item x tail
    allocate (.pair head.root tail.root) head

private def pair {n : ℕ} (p : Pair n) (s : Store) : Store :=
  let a := word p.1.val.bits s
  let b := word p.2.val.bits a
  allocate (.pair a.root b.root) b

private def trials (empty : Bits) : ℕ→Store→Store
  | 0, s => {s with root := empty}
  | m+1, s =>
    let tail := trials empty m s
    allocate (.pair empty tail.root) tail

private def readPair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair a b) => some (a,b)
  | _ => none

private def readLabel (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) := do
  let (a,b) ← readPair heap root
  let u ← PhysicalCoverReader.readWord heap a
  let v ← PhysicalCoverReader.readWord heap b
  pure (value u,value v)

private def lookupCase (wanted : Pair 3) (expected : Bits) : IO Unit := do
  let entries : List (Pair 3×Bits) := [((0,1),[true]),((0,2),[false,true,false]),((2,2),[true,true])]
  let grid := storeList (fun (label,bits) s =>
    let key := pair label s
    let val := word bits key
    allocate (.pair key.root val.root) val) entries PackedWordPairTable.seed
  let key := pair wanted grid
  let tape := [true,false,true]
  let initial : BitState 104 := ⟨key.heap,key.next,⟨key.root,grid.root,[],[]⟩,[],0,tape⟩
  let k := EpochGridLookupProgram.steps wanted entries
  let run := fun fuel => PhysicalCoverExecution.executeCached EpochGridLookupProgram.program fuel initial 0
  let some (out,charge) := run (k+1) | throw (IO.userError "grid lookup missed its paid halt")
  let final := eraseState out
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected &&
      out.pc == 1 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < charge do
    throw (IO.userError "grid lookup mismatched a stored label, word or stop")
  IO.println s!"PASS physical grid lookup ({wanted.1.val}, {wanted.2.val}) returned {expected}, {k} instructions, paid {charge}"

private def selectedCase : IO Unit := do
  let adjacency : PairFlags 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let z : Row 3 := #v[0,0,0]
  let weights : Family 3 := #v[#v[z,z,#v[0,3,0]],#v[z,z,z],#v[#v[8,17,5],z,z]]
  let d : Data 3 := ⟨#v[#v[false,false,true],#v[false,false,false],#v[true,false,false]],#v[true,false,false],weights,1,25⟩
  let seed := PackedWordPairTable.seed
  let labels := storeList word ((List.finRange 3).map fun i => i.val.bits) seed
  let matrix := storeList word (GraphRelaxationRefinement.matrix adjacency) labels
  let graph := allocate (.pair labels.root matrix.root) matrix
  let remaining := storeList word (d.remaining.toList.map Vector.toList) graph
  let cut := word d.cut.toList remaining
  let masks := allocate (.pair remaining.root cut.root) cut
  let words := (RetainedMassTableProgram.pairOrder 3).map fun p => (row weights p).toList.map (fun i => i.bits++[false,false])
  let table := storeList (storeList word) words masks
  let free := allocate (.flag false) table
  let weightContext := allocate (.pair table.root free.root) free
  let packedState := allocate (.pair masks.root weightContext.root) weightContext
  let env := allocate (.pair graph.root packedState.root) packedState
  let vertices := word (3 : ℕ).bits env
  let one := word [true] vertices
  let config := allocate (.pair vertices.root one.root) one
  let L := 3
  let positive : 0<L := by decide
  let grid := word L.bits config
  let cap := trials seed.root 2 grid
  let pairs := storeList pair (RetainedMassTableProgram.pairOrder 3) cap
  let literal := [false,false,false,true,false,false,true,true,false,true]
  let inEpoch : BitState 401 := ⟨pairs.heap,pairs.next,⟨remaining.root,grid.root,cap.root,pairs.root⟩,[],0,literal⟩
  let tries := PhysicalEpochInputProgram.instructionBound 3 L 2
  let epochSteps := PhysicalEpochInputProgram.steps d.remaining positive 2 literal
  let some (epoch,epochCharge) := GuardedReferenceExecution.execute PhysicalEpochInputProgram.program (tries+1) inEpoch 0
    | throw (IO.userError "literal fair tape failed to produce an epoch")
  let ep := eraseState epoch
  let some (order,cellTable) := readPair ep.heap ep.registers.d | throw (IO.userError "missing epoch order and cell table")
  let some (selected,_) := readPair ep.heap order | throw (IO.userError "missing head of the drawn order")
  let expected : Pair 3 := (0,2)
  let exactCells : List (Pair 3×Bits) := [((0,2),[true,false]),((2,0),[false,true])]
  unless readLabel ep.heap selected == some (0,2) && epoch.source == [true,false,true] && epoch.pc == 3 &&
      epoch.stack.isEmpty && epoch.heap.take inEpoch.heap.length == inEpoch.heap &&
      (GuardedReferenceExecution.execute PhysicalEpochInputProgram.program epochSteps inEpoch 0).isNone do
    throw (IO.userError "the drawn demand or literal tape remainder disagreed")
  let input : BitState 2451 := ⟨epoch.heap,epoch.next,⟨selected.bits,cellTable.bits,config.root,env.root⟩,[],0,epoch.source⟩
  let k := EpochSelectedRoundProgram.steps adjacency d expected exactCells words
  let run := fun fuel => PhysicalCoverExecution.executeCached EpochSelectedRoundProgram.program fuel input 0
  let some (out,charge) := run (k+1) | throw (IO.userError s!"the selected epoch round missed its paid halt at {k}")
  let final := eraseState out
  let some (newMasks,newMass) := readPair final.heap final.registers.d
    | throw (IO.userError "the physical round did not return state update fields")
  let some (newRemaining,newCut) := readPair final.heap newMasks | throw (IO.userError "missing updated masks")
  let y := PhysicalSampledRoundProgram.cut (EpochSelectedRoundProgram.enumeration 3) adjacency d expected [true,false]
  let expectedState := (EncodedRoundingState.roundData d expected y).1
  unless PhysicalCoverReader.readList final.heap (PhysicalCoverReader.readWord final.heap) final.heap.length newRemaining ==
      some (expectedState.remaining.toList.map Vector.toList) &&
      PhysicalCoverReader.readWord final.heap newCut == some [true,true,false] && expectedState.current == 5 &&
      PhysicalCoverReader.readWord final.heap newMass == some (5 : ℕ).bits && out.pc == 10 && out.stack.isEmpty &&
      out.source == epoch.source && out.heap.take input.heap.length == input.heap && (run k).isNone && 0 < charge do
    throw (IO.userError "the selected epoch round disagreed on masks, mass, tape or paid halt")
  IO.println s!"PASS actual fair epoch to selected round (0, 2), cell 1, cut [true, true, false], mass 5, 7 requests, epoch paid {epochCharge}, {k} round instructions, round paid {charge}"

def main : IO Unit := do
  lookupCase (0,2) [false,true,false]
  lookupCase (2,2) [true,true]
  lookupCase (1,2) []
  selectedCase
