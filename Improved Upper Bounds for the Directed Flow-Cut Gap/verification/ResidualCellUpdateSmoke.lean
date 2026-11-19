import DirectedFlowCutGap.ResidualCellUpdateProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private abbrev Store := PackedWordPairTable.Prepared

private def storeEdges : List (Bits×Bits) → Store → Store
  | [],p => PackedWordPairTable.allocate .nil p
  | (u,v)::es,p =>
    let tail := storeEdges es p
    let start := PackedWordPairTable.word u tail
    let next := PackedWordPairTable.word v start
    let edge := PackedWordPairTable.allocate (.pair start.root next.root) next
    PackedWordPairTable.allocate (.pair edge.root tail.root) edge

private def check (edges : List (ℕ×ℕ)) (z expected : Int) (keepRoot : Bool) : IO Unit := do
  let amount : BinarySigned.Signed := ⟨z < 0,z.natAbs.bits⟩
  let u := [false,true,false]
  let v := [true,false]
  let es := edges.map fun (a,b) => (a.bits,b.bits)
  let storage := storeEdges es PackedWordPairTable.seed
  let mag := PackedWordPairTable.word amount.magnitude storage
  let sign := PackedWordPairTable.allocate (.flag amount.negative) mag
  let signed := PackedWordPairTable.allocate (.pair mag.root sign.root) sign
  let capacity := PackedWordPairTable.word [true,true,false,false] signed
  let cell := PackedWordPairTable.allocate (.pair signed.root capacity.root) capacity
  let uRoot := PackedWordPairTable.word u cell
  let vRoot := PackedWordPairTable.word v uRoot
  let tape := [true,false,false]
  let initial : BitState 424 := ⟨vRoot.heap,vRoot.next,⟨cell.root,storage.root,uRoot.root,vRoot.root⟩,[],30,tape⟩
  let k := ResidualCellUpdateProgram.steps es u v amount
  let run := fun budget => PhysicalCoverExecution.executeCached ResidualCellUpdateProgram.program budget initial 0
  let some (out,paid) := run (k+1)
    | throw (IO.userError "the residual cell update did not reach its paid stop")
  let stop := eraseState out
  let some (.pair updated cap) := stop.heap[stop.registers.d]?
    | throw (IO.userError "the residual update did not return a cell")
  let some (.pair magnitude negative) := stop.heap[updated]?
    | throw (IO.userError "the residual update did not return a signed amount")
  unless PhysicalCoverReader.readWord stop.heap magnitude == some expected.natAbs.bits &&
      stop.heap[negative]? == some (.flag (expected < 0)) && cap == value capacity.root &&
      (stop.registers.d == value cell.root) == keepRoot && out.pc == 31 && out.stack.isEmpty &&
      out.source == tape && out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "unexpected residual cell, tape, heap prefix or terminal state")
  IO.println s!"PASS physical residual cell {edges}, {z} to {expected}, {k} instructions, paid {paid}"

def main : IO Unit := do
  check [(2,1),(1,0)] (-1) 0 false
  check [(1,2)] 0 (-1) false
  check [(2,0)] 3 3 true
  check [] 0 0 true
  check [(2,1),(1,2)] 7 7 false
