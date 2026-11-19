import DirectedFlowCutGap.ResidualMatrixProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation
open ResidualRowProgram (Entry)

private abbrev Store := PackedWordPairTable.Prepared

private def storeList {α : Type} (item : α → Store → Store) : List α → Store → Store
  | [], p => PackedWordPairTable.allocate .nil p
  | x :: xs, p =>
    let tail := storeList item xs p
    let head := item x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def storeEntry (x : Entry) (p : Store) : Store :=
  let mag := PackedWordPairTable.word x.1.magnitude p
  let sign := PackedWordPairTable.allocate (.flag x.1.negative) mag
  let amount := PackedWordPairTable.allocate (.pair mag.root sign.root) sign
  let capacity := PackedWordPairTable.word x.2 amount
  PackedWordPairTable.allocate (.pair amount.root capacity.root) capacity

private def check (xs : List (List Entry)) (expected : List Bits) : IO Unit := do
  let input := storeList (storeList storeEntry) xs PackedWordPairTable.seed
  let tape := [true,false,true]
  let initial : BitState 92 := ⟨input.heap,input.next,⟨input.root,[],[],[]⟩,[],14,tape⟩
  let k := ResidualMatrixProgram.steps xs+1
  let run := fun budget => PhysicalCoverExecution.executeCached ResidualMatrixProgram.program budget initial 0
  let some (out,paid) := run (k+1)
    | throw (IO.userError "the residual matrix scan did not reach its paid stop")
  let stop := eraseState out
  let matrix := PhysicalCoverReader.readList stop.heap (PhysicalCoverReader.readWord stop.heap)
    stop.heap.length stop.registers.d
  unless matrix == some expected && out.pc == 15 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "the residual matrix disagreed or did not preserve the input state")
  IO.println s!"PASS fixed residual matrix {expected}, {k} successful instructions, paid {paid}"

private def entry (negative : Bool) (magnitude : ℕ) (capacity : Bits) : Entry :=
  (⟨negative,magnitude.bits⟩,capacity)

def main : IO Unit := do
  let zero := entry false 0 []
  let reverse := entry true 2 []
  let spare := entry false 2 [false,false,true,false]
  let saturated := entry false 2 [false,true]
  let unused := entry false 0 [true,false]
  check [[zero,spare,unused],[reverse,zero,saturated],[zero,reverse,zero]]
    [[false,true,true],[true,false,false],[false,true,false]]
  check [[],[]] [[],[]]
  check [] []
