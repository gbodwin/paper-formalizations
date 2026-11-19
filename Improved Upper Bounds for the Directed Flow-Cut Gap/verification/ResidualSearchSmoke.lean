import DirectedFlowCutGap.ResidualSearchProgram
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

private def storeEdge (e : Bits×Bits) (p : Store) : Store :=
  let u := PackedWordPairTable.word e.1 p
  let v := PackedWordPairTable.word e.2 u
  PackedWordPairTable.allocate (.pair u.root v.root) v

private def readEdge (h : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) := do
  let some (.pair u v) := h[root]? | none
  let a ← PhysicalCoverReader.readWord h u
  let b ← PhysicalCoverReader.readWord h v
  pure (value a,value b)

private def check (xs : List (List Entry)) (expected : List (ℕ×ℕ)) : IO Unit := do
  let label := fun i : Fin 3 => i.val.bits++[false]
  let vs := (List.finRange 3).map label
  let pairs := (ResidualSearchData.pairs 3).map (SupportSearchEncoding.encodeEdge label)
  let flow := storeList (storeList storeEntry) xs PackedWordPairTable.seed
  let vertices := storeList PackedWordPairTable.word vs flow
  let edges := storeList storeEdge pairs vertices
  let source := PackedWordPairTable.word (label 0) edges
  let target := PackedWordPairTable.word (label 2) source
  let context := PackedWordPairTable.allocate (.pair target.root edges.root) target
  let tape := [true,false,true]
  let initial : BitState 388 :=
    ⟨context.heap,context.next,⟨flow.root,vertices.root,source.root,context.root⟩,[],0,tape⟩
  let count := ResidualSearchProgram.steps xs vs pairs (label 0) (label 2)
  let run := fun budget => PhysicalCoverExecution.executeCached ResidualSearchProgram.program budget initial 0
  let some (out,paid) := run (count+1)
    | throw (IO.userError "the residual search did not reach its paid stop")
  let stop := eraseState out
  let path := PhysicalCoverReader.readList stop.heap (readEdge stop.heap) stop.heap.length stop.registers.d
  unless path == some expected && out.pc == 5 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run count).isNone && 0 < paid do
    throw (IO.userError "unexpected residual path or terminal state")
  IO.println s!"PASS physical residual path {expected}, {count} successful instructions, paid {paid}"

private def cell (z : Int) (cap : ℕ) : Entry :=
  (⟨z < 0,z.natAbs.bits⟩,cap.bits++[false])

def main : IO Unit := do
  let z := cell 0 0
  let free := cell 0 2
  let full := cell 2 2
  let reverse := cell (-2) 0
  check [[z,free,z],[z,z,free],[z,z,z]] [(0,1),(1,2)]
  check [[z,full,z],[reverse,z,full],[z,reverse,z]] []
  check [[z,full,cell 0 1],[reverse,z,full],[z,reverse,z]] [(0,2)]
