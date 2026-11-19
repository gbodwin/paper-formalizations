import DirectedFlowCutGap.ResidualTableUpdateProgram
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

private def readEntry (heap : NaturalHeap) (r : ℕ) : Option (Int×ℕ) := do
  let some (.pair signed cap) := heap[r]? | none
  let some (.pair magnitude sign) := heap[signed]? | none
  let some (.flag negative) := heap[sign]? | none
  let bits ← PhysicalCoverReader.readWord heap magnitude
  let z := BinarySigned.decode ⟨negative,bits⟩
  if bits == z.natAbs.bits && negative == (z < 0) then pure (z,cap) else none

private def readTable (heap : NaturalHeap) (r : ℕ) : Option (List (List (Int×ℕ))) :=
  let row := PhysicalCoverReader.readList heap (readEntry heap) heap.length
  PhysicalCoverReader.readList heap row heap.length r

private def check (xs : List (List Entry)) (us vs : List ℕ) (edges : List (ℕ×ℕ))
    (expected : List (List Int)) : IO Unit := do
  let words := fun labels : List ℕ => labels.map fun k => k.bits++[false]
  let rows := words us
  let columns := words vs
  let es := edges.map fun (u,v) => (u.bits,v.bits)
  let flow := storeList (storeList storeEntry) xs PackedWordPairTable.seed
  let rowRoot := storeList PackedWordPairTable.word rows flow
  let colRoot := storeList PackedWordPairTable.word columns rowRoot
  let path := storeList storeEdge es colRoot
  let ctx := PackedWordPairTable.allocate (.pair path.root colRoot.root) path
  let tape := [true,false,true]
  let initial : BitState 480 :=
    ⟨ctx.heap,ctx.next,⟨flow.root,rowRoot.root,ctx.root,[]⟩,[],26,tape⟩
  let count := ResidualTableUpdateProgram.steps es columns xs rows+1
  let run := fun budget => PhysicalCoverExecution.executeCached ResidualTableUpdateProgram.program budget initial 0
  let some (out,paid) := run (count+1)
    | throw (IO.userError "the residual table update did not reach its paid stop")
  let final := eraseState out
  let some old := readTable (eraseHeap initial.heap) (value flow.root)
    | throw (IO.userError "the input amount table could not be read")
  let some new := readTable final.heap final.registers.d
    | throw (IO.userError "the updated amount table could not be read")
  unless new.map (List.map Prod.fst) == expected &&
      new.map (List.map Prod.snd) == old.map (List.map Prod.snd) &&
      out.pc == 27 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run count).isNone && 0 < paid do
    throw (IO.userError "the updated table, capacities or terminal state disagreed")
  IO.println s!"PASS physical residual table {edges}, amounts {expected}, {count} instructions, paid {paid}"

private def entry (z : Int) (capacity : ℕ) : Entry :=
  (⟨z < 0,z.natAbs.bits⟩,capacity.bits++[false])

def main : IO Unit := do
  let z := entry 0 0
  let free := entry 0 2
  check [[z,free,z],[z,z,free],[z,z,z]] [0,1,2] [0,1,2] [(0,1),(1,2)]
    [[0,1,0],[-1,0,1],[0,-1,0]]
  check [[z,entry (-1) 3],[entry 1 1,z]] [0,1] [0,1] [(0,1)] [[0,0],[0,0]]
  check [[],[]] [0,1] [] [] [[],[]]
  check [] [] [] [] []
