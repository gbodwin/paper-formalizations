import DirectedFlowCutGap.EpochMaterializeProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation
open PhysicalBoundedDrawProgram (Outcome)

private def storeKeys : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared × List Bits
  | [], heap => (PackedWordPairTable.allocate .nil heap,[])
  | w::ws, heap =>
    let (tail,labels) := storeKeys ws heap
    let word := PackedWordPairTable.word w tail
    (PackedWordPairTable.allocate (.pair word.root tail.root) word,word.root::labels)

private def storeDraws : List Outcome → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], heap => PackedWordPairTable.allocate .nil heap
  | result::rest, heap =>
    let tail := storeDraws rest heap
    let index := PackedWordPairTable.word result.index tail
    let flag := PackedWordPairTable.allocate (.flag result.failed) index
    let first := PackedWordPairTable.allocate (.pair index.root flag.root) flag
    PackedWordPairTable.allocate (.pair first.root tail.root) first

private def readPair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair p q) => some (p,q)
  | _ => none

private def readGrid (heap : NaturalHeap) (root : ℕ) : Option (ℕ×Bits) := do
  let (key,word) ← readPair heap root
  let bits ← PhysicalCoverReader.readWord heap word
  pure (key,bits)

private def check (keys : List Bits) (perm grid : List Outcome) (expected : List ℕ) : IO Unit := do
  let (input,addresses) := storeKeys keys PackedWordPairTable.seed
  let draws := storeDraws (perm++grid) input
  let tape := [true,false,true]
  let initial : BitState 145 := ⟨draws.heap,draws.next,⟨input.root,draws.root,[],[]⟩,[],0,tape⟩
  let refs := addresses.map value
  let k := EpochMaterializeProgram.steps perm refs.length
  let run := fun fuel => PhysicalCoverExecution.executeCached EpochMaterializeProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "epoch input materialization missed its paid halt")
  let final := eraseState out
  let some (order,cells) := readPair final.heap final.registers.d | throw (IO.userError "missing permuted order or grid table")
  let some expectedRefs := expected.mapM (refs[·]?) | throw (IO.userError "invalid expected permutation")
  unless PhysicalCoverReader.readList final.heap some final.heap.length order == some expectedRefs &&
      PhysicalCoverReader.readList final.heap (readGrid final.heap) final.heap.length cells == some (refs.zip (grid.map Outcome.index)) &&
      out.pc == 4 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "the permutation or original-label grid assignment disagreed")
  IO.println s!"PASS physical epoch permutation {expected} and original-label cells {(grid.map fun d => value d.index)}, {k} instructions, paid {paid}"

private def draw (index : Bits) (failed : Bool := false) : Outcome := ⟨index,failed,[],[]⟩

def main : IO Unit := do
  check [] [] [] []
  check [[true]] [draw [] true] [draw [true,false,true,false]] [0]
  check [[true],[],[false,true]]
    [draw [false,true,false],draw [true,false],draw [] true] [draw [true],draw [true,true],draw []] [2,0,1]
