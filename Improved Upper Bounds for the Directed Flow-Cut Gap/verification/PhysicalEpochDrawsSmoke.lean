import DirectedFlowCutGap.PhysicalEpochDraws
import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.PhysicalCoverReader

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def wordTable : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], s => PackedWordPairTable.allocate .nil s
  | x::xs,s =>
    let tail := wordTable xs s
    let head := PackedWordPairTable.word x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def spine (nilRoot : Bits) : ℕ → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | 0,s => { s with root := nilRoot }
  | k+1,s =>
    let tail := spine nilRoot k s
    PackedWordPairTable.allocate (.pair nilRoot tail.root) tail

private def read (heap : NaturalHeap) (r : ℕ) : Option (ℕ × Bool) := do
  let some (.pair word tag) := heap[r]? | none
  let bits ← PhysicalCoverReader.readWord heap word
  let some (.flag failure) := heap[tag]? | none
  pure (value bits,failure)

private def check (description : String) (m : ℕ) (tape : Bits)
    (expected : Option (List (ℕ×Bool) × Bits × ℕ)) : IO Unit := do
  let grid := 3
  let fuel := 2
  let caps := PhysicalEpochDraws.epochBounds grid (by decide) m
  let seed := PackedWordPairTable.seed
  let words := wordTable caps seed
  let trials := spine seed.root fuel words
  let initial : BitState 94 := ⟨trials.heap,trials.next,⟨words.root,trials.root,[],[]⟩,[],14,tape⟩
  let budget := PhysicalDrawSequenceProgram.instructionBound 2 fuel caps.length
  let p := PhysicalDrawSequenceProgram.program
  let total := PhysicalDrawSequenceProgram.steps fuel caps tape + 1
  let tree := LazyFairBitTrees.lower fuel (RetainedDrawTrees.tape grid (by decide) m)
  let logical := (EncodedSolverBits.run tree tape).map (fun (result,rest,reads) =>
    (PhysicalEpochDraws.values grid m result,rest,reads))
  let model := expected.map (fun (result,rest,reads) => (result.map Prod.fst,rest,reads))
  unless logical == model do
    throw (IO.userError s!"retained tape tree unexpectedly disagreed for {description}")
  match GuardedReferenceExecution.execute p (budget+1) initial 0, expected with
  | none, none => IO.println s!"PASS physical epoch {description}, empty input result"
  | some (out,paid), some (expected,rest,reads) =>
    let heap := eraseHeap out.heap
    let seen := PhysicalCoverReader.readList heap (read heap) heap.length (value out.registers.d)
    let observed := PhysicalDrawSequenceProgram.batch fuel caps tape
    unless seen == some expected && out.source == rest && observed.requests == tape.take reads &&
        out.pc == 15 && out.stack.isEmpty && out.heap.take initial.heap.length == initial.heap &&
        (GuardedReferenceExecution.execute p total initial 0).isNone && 0 < paid do
      throw (IO.userError s!"physical epoch disagreed for {description}")
    IO.println s!"PASS physical epoch {description}, {reads} requests, {total} instructions, paid {paid}"
  | _, _ => throw (IO.userError s!"physical epoch ended incorrectly for {description}")

def main : IO Unit := do
  let tape := [true,false,true,false,true,true,false,true,true,true,true,true,false,true]
  check "permutation and cells" 2 tape (some ([(1,false),(0,false),(2,false),(0,true)],[false,true],12))
  check "short fourth draw" 2 (tape.take 11) none
  check "empty active set" 0 [true,false] (some ([],[true,false],0))
