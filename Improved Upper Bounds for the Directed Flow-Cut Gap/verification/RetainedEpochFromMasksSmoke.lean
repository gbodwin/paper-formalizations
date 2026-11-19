import DirectedFlowCutGap.RetainedEpochFromMasks
import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.PhysicalCoverReader

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private def maskTable : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], s => PackedWordPairTable.allocate .nil s
  | x::xs,s =>
    let tail := maskTable xs s
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

private def check {n : ℕ} (description : String) (a : PairFlags n) (tape : Bits)
    (expected : Option (List (ℕ×Bool) × Bits × ℕ)) : IO Unit := do
  let grid := 3
  let fuel := 2
  let seed := PackedWordPairTable.seed
  let rows := maskTable (a.toList.map Vector.toList) seed
  let level := PackedWordPairTable.word grid.bits rows
  let trials := spine seed.root fuel level
  let initial : BitState 174 := ⟨trials.heap,trials.next,⟨rows.root,level.root,trials.root,[]⟩,[],0,tape⟩
  let budget := RetainedEpochFromMasks.instructionBound n grid fuel
  let p := RetainedEpochFromMasks.program
  let total := RetainedEpochFromMasks.steps a (show 0<grid by decide) fuel tape
  let tree := LazyFairBitTrees.lower fuel (RetainedDrawTrees.sampleTape (show 0<grid by decide) a)
  let logical := (EncodedSolverBits.run tree tape).map (fun (result,rest,reads) =>
    (PhysicalEpochDraws.values grid (Fintype.card ↥(remainingSet a)) result,rest,reads))
  let model := expected.map (fun (result,rest,reads) => (result.map Prod.fst,rest,reads))
  unless logical == model do
    throw (IO.userError s!"retained tape unexpectedly disagreed for {description}")
  match GuardedReferenceExecution.execute p (budget+1) initial 0, expected with
  | none, none => IO.println s!"PASS physical epoch from mask {description}, empty input result"
  | some (out,paid), some (expected,rest,reads) =>
    let heap := eraseHeap out.heap
    let seen := PhysicalCoverReader.readList heap (read heap) heap.length (value out.registers.d)
    let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds a (show 0<grid by decide)) tape
    unless seen == some expected && out.source == rest && observed.requests == tape.take reads &&
        out.pc == RetainedEpochFromMasks.drawLabel 15 && out.stack.isEmpty &&
        out.heap.take initial.heap.length == initial.heap &&
        (GuardedReferenceExecution.execute p total initial 0).isNone && 0 < paid do
      throw (IO.userError s!"physical epoch from mask disagreed for {description}")
    IO.println s!"PASS physical epoch from mask {description}, {reads} requests, {total} instructions, paid {paid}"
  | _, _ => throw (IO.userError s!"physical epoch from mask ended incorrectly for {description}")

def main : IO Unit := do
  let tape := [true,false,true,false,true,true,false,true,true,true,true,true,false,true]
  let a : PairFlags 2 := #v[#v[false,true],#v[true,false]]
  let z : PairFlags 2 := #v[#v[false,false],#v[false,false]]
  check "two active pairs" a tape (some ([(1,false),(0,false),(2,false),(0,true)],[false,true],12))
  check "short fourth draw" a (tape.take 11) none
  check "no active pairs" z [true,false] (some ([],[true,false],0))
