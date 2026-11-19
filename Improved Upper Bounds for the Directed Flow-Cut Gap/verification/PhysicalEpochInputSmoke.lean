import DirectedFlowCutGap.PhysicalEpochInputProgram
import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.PhysicalCoverReader

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation RetainedGridState

private def maskRows : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], heap => PackedWordPairTable.allocate .nil heap
  | b::bs, heap =>
    let tail := maskRows bs heap
    let row := PackedWordPairTable.word b tail
    PackedWordPairTable.allocate (.pair row.root tail.root) row

private def storePairs : List (ℕ×ℕ) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], heap => PackedWordPairTable.allocate .nil heap
  | (a,b)::rest, heap =>
    let tail := storePairs rest heap
    let x := PackedWordPairTable.word a.bits tail
    let y := PackedWordPairTable.word b.bits x
    let entry := PackedWordPairTable.allocate (.pair x.root y.root) y
    PackedWordPairTable.allocate (.pair entry.root tail.root) entry

private def spine (nilRoot : Bits) : ℕ → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | 0, heap => {heap with root:=nilRoot}
  | n+1, heap =>
    let tail := spine nilRoot n heap
    PackedWordPairTable.allocate (.pair nilRoot tail.root) tail

private def readPair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair a b) => some (a,b)
  | _ => none

private def readLabel (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) := do
  let (a,b) ← readPair heap root
  let x ← PhysicalCoverReader.readWord heap a
  let y ← PhysicalCoverReader.readWord heap b
  pure (value x,value y)

private def readCell (heap : NaturalHeap) (root : ℕ) : Option ((ℕ×ℕ)×ℕ) := do
  let (a,b) ← readPair heap root
  let key ← readLabel heap a
  let bits ← PhysicalCoverReader.readWord heap b
  pure (key,value bits)

private def check (a : PairFlags 2) (tape : Bits) (fuel : ℕ)
    (expected : Option (List (ℕ×ℕ) × List ((ℕ×ℕ)×ℕ) × Bits × ℕ)) : IO Unit := do
  let grid := 3
  let positive : 0<grid := by decide
  let seed := PackedWordPairTable.seed
  let rows := maskRows (a.toList.map Vector.toList) seed
  let level := PackedWordPairTable.word grid.bits rows
  let trials := spine seed.root fuel level
  let pairs := storePairs ((List.range 2).product (List.range 2)) trials
  let initial : BitState 401 := ⟨pairs.heap,pairs.next,⟨rows.root,level.root,trials.root,pairs.root⟩,[],0,tape⟩
  let budget := PhysicalEpochInputProgram.instructionBound 2 grid fuel
  let k := PhysicalEpochInputProgram.steps a positive fuel tape
  let tree := LazyFairBitTrees.lower fuel (RetainedDrawTrees.sampleTape positive a)
  let logical := (EncodedSolverBits.run tree tape).map (fun (t,rest,reads) =>
    let input := RetainedTapeInput.materialize positive a t
    let order := input.order.map fun (u,v) => (u.val,v.val)
    let cells := (RetainedTapeInput.activeList a).map fun p => ((p.1.val,p.2.val),(input.cell p).val)
    (order,cells,rest,reads))
  unless logical == expected do
    throw (IO.userError s!"retained epoch input changed on literal tape, expected {expected}, got {logical}")
  let run := fun limit => GuardedReferenceExecution.execute PhysicalEpochInputProgram.program limit initial 0
  match run (budget+1),expected with
  | none,none => IO.println "PASS physical epoch input rejected a short fair tape"
  | some (out,paid),some (order,cells,rest,reads) =>
    let final := eraseState out
    let some (orderRoot,cellRoot) := readPair final.heap final.registers.d
      | throw (IO.userError "the epoch output pair was unreadable")
    let permutation := PhysicalCoverReader.readList final.heap (readLabel final.heap) final.heap.length orderRoot
    let cellTable := PhysicalCoverReader.readList final.heap (readCell final.heap) final.heap.length cellRoot
    let observed := PhysicalDrawSequenceProgram.batch fuel (RetainedEpochFromMasks.bounds a positive) tape
    unless permutation == some order && cellTable == some cells &&
        out.pc == 3 && out.stack.isEmpty && out.source == rest && observed.requests == tape.take reads &&
        out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
      throw (IO.userError "materialized epoch did not match the literal tape, original labels or charged halt")
    IO.println s!"PASS physical epoch input order {order}, cells {cells}, {reads} requests, {k} instructions, paid {paid}"
  | _,_ => throw (IO.userError "physical epoch input stopped unexpectedly")

def main : IO Unit := do
  let a : PairFlags 2 := #v[#v[false,true],#v[true,false]]
  let noneActive : PairFlags 2 := #v[#v[false,false],#v[false,false]]
  let tape := [true,false,false,false,true,true,false,true,true,false]
  check a tape 2 (some ([(1,0),(0,1)],[((0,1),2),((1,0),1)],[true,true,false],7))
  check a (tape.take 6) 2 none
  check a [true,false] 0 (some ([(0,1),(1,0)],[((0,1),0),((1,0),0)],[true,false],0))
  check noneActive [false,true] 2 (some ([],[],[false,true],0))
