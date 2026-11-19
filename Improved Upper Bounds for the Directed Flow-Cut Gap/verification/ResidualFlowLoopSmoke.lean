import DirectedFlowCutGap.ResidualMaxFlowCutProgram
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

private def readEdge (heap : NaturalHeap) (r : ℕ) : Option (ℕ×ℕ) := do
  let some (.pair a b) := heap[r]? | none
  let u ← PhysicalCoverReader.readWord heap a
  let v ← PhysicalCoverReader.readWord heap b
  pure (value u,value v)

private def loopSteps (vs : List Bits) (edges : List (Bits×Bits)) (source target : Bits)
    (xs : List (List Entry)) (fuel : ℕ) : Option (ℕ×ℕ) := do
  let path := ResidualFlowStepProgram.path xs vs edges source target
  let count := ResidualFlowStepProgram.steps xs vs edges source target
  if path.isEmpty then
    pure (count+12,0)
  else
    match fuel with
    | 0 => none
    | k+1 =>
      let next := ResidualFlowStepProgram.outputTable xs vs path
      let (later,rounds) ← loopSteps vs edges source target next k
      pure (count+13+later,rounds+1)

private def check {n : ℕ} (s t : Fin n) (xs : List (List Entry)) (fuel : ℕ)
    (first : List (ℕ×ℕ)) (expected : List (List Int)) (rounds : ℕ) (expectedCut : Bits) : IO Unit := do
  let label := fun i : Fin n => i.val.bits++[false]
  let vs := ResidualFlowStepProgram.wordTable label
  let pairs := ResidualFlowStepProgram.pairTable label
  let flow := storeList (storeList storeEntry) xs PackedWordPairTable.seed
  let vertices := storeList PackedWordPairTable.word vs flow
  let edges := storeList storeEdge pairs vertices
  let source := PackedWordPairTable.word (label s) edges
  let target := PackedWordPairTable.word (label t) source
  let ends := PackedWordPairTable.allocate (.pair target.root edges.root) target
  let sourceAndEnds := PackedWordPairTable.allocate (.pair source.root ends.root) ends
  let network := PackedWordPairTable.allocate (.pair vertices.root sourceAndEnds.root) sourceAndEnds
  let limit := storeList (fun _ (p : Store) => {p with root := PackedWordPairTable.seed.root})
    (List.replicate fuel ()) network
  let tape := [false,true,false]
  let startStep : BitState 884 :=
    ⟨limit.heap,limit.next,⟨flow.root,vertices.root,source.root,ends.root⟩,[],0,tape⟩
  let count := ResidualFlowStepProgram.steps xs vs pairs (label s) (label t)
  let stepRun := fun cap => PhysicalCoverExecution.executeCached ResidualFlowStepProgram.program cap startStep 0
  let some (stepEnd,paidStep) := stepRun (count+1)
    | throw (IO.userError "the fused residual step did not reach its paid stop")
  let phase := eraseState stepEnd
  let some (.pair next found) := phase.heap[phase.registers.d]?
    | throw (IO.userError "the fused residual step did not return the table and path")
  let path := PhysicalCoverReader.readList phase.heap (readEdge phase.heap) phase.heap.length found
  unless path == some first && (next == value flow.root) == first.isEmpty &&
      stepEnd.pc == 5 && stepEnd.stack.isEmpty && stepEnd.source == tape &&
      stepEnd.heap.take startStep.heap.length == startStep.heap && (stepRun count).isNone && 0 < paidStep do
    throw (IO.userError "the fused residual step produced unexpected output")
  IO.println s!"PASS fused residual step {first}, {count} instructions, paid {paidStep}"
  let some (total,referenceRounds) := loopSteps vs pairs (label s) (label t) xs fuel
    | throw (IO.userError "the fixture's iteration budget ran out")
  let iterations := total+1
  let initial : BitState 908 :=
    ⟨limit.heap,limit.next,⟨flow.root,network.root,limit.root,[]⟩,[],20,tape⟩
  let loop := fun cap => PhysicalCoverExecution.executeCached ResidualFlowLoopProgram.program cap initial 0
  let some (out,paid) := loop (iterations+1)
    | throw (IO.userError "the residual loop did not reach its paid stop")
  let final := eraseState out
  let some old := readTable (eraseHeap initial.heap) (value flow.root)
    | throw (IO.userError "the input flow table was unreadable")
  let some new := readTable final.heap final.registers.d
    | throw (IO.userError "the terminal flow table was unreadable")
  unless referenceRounds == rounds && new.map (List.map Prod.fst) == expected &&
      new.map (List.map Prod.snd) == old.map (List.map Prod.snd) &&
      out.pc == 21 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (loop iterations).isNone && 0 < paid do
    throw (IO.userError "the terminal flow, capacities or paid stop disagreed")
  IO.println s!"PASS physical residual loop {rounds} augmentations, amounts {expected}, {iterations} instructions, paid {paid}"
  let terminal := List.zipWith (fun row amounts =>
    List.zipWith (fun (x : Entry) (z : Int) => ((⟨z < 0,z.natAbs.bits⟩,x.2) : Entry)) row amounts) xs expected
  let cutCount := ResidualCutProgram.steps terminal vs pairs (label t)
  let cutInitial : BitState 700 :=
    ⟨out.heap,out.next,⟨out.registers.d,vertices.root,[],ends.root⟩,[],0,tape⟩
  let cutRun := fun cap => PhysicalCoverExecution.executeCached ResidualCutProgram.program cap cutInitial 0
  let some (cutEnd,cutPaid) := cutRun (cutCount+1)
    | throw (IO.userError "the residual cut scan did not halt")
  let cutState := eraseState cutEnd
  unless PhysicalCoverReader.readWord cutState.heap cutState.registers.d == some expectedCut &&
      cutEnd.pc == 7 && cutEnd.stack.isEmpty && cutEnd.source == tape &&
      cutEnd.heap.take cutInitial.heap.length == cutInitial.heap && (cutRun cutCount).isNone && 0 < cutPaid do
    throw (IO.userError "the sink-complement scan returned unexpected flags")
  IO.println s!"PASS physical sink complement {expectedCut}, {cutCount} instructions, paid {cutPaid}"
  let fullCount := iterations+cutCount+7
  let wholeInitial : BitState 1624 :=
    ⟨limit.heap,limit.next,⟨flow.root,network.root,limit.root,[]⟩,[],0,tape⟩
  let wholeRun := fun cap => PhysicalCoverExecution.executeCached ResidualMaxFlowCutProgram.program cap wholeInitial 0
  let some (wholeEnd,wholePaid) := wholeRun (fullCount+1)
    | throw (IO.userError "the full maximum-flow cut did not halt")
  let wholeState := eraseState wholeEnd
  unless PhysicalCoverReader.readWord wholeState.heap wholeState.registers.d == some expectedCut &&
      wholeEnd.pc == 5 && wholeEnd.stack.isEmpty && wholeEnd.source == tape &&
      wholeEnd.heap.take wholeInitial.heap.length == wholeInitial.heap && (wholeRun fullCount).isNone && 0 < wholePaid do
    throw (IO.userError "the full maximum-flow cut returned unexpected flags")
  IO.println s!"PASS physical maximum-flow cut {expectedCut}, {fullCount} instructions, paid {wholePaid}"

private def entry (z : Int) (capacity : ℕ) : Entry :=
  (⟨z < 0,z.natAbs.bits⟩,capacity.bits++[false])

def main : IO Unit := do
  let z := entry 0 0
  let cap := entry 0 2
  let saturated := entry 2 2
  let reverse := entry (-2) 0
  let terminal := [[0,2,1],[-2,0,2],[-1,-2,0]]
  check (n:=3) 0 2 [[z,cap,entry 0 1],[z,z,cap],[z,z,z]] 3 [(0,2)] terminal 3 [true,true,false]
  check (n:=3) 0 2 [[z,saturated,entry 1 1],[reverse,z,saturated],[entry (-1) 0,reverse,z]]
    0 [] terminal 0 [true,true,false]
  let unit := entry 1 1
  let empty := entry 0 1
  let minus := entry (-1) 0
  let start := [[z,unit,empty,z],[minus,z,unit,empty],[z,minus,z,unit],[z,z,minus,z]]
  check (n:=4) 0 3 start 4 [(0,2),(2,1),(1,3)]
    [[0,1,1,0],[-1,0,0,1],[-1,0,0,1],[0,-1,-1,0]] 1 [true,true,true,false]
