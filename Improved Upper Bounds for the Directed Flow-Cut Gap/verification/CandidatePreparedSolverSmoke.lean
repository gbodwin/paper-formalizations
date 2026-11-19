import DirectedFlowCutGap.CandidatePreparedSolverProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def storeList {α : Type} (store : α → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared) :
    List α → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], prep => PackedWordPairTable.allocate .nil prep
  | x::rest, prep =>
    let tail := storeList store rest prep
    let head := store x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def readWords (heap : NaturalHeap) (root : ℕ) : Option (List Bits) :=
  PhysicalCoverReader.readList heap (PhysicalCoverReader.readWord heap) heap.length root

private def executeCounted {C : ℕ} (p : Program C) :
    ℕ → CachedReferenceExecution.FastState C → ℕ → ℕ → Option (BitState C×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, state, used, paid =>
    match CachedReferenceExecution.attempt p state with
    | .stopped final cost => some (final.freeze,used,paid+cost)
    | .completed next => executeCounted p fuel next.state (used+1) (paid+next.cost)

private def checkDecoder (flags removed grid : Bits) (expected : List Bits) : IO Unit := do
  let cut := PackedWordPairTable.word flags PackedWordPairTable.seed
  let mask := PackedWordPairTable.word removed cut
  let size := PackedWordPairTable.word grid mask
  let tape := [false,true,true,false]
  let initial : BitState 193 := ⟨size.heap,size.next,⟨cut.root,mask.root,size.root,[]⟩,[],0,tape⟩
  let k := CandidateDecoderProgram.steps grid flags removed
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateDecoderProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "candidate decoder did not halt at the verified step count")
  let final := eraseState out
  unless readWords final.heap final.registers.d == some expected && out.pc == 3 &&
    out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
    (run k).isNone && 0 < paid do
    throw (IO.userError "candidate decoder lost a block suffix, a grid value, or the paid halt")
  IO.println s!"PASS physical candidate decode grid {value grid}, output {expected.map value}, {k} instructions, paid {paid}"

private def residualTrace (labels : List Bits) (edges : List (Bits×Bits)) (s t : Bits) :
    ℕ → List (List ResidualRowProgram.Entry) → Option (List (List ResidualRowProgram.Entry)×ℕ×ℕ)
  | fuel, table =>
    let path := ResidualFlowStepProgram.path table labels edges s t
    let k := ResidualFlowStepProgram.steps table labels edges s t
    if path.isEmpty then some (table,k+12,0)
    else
      match fuel with
      | 0 => none
      | next+1 => do
        let (final,steps,augmentations) ← residualTrace labels edges s t next
          (ResidualFlowStepProgram.outputTable table labels path)
        pure (final,k+13+steps,augmentations+1)

private def checkPreparedSolver : IO Unit := do
  let D : EncodedCandidateCapacity.Input 3 := {
    adjacency := Vector.ofFn fun a => Vector.ofFn fun b => (a == 0 && b == 1) || (a == 1 && b == 2)
    removed := Vector.ofFn fun _ => false }
  let F := CandidateEnumeration.make 3 1
  let vertices := F.network.enumeration.vertices
  let m := CandidatePhysicalCut.networkSize 3 1
  let problem := D.construct 0 2 1 1 F.nodes.enumeration F.network.enumeration
  let rows := vertices.map fun a => vertices.map fun b => (D.directCapacity 0 2 1 1 problem.budget a b).bits
  let ws := (List.range m).map Nat.bits
  unless vertices.map CandidateEnumeration.networkIndex == List.range m && problem.budget == 6 do
    throw (IO.userError s!"prepared two-edge candidate changed: budget {problem.budget}")
  let cs := storeList (storeList PackedWordPairTable.word) rows PackedWordPairTable.seed
  let nw := [true,true,false]
  let lw := [true,false,false]
  let dimension := PackedWordPairTable.word nw cs
  let mask := PackedWordPairTable.word D.removed.toList dimension
  let size := PackedWordPairTable.word lw mask
  let bundle := PackedWordPairTable.allocate (.pair mask.root size.root) size
  let tape := [true,false,true,true]
  let initial : BitState 2386 := ⟨bundle.heap,bundle.next,⟨cs.root,dimension.root,bundle.root,[]⟩,[],0,tape⟩
  let edges := ws.product ws
  let s := (m-2).bits
  let t := (m-1).bits
  let some (finalFlow,loop,augmentations) := residualTrace ws edges s t problem.budget (ResidualZeroTableProgram.table rows)
    | throw (IO.userError "the two-edge candidate exceeded its computed budget")
  unless augmentations == 4 do
    throw (IO.userError s!"expected four closure-flow augmentations, found {augmentations}")
  let expectedMask := ResidualCutData.flags (n:=38) finalFlow (fun i => i.val.bits) 37
  let expected : List ℕ := [0,1,0]
  unless (CandidateNumeratorScanProgram.scan 2 lw expectedMask D.removed.toList).map value == expected do
    throw (IO.userError "the retained cut does not assign one unit to the interior vertex")
  let cutSteps := CandidateInputConfigurationProgram.steps nw lw+CandidateBudgetProgram.steps D.removed.toList lw+
    ResidualZeroTableProgram.tableSteps rows+BinaryCounterProgram.steps problem.budget.bits+loop+
    ResidualCutProgram.steps finalFlow ws edges t+32
  let k := cutSteps+CandidateDecoderProgram.steps lw expectedMask D.removed.toList+6
  IO.println s!"Prepared two-edge path with {m} closure vertices and {k} expected instructions"
  (← IO.getStdout).flush
  let some (out,used,paid) := executeCounted CandidatePreparedSolverProgram.program (k+1)
      (CachedReferenceExecution.FastState.ofReference initial) 0 0
    | throw (IO.userError s!"candidate solver did not halt after {k} steps")
  let final := eraseState out
  let some words := readWords final.heap final.registers.d | throw (IO.userError "candidate numerator list was not readable")
  unless words.map value == expected && out.pc == 4 && used == k &&
    out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
    0 < paid do
    throw (IO.userError s!"two-edge solver returned {words.map value} in {used} steps instead of {expected} in {k} steps")
  IO.println s!"PASS physical prepared candidate with {m} vertices, budget {problem.budget}, {augmentations} augmentations, numerators {expected}, {k} instructions, paid {paid}"

def main : IO Unit := do
  checkDecoder [true,true,false,true,true,true,true,false,false,true,true,true,false,true] [false,true] [false,true,false]
    [[true],[false,true,false]]
  checkDecoder [true,true,true,false,false,false] [false] [false,true] [[]]
  checkDecoder [false,true] [false] [] [[true]]
  checkDecoder [true,false] [] [true,true,false] []
  (← IO.getStdout).flush
  checkPreparedSolver
