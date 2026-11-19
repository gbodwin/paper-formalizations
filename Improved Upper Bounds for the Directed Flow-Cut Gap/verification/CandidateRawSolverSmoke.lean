import DirectedFlowCutGap.CandidateRawSolverProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def storeRows : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], heap => PackedWordPairTable.allocate .nil heap
  | row::rows, heap =>
    let tail := storeRows rows heap
    let word := PackedWordPairTable.word row tail
    PackedWordPairTable.allocate (.pair word.root tail.root) word

private def start {C n : ℕ} (pc : Fin C) (D : EncodedCandidateCapacity.Input n) (s t : Fin n)
    (vertices grid bound tape : Bits) : BitState C :=
  let graph := storeRows (D.adjacency.toList.map Vector.toList) PackedWordPairTable.seed
  let nv := PackedWordPairTable.word vertices graph
  let mask := PackedWordPairTable.word D.removed.toList nv
  let level := PackedWordPairTable.word grid mask
  let input := PackedWordPairTable.allocate (.pair mask.root level.root) level
  let cap := PackedWordPairTable.word bound input
  let source := PackedWordPairTable.word s.val.bits cap
  let target := PackedWordPairTable.word t.val.bits source
  let ends := PackedWordPairTable.allocate (.pair source.root target.root) target
  let params := PackedWordPairTable.allocate (.pair cap.root ends.root) ends
  ⟨params.heap,params.next,⟨graph.root,nv.root,input.root,params.root⟩,[],pc,tape⟩

private def executeCounted {C : ℕ} (p : Program C) :
    ℕ → CachedReferenceExecution.FastState C → ℕ → ℕ → Option (BitState C×ℕ×ℕ)
  | 0, _, _, _ => none
  | fuel+1, state, used, paid =>
    match CachedReferenceExecution.attempt p state with
    | .stopped final cost => some (final.freeze,used,paid+cost)
    | .completed next => executeCounted p fuel next.state (used+1) (paid+next.cost)

private def readWords (heap : NaturalHeap) (root : ℕ) : Option (List Bits) :=
  PhysicalCoverReader.readList heap (PhysicalCoverReader.readWord heap) heap.length root

private def checkMatrix {n : ℕ} (D : EncodedCandidateCapacity.Input n) (s t : Fin n) (L B : ℕ) : IO Unit := do
  let nv := n.bits++[false]
  let grid := L.bits++[false,false]
  let cap := B.bits++[false]
  let tape := [true,false,true,true]
  let initial := start (0 : Fin 1395) D s t nv grid cap tape
  let bound := CandidateCapacityMatrixProgram.instructionBound n L nv.length grid.length cap.length
  let some (out,used,paid) := executeCounted CandidateCapacityMatrixProgram.program (bound+1)
      (CachedReferenceExecution.FastState.ofReference initial) 0 0
    | throw (IO.userError "raw capacity construction did not halt within its proved bound")
  let f := eraseState out
  let nodes := CandidateEnumeration.networkOrder n L
  let β := 2*L*CandidateBudgetData.remaining D.removed.toList
  let expected := nodes.map fun a => nodes.map fun b => (D.directCapacity s t L B β a b).bits
  unless PhysicalCoverReader.readList f.heap (readWords f.heap) f.heap.length f.registers.d == some expected &&
      out.pc == 4 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      used ≤ bound && 0 < paid do
    throw (IO.userError s!"capacity table disagreed with the encoded formula for n={n}, L={L}, B={B}")
  IO.println s!"PASS raw candidate matrix n={n}, grid {L}, bound {B}, {nodes.length} by {nodes.length}, {used} instructions, paid {paid}"

private def checkSolver : IO Unit := do
  let D : EncodedCandidateCapacity.Input 2 := {
    adjacency := Vector.ofFn fun _ => Vector.ofFn fun _ => false
    removed := Vector.ofFn fun _ => true }
  let grid := [true,false,false]
  let tape := [false,true,false]
  let initial := start (0 : Fin 3797) D 0 1 [false,true,false] grid [true,false] tape
  let some (out,used,paid) := executeCounted CandidateRawSolverProgram.program 5000000
      (CachedReferenceExecution.FastState.ofReference initial) 0 0
    | throw (IO.userError "the complete candidate solver did not reach the paid halt")
  let f := eraseState out
  unless readWords f.heap f.registers.d == some [grid,grid] && out.pc == 2 && out.stack.isEmpty &&
      out.source == tape && out.heap.take initial.heap.length == initial.heap && 0 < paid do
    throw (IO.userError "the raw candidate solver did not return both original grid words")
  IO.println s!"PASS original graph to candidate numerators [1, 1], 26 closure vertices, {used} instructions, paid {paid}"

def main : IO Unit := do
  checkMatrix (n:=3)
    { adjacency := Vector.ofFn fun a => Vector.ofFn fun b => (a == 0 && b == 1) || (a == 1 && b == 2)
      removed := Vector.ofFn fun _ => false } 0 2 1 1
  checkMatrix (n:=2)
    { adjacency := Vector.ofFn fun a => Vector.ofFn fun b => a == 1 && b == 0
      removed := Vector.ofFn fun v => v == 0 } 0 1 2 0
  (← IO.getStdout).flush
  checkSolver
