import DirectedFlowCutGap.IntegerCellTestProgram
import DirectedFlowCutGap.PhysicalCoverExecution
import DirectedFlowCutGap.PackedWordPairTable

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def check (description : String) (distance : Option ℕ) (weight level : ℕ) (expected : Bool) : IO Unit := do
  let padded (n : ℕ) := n.bits ++ [false, false]
  let weightWord := padded weight
  let levelWord := padded level
  let seed := PackedWordPairTable.seed
  let (stored, logical) : PackedWordPairTable.Prepared × Option GraphWalkExtension.Walk := match distance with
    | none => (seed, none)
    | some d =>
      let num := PackedWordPairTable.word (padded d) seed
      let den := PackedWordPairTable.word (padded 1) num
      let pair := PackedWordPairTable.allocate (.pair num.root den.root) den
      (PackedWordPairTable.allocate (.pair seed.root pair.root) pair, some ⟨[], ⟨padded d, padded 1, by decide⟩⟩)
  let a := PackedWordPairTable.word weightWord stored
  let j := PackedWordPairTable.word levelWord a
  let tape := [false,true,true]
  let input : BitState 186 := ⟨j.heap,j.next,⟨stored.root,a.root,j.root,[]⟩,[],19,tape⟩
  let k := IntegerCellTestProgram.instructions logical weightWord levelWord + 1
  let p := IntegerCellTestProgram.program
  let some (out, paid) := PhysicalCoverExecution.executeCached p (k+1) input 0
    | throw (IO.userError s!"midpoint test did not halt for {description}")
  let seen := (eraseHeap out.heap)[value out.registers.d]?
  unless seen == some (.flag expected) && out.pc == 20 && out.stack.isEmpty &&
      out.source == tape && out.heap.take input.heap.length == input.heap &&
      (PhysicalCoverExecution.executeCached p k input 0).isNone && 0 < paid do
    throw (IO.userError s!"midpoint test failed for {description}")
  IO.println s!"PASS fixed midpoint {description}, {k} instructions, paid {paid}"

def main : IO Unit := do
  check "below lower boundary" (some 3) 2 2 false
  check "at lower boundary" (some 3) 2 3 true
  check "strictly inside" (some 3) 2 4 true
  check "at upper boundary" (some 3) 2 5 false
  check "zero width" (some 3) 0 3 false
  check "infinite distance" none 2 4 false
