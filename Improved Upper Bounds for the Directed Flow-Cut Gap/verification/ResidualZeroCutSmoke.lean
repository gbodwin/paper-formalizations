import DirectedFlowCutGap.ResidualZeroMinCutProgram
import DirectedFlowCutGap.CandidateBudgetCutProgram
import DirectedFlowCutGap.MinimumClosureCut
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation
open ResidualRowProgram (Entry)
open MinimumClosureCut

private abbrev Store := PackedWordPairTable.Prepared

private def storeList {α : Type} (item : α → Store → Store) : List α → Store → Store
  | [], p => PackedWordPairTable.allocate .nil p
  | x::xs, p =>
    let tail := storeList item xs p
    let head := item x tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def storeEdge (e : Bits×Bits) (p : Store) : Store :=
  let u := PackedWordPairTable.word e.1 p
  let v := PackedWordPairTable.word e.2 u
  PackedWordPairTable.allocate (.pair u.root v.root) v

private def readTable {α : Type} (h : NaturalHeap) (item : ℕ → Option α) (r : ℕ) : Option (List (List α)) :=
  PhysicalCoverReader.readList h (PhysicalCoverReader.readList h item h.length) h.length r

private def readZeroEntry (h : NaturalHeap) (r : ℕ) : Option (ℕ×ℕ) := do
  let some (.pair amount cap) := h[r]? | none
  let some (.pair mag sign) := h[amount]? | none
  if h[mag]? == some .nil && h[sign]? == some (.flag false) then pure (amount,cap) else none

private def iterate (vs : List Bits) (es : List (Bits×Bits)) (s t : Bits)
    (xs : List (List Entry)) (fuel : ℕ) : Option (ℕ×List (List Entry)) := do
  let path := ResidualFlowStepProgram.path xs vs es s t
  let count := ResidualFlowStepProgram.steps xs vs es s t
  if path.isEmpty then
    pure (count+12,xs)
  else
    match fuel with
    | 0 => none
    | k+1 =>
      let (later,result) ← iterate vs es s t (ResidualFlowStepProgram.outputTable xs vs path) k
      pure (count+13+later,result)

private def check (required : Bool) (cost : Int) : IO Unit := do
  let P : MinimumClosureProblem.Problem (Fin 1) := {
    required := if required then {0} else ∅
    forbidden := ∅
    arcs := ∅
    cost := fun _ => cost }
  let node (i : Fin 3) : Vertex (Fin 1) :=
    if i.val == 0 then .inl 0 else .inr (i.val == 2)
  let cs := (List.finRange 3).map fun u => (List.finRange 3).map fun v =>
    (capacity P (node u) (node v)).bits++[false]
  let word := (budget P).bits++[false,false]
  let label := fun i : Fin 3 => i.val.bits
  let vs := ResidualFlowStepProgram.wordTable label
  let pairs := ResidualFlowStepProgram.pairTable label
  let table := storeList (storeList PackedWordPairTable.word) cs PackedWordPairTable.seed
  let vertices := storeList PackedWordPairTable.word vs table
  let edges := storeList storeEdge pairs vertices
  let source := PackedWordPairTable.word (label 1) edges
  let target := PackedWordPairTable.word (label 2) source
  let ends := PackedWordPairTable.allocate (.pair target.root edges.root) target
  let endpoints := PackedWordPairTable.allocate (.pair source.root ends.root) ends
  let setup := PackedWordPairTable.allocate (.pair vertices.root endpoints.root) endpoints
  let funds := PackedWordPairTable.word word setup
  let tape := [true,false,true]
  let regs : Registers Bits := ⟨table.root,setup.root,funds.root,[]⟩
  let start : BitState 32 := ⟨funds.heap,funds.next,regs,[],0,tape⟩
  let make := fun count => PhysicalCoverExecution.executeCached ResidualZeroTableProgram.program count start 0
  let setupSteps := ResidualZeroTableProgram.tableSteps cs+4
  let some (init,paidInit) := make (setupSteps+1)
    | throw (IO.userError "zero-table initialization did not halt")
  let before := eraseHeap start.heap
  let after := eraseState init
  let some old := readTable before some (value table.root)
    | throw (IO.userError "capacity pointers were unreadable")
  let some new := readTable after.heap (readZeroEntry after.heap) after.registers.d
    | throw (IO.userError "the initialized table did not contain canonical zero fields")
  let shared := new.flatten.map Prod.fst
  let some zeroRoot := shared.head? | throw (IO.userError "the expected nonempty flow table was empty")
  unless new.map (List.map Prod.snd) == old && shared.all (fun p => p == zeroRoot) &&
      init.pc == 4 && init.stack.isEmpty && init.source == tape && init.heap.take start.heap.length == start.heap &&
      (make setupSteps).isNone && 0 < paidInit do
    throw (IO.userError "the starting flow failed its exact initialization checks")
  IO.println s!"PASS physical zero-flow table with budget {value word}, {setupSteps} instructions, paid {paidInit}"
  let xs := ResidualZeroTableProgram.table cs
  let some (flowSteps,terminal) := iterate vs pairs (label 1) (label 2) xs (value word)
    | throw (IO.userError "the closure fixture's budget was insufficient")
  let k := setupSteps+BinaryCounterProgram.steps word+flowSteps+ResidualCutProgram.steps terminal vs pairs (label 2)+16
  let initial : BitState 1689 := ⟨funds.heap,funds.next,regs,[],0,tape⟩
  let run := fun cap => PhysicalCoverExecution.executeCached ResidualZeroMinCutProgram.program cap initial 0
  let some (out,paid) := run (k+1)
    | throw (IO.userError "binary capacity-to-cut execution did not halt")
  let final := eraseState out
  let expected := [true,true,false]
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected &&
      out.pc == 3 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "the closure cut, tape or charged stop disagreed")
  IO.println s!"PASS physical binary closure cut {expected}, budget {value word}, {k} instructions, paid {paid}"
  let flags := if required then [true,false,true] else [true,true]
  let grid := [true,false,false]
  let mask := PackedWordPairTable.word flags setup
  let scale := PackedWordPairTable.word grid mask
  let pair := PackedWordPairTable.allocate (.pair mask.root scale.root) scale
  let entry : BitState 1862 := ⟨pair.heap,pair.next,⟨table.root,setup.root,pair.root,[]⟩,[],0,tape⟩
  let canonical := (budget P).bits
  let k := setupSteps+BinaryCounterProgram.steps canonical+flowSteps+
    ResidualCutProgram.steps terminal vs pairs (label 2)+22+CandidateBudgetProgram.steps flags grid
  let run := fun cap => PhysicalCoverExecution.executeCached CandidateBudgetCutProgram.program cap entry 0
  let some (out,paid) := run (k+1)
    | throw (IO.userError "mask-to-closure-cut execution did not halt")
  let final := eraseState out
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected &&
      PhysicalCoverReader.readWord final.heap final.registers.c == some canonical &&
      out.pc == 2 && out.stack.isEmpty && out.source == tape &&
      out.heap.take entry.heap.length == entry.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "the computed closure budget or its use by the solver disagreed")
  IO.println s!"PASS physical mask-to-closure cut {expected}, computed budget {value canonical}, {k} instructions, paid {paid}"

private def checkBudget (flags grid : Bits) (expected : ℕ) : IO Unit := do
  let mask := PackedWordPairTable.word flags PackedWordPairTable.seed
  let size := PackedWordPairTable.word grid mask
  let tape := [false,true,false]
  let initial : BitState 157 := ⟨size.heap,size.next,⟨mask.root,size.root,[],[]⟩,[],0,tape⟩
  let k := CandidateBudgetProgram.steps flags grid
  let run := fun cap => PhysicalCoverExecution.executeCached CandidateBudgetProgram.program cap initial 0
  let some (out,paid) := run (k+1)
    | throw (IO.userError "mask budget computation did not halt")
  let final := eraseState out
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected.bits &&
      out.pc == 5 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "the computed budget disagreed with its canonical value or the halt")
  IO.println s!"PASS physical mask budget {expected}, {k} instructions, paid {paid}"

def main : IO Unit := do
  checkBudget [false,true,false,false,true,false] [true,true,false,false] 24
  checkBudget [false,false] [false,false] 0
  checkBudget [true,true,true] [true,false] 0
  checkBudget [] [true,true,true] 0
  check true 2
  check false 0
