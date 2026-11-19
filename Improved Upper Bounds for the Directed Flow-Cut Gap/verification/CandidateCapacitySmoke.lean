import DirectedFlowCutGap.CandidateCapacityWords
import DirectedFlowCutGap.CandidateLevelTestProgram
import DirectedFlowCutGap.CandidatePortAdjacencyProgram
import DirectedFlowCutGap.CandidateTerminalFlagsProgram
import DirectedFlowCutGap.CandidateCoreCapacityProgram
import DirectedFlowCutGap.CandidateTerminalCapacityProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def checkWords (budget : Bits) (numeric : ℕ) : IO Unit := do
  let words := PackedWordPairTable.word budget PackedWordPairTable.seed
  let f := PackedWordPairTable.allocate (.flag false) words
  let t := PackedWordPairTable.allocate (.flag true) f
  let tape := [true,false,true]
  let initial : BitState 32 := ⟨t.heap,t.next,⟨words.root,[],[],[]⟩,[],0,tape⟩
  let k := CandidateCapacityWords.steps budget
  let make := fun fuel => PhysicalCoverExecution.executeCached CandidateCapacityWords.program fuel initial 0
  let some (built,paid) := make (k+1) | throw (IO.userError "capacity word construction did not halt")
  let source := built.registers.d
  unless built.pc == 9 && built.stack.isEmpty && built.source == tape &&
      built.heap.take initial.heap.length == initial.heap && (make k).isNone && 0 < paid do
    throw (IO.userError "capacity word construction lost the tape, heap prefix or halt")
  for pair in [(false,false),(true,false),(false,true),(true,true)] do
    let unitFlag := if pair.1 then t.root else f.root
    let barrierFlag := if pair.2 then t.root else f.root
    let select : BitState 8 := ⟨built.heap,built.next,⟨source,unitFlag,barrierFlag,[]⟩,[],0,tape⟩
    let run := fun fuel => PhysicalCoverExecution.executeCached CandidateCapacityWords.select fuel select 0
    let some (out,paidSelect) := run 5 | throw (IO.userError "capacity selector did not halt")
    let endState := eraseState out
    let some result := PhysicalCoverReader.readWord endState.heap endState.registers.d
      | throw (IO.userError "selected capacity was not a stored word")
    let expected := (if pair.1 then 1 else 0)+(if pair.2 then numeric+1 else 0)
    unless value result == expected && result == CandidateCapacityWords.word budget pair.1 pair.2 &&
        out.pc == 6 && out.stack.isEmpty && out.source == tape && out.heap == built.heap &&
        (run 4).isNone && 0 < paidSelect do
      throw (IO.userError "capacity selector returned the wrong word or changed storage")
  IO.println s!"PASS physical four capacities from budget {numeric}, {k} setup instructions, paid {paid}"

private def checkLevels (same : Bool) (a b shift : Bits) (expected : Bool) : IO Unit := do
  let left := PackedWordPairTable.word a PackedWordPairTable.seed
  let right := PackedWordPairTable.word b left
  let gap := PackedWordPairTable.word shift right
  let flag := PackedWordPairTable.allocate (.flag same) gap
  let tape := [false,true,true]
  let start : BitState 144 := ⟨flag.heap,flag.next,⟨left.root,right.root,gap.root,flag.root⟩,[],0,tape⟩
  let k := CandidateLevelTestProgram.steps same a b shift
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateLevelTestProgram.program fuel start 0
  let some (out,paid) := run (k+1) | throw (IO.userError "threshold implication test did not halt")
  let endState := eraseState out
  unless endState.heap[endState.registers.d]? == some (.flag expected) &&
      out.pc == 16 && out.stack.isEmpty && out.source == tape &&
      out.heap.take start.heap.length == start.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "threshold implication result or execution receipt disagreed")
  IO.println s!"PASS physical threshold implication, equal points {same}, levels {value a}/{value b}, shift {value shift}, result {expected}, {k} instructions, paid {paid}"

private def storeRows : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], p => PackedWordPairTable.allocate .nil p
  | row::rest, p =>
    let tail := storeRows rest p
    let head := PackedWordPairTable.word row tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def storeTag : CandidatePortAdjacencyProgram.Kind → Cell Bits
  | .core => .nil
  | .start => .flag false
  | .finish => .flag true

private def checkPorts (p q : TerminalPorts.Vertex (Fin 3)) (expected : Bool) : IO Unit := do
  let D : EncodedCandidateCapacity.Input 3 := {
    adjacency := Vector.ofFn fun u => Vector.ofFn fun v => u.val == 0 && v.val == 1
    removed := Vector.ofFn fun _ => false }
  let u := CandidatePortAdjacencyProgram.kind p
  let v := CandidatePortAdjacencyProgram.kind q
  let a := (CandidatePortAdjacencyProgram.vertex p).val.bits++[false]
  let b := (CandidatePortAdjacencyProgram.vertex q).val.bits++[false,false]
  let matrix := storeRows (CandidatePortAdjacencyProgram.rows D) PackedWordPairTable.seed
  let x := PackedWordPairTable.word a matrix
  let y := PackedWordPairTable.word b x
  let ctx := PackedWordPairTable.allocate (.pair matrix.root y.root) y
  let first := PackedWordPairTable.allocate (storeTag u) ctx
  let second := PackedWordPairTable.allocate (storeTag v) first
  let tags := PackedWordPairTable.allocate (.pair first.root second.root) second
  let tape := [false,true,false]
  let start : BitState 116 := ⟨tags.heap,tags.next,⟨x.root,ctx.root,tags.root,[]⟩,[],0,tape⟩
  let route := CandidatePortAdjacencyProgram.route u v
  let k := CandidatePortAdjacencyProgram.routeSteps u +
    match route with
    | .absent => 1
    | .original => GraphAdjacencyProgram.steps a b+1
    | .diagonal => BinaryComparisonProgram.steps a b+6+
        if value a == value b then 0 else GraphAdjacencyProgram.steps a b
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidatePortAdjacencyProgram.program fuel start 0
  let some (out,paid) := run (k+1) | throw (IO.userError "tagged port adjacency test did not halt")
  let endState := eraseState out
  unless endState.heap[endState.registers.d]? == some (.flag expected) &&
      expected == (D.portAdjWithCost p q).1 && out.pc == 10 && out.stack.isEmpty && out.source == tape &&
      out.heap.take start.heap.length == start.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "tagged adjacency result or execution receipt disagreed")
  IO.println s!"PASS physical port adjacency from {value a} to {value b}, result {expected}, {k} instructions, paid {paid}"

private def readFlag (heap : NaturalHeap) (root : ℕ) : Option Bool :=
  match heap[root]? with
  | some (.flag b) => some b
  | _ => none

private def checkGap (p : TerminalPorts.Vertex (Fin 3)) (grid bound : Bits)
    (expectedActive : Bool) (expectedGap : ℕ) : IO Unit := do
  let flags := [false,true,false]
  let u := CandidatePortAdjacencyProgram.vertex p
  let kind := CandidatePortAdjacencyProgram.kind p
  let mask := PackedWordPairTable.word flags PackedWordPairTable.seed
  let index := PackedWordPairTable.word (u.val.bits++[false]) mask
  let tag := PackedWordPairTable.allocate (storeTag kind) index
  let size := PackedWordPairTable.word grid tag
  let limit := PackedWordPairTable.word bound size
  let tape := [true,true,false]
  let minStart : BitState 56 := ⟨limit.heap,limit.next,⟨size.root,limit.root,[],[]⟩,[],0,tape⟩
  let minSteps := BinaryMinimumWordProgram.steps grid bound
  let minRun := fun fuel => PhysicalCoverExecution.executeCached BinaryMinimumWordProgram.program fuel minStart 0
  let some (capped,minCharge) := minRun (minSteps+1) | throw (IO.userError "grid bound did not halt")
  let expectedRef := if value grid ≤ value bound then size.root else limit.root
  unless capped.registers.d == expectedRef && capped.source == tape && capped.pc == 4 && capped.stack.isEmpty &&
      capped.heap.take minStart.heap.length == minStart.heap && (minRun minSteps).isNone && 0 < minCharge do
    throw (IO.userError "grid bound result or original word address disagreed")
  let limits := PackedWordPairTable.allocate (.pair size.root capped.registers.d) ⟨capped.heap,capped.next,[],0⟩
  let initial : BitState 52 := ⟨limits.heap,limits.next,⟨index.root,mask.root,limits.root,tag.root⟩,[],0,tape⟩
  let k := CandidatePortGapProgram.steps kind (u.val.bits++[false])
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidatePortGapProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "candidate port gap did not halt")
  let endState := eraseState out
  let some (.pair activeRoot gapRoot) := endState.heap[endState.registers.d]?
    | throw (IO.userError "candidate port gap did not return both fields")
  let some bits := PhysicalCoverReader.readWord endState.heap gapRoot
    | throw (IO.userError "candidate port gap was not stored")
  unless readFlag endState.heap activeRoot == some expectedActive && value bits == expectedGap &&
      out.pc == 11 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "candidate port gap disagreed with mask and minimum")
  IO.println s!"PASS physical port activity {expectedActive}, gap {expectedGap}, grid bound {minSteps} and gap {k} instructions, paid {minCharge+paid}"

private def storeFlags (a b : Bool) (p : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let x := PackedWordPairTable.allocate (.flag a) p
  let y := PackedWordPairTable.allocate (.flag b) x
  PackedWordPairTable.allocate (.pair x.root y.root) y

private def checkShift (a b same edge : Bool) (expected : ℕ) : IO Unit := do
  let tape := [false,true,true]
  let grid := PackedWordPairTable.word [false,false,true] PackedWordPairTable.seed
  let gap := PackedWordPairTable.word [true,false] grid
  let words := PackedWordPairTable.allocate (.pair grid.root gap.root) gap
  let relations := storeFlags same edge words
  let signs := storeFlags a b relations
  let initial : BitState 24 := ⟨signs.heap,signs.next,⟨words.root,relations.root,signs.root,[]⟩,[],0,tape⟩
  let k := CandidateShiftSelectProgram.steps a b same
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateShiftSelectProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "shift selection did not halt")
  let endState := eraseState out
  let some shifted := PhysicalCoverReader.readWord endState.heap endState.registers.d
    | throw (IO.userError "shift selection did not return a word")
  unless value shifted == expected && out.pc == 20 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "shift selection result or paid halt disagreed")
  IO.println s!"PASS physical shift {expected} for signs {a}/{b}, same port {same}, reverse edge {edge}, {k} instructions, paid {paid}"

private def checkTerminal (level : Bits) (side sign on pin unit hard : Bool) : IO Unit := do
  let tape := [true,false]
  let size := PackedWordPairTable.word level PackedWordPairTable.seed
  let nodeFields := storeFlags sign on size
  let pins := storeFlags side pin nodeFields
  let initial : BitState 41 := ⟨pins.heap,pins.next,⟨size.root,nodeFields.root,pins.root,[]⟩,[],0,tape⟩
  let k := CandidateTerminalFlagsProgram.steps level
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateTerminalFlagsProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "terminal capacity flags did not halt")
  let final := eraseState out
  let some (.pair unitRoot barrierRoot) := final.heap[final.registers.d]?
    | throw (IO.userError "terminal capacity flags did not return the two fields")
  unless readFlag final.heap unitRoot == some unit && readFlag final.heap barrierRoot == some hard &&
      out.pc == 21 && out.stack.isEmpty && out.source == tape &&
      out.heap.take initial.heap.length == initial.heap && (run k).isNone && 0 < paid do
    throw (IO.userError "terminal capacity flags or paid halt disagreed")
  IO.println s!"PASS physical terminal flags at level {value level}, sink side {side}, unit {unit}, barrier {hard}, {k} instructions, paid {paid}"
  let budget := 6
  let funds := PackedWordPairTable.word budget.bits pins
  let build : BitState 32 := ⟨funds.heap,funds.next,⟨funds.root,[],[],[]⟩,[],0,tape⟩
  let some (words,_) := PhysicalCoverExecution.executeCached CandidateCapacityWords.program
      (CandidateCapacityWords.steps budget.bits+1) build 0
    | throw (IO.userError "terminal capacity words did not halt")
  let entry : BitState 65 := ⟨words.heap,words.next,⟨size.root,nodeFields.root,pins.root,words.registers.d⟩,[],0,tape⟩
  let k := CandidateTerminalCapacityProgram.steps level
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateTerminalCapacityProgram.program fuel entry 0
  let some (out,paid) := run (k+1) | throw (IO.userError "fused terminal capacity did not halt")
  let final := eraseState out
  let expected := (if unit then 1 else 0)+(if hard then budget+1 else 0)
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected.bits &&
      out.pc == 5 && out.stack.isEmpty && out.source == tape && out.heap.take entry.heap.length == entry.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "fused terminal capacity missed the actual flags or paid halt")
  IO.println s!"PASS fused physical terminal capacity {expected} at level {value level}, sink side {side}, {k} instructions, paid {paid}"

private def checkCore (a b : CandidateEnumeration.Node 3 4) (limit : ℕ) (hard : Bool) : IO Unit := do
  let D : EncodedCandidateCapacity.Input 3 := {
    adjacency := Vector.ofFn fun u => Vector.ofFn fun v => u.val == 0 && v.val == 1
    removed := Vector.ofFn fun v => v.val == 2 }
  let x := a.2.val.bits++[false]
  let y := b.2.val.bits
  let grid := [false,false,true]
  let gap := CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid limit.bits) a.1.1
  let samePort := decide (a.1.1=b.1.1)
  let samePoint := decide (a.1=b.1)
  let edge := CandidatePortAdjacencyProgram.result D b.1.1 a.1.1
  let left := PackedWordPairTable.word x PackedWordPairTable.seed
  let right := PackedWordPairTable.word y left
  let levels := PackedWordPairTable.allocate (.pair left.root right.root) right
  let gridWord := PackedWordPairTable.word grid levels
  let gapWord := PackedWordPairTable.word gap gridWord
  let bounds := PackedWordPairTable.allocate (.pair gridWord.root gapWord.root) gapWord
  let signs := storeFlags a.1.2 b.1.2 bounds
  let relation := storeFlags samePort edge signs
  let inputs := PackedWordPairTable.allocate (.pair signs.root relation.root) relation
  let point := PackedWordPairTable.allocate (.flag samePoint) inputs
  let rel := PackedWordPairTable.allocate (.pair inputs.root point.root) point
  let β := 2*4*CandidateBudgetData.remaining D.removed.toList
  let budget := PackedWordPairTable.word β.bits rel
  let tape := [true,true,false]
  let build : BitState 32 := ⟨budget.heap,budget.next,⟨budget.root,[],[],[]⟩,[],0,tape⟩
  let some (withWords,_) := PhysicalCoverExecution.executeCached CandidateCapacityWords.program
      (CandidateCapacityWords.steps β.bits+1) build 0
    | throw (IO.userError "candidate core words did not halt")
  let initial : BitState 208 := ⟨withWords.heap,withWords.next,
    ⟨levels.root,bounds.root,rel.root,withWords.registers.d⟩,[],0,tape⟩
  let shifted := CandidateShiftSelectProgram.word grid gap a.1.2 b.1.2 samePort edge
  let k := CandidateCoreCapacityProgram.barrierSteps a.1.2 b.1.2 samePort samePoint x y shifted+8
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateCoreCapacityProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "fused candidate core capacity did not halt")
  let final := eraseState out
  let expected := if hard then β+1 else 0
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected.bits &&
      expected == D.directCapacity 0 1 4 limit β (.inl a) (.inl b) && out.pc == 4 &&
      out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "fused candidate core capacity disagreed with the original closure cell")
  IO.println s!"PASS fused physical candidate core capacity {expected}, levels {value x}/{value y}, shift {value shifted}, {k} instructions, paid {paid}"

def main : IO Unit := do
  checkWords [true,true,true] 7
  checkWords [false,false] 0
  checkLevels true [false,false,true,false] [false,true] [true,true,true] true
  checkLevels true [false,true] [false,false,true] [false,false] false
  checkLevels true [] [false,false] [true] true
  checkLevels false [true,true,true] [true,true,false] [false,false,true,false] true
  checkLevels false [false,true,true] [true,true] [false,false,true] false
  checkLevels false [false] [] [false,false] true
  checkPorts (.inl 0) (.inl 1) true
  checkPorts (.inl 1) (.inl 0) false
  checkPorts (.inr (.inl 0)) (.inl 1) true
  checkPorts (.inl 0) (.inr (.inr 1)) true
  checkPorts (.inr (.inl 2)) (.inr (.inr 2)) true
  checkPorts (.inr (.inl 0)) (.inr (.inr 1)) true
  checkPorts (.inr (.inl 1)) (.inr (.inr 0)) false
  checkPorts (.inr (.inr 0)) (.inl 1) false
  checkPorts (.inl 0) (.inr (.inl 1)) false
  checkGap (.inl 0) [false,false,true] [false,true,false] true 2
  checkGap (.inl 1) [false,false,true] [false,true,false] false 4
  checkGap (.inr (.inl 2)) [false,true,false] [false,true] false 0
  checkGap (.inl 2) [false,true] [false,false,true] true 2
  checkShift false true true false 0
  checkShift false true false true 0
  checkShift false true false false 4
  checkShift true false true true 1
  checkShift true false false true 4
  checkShift true true true true 4
  checkTerminal [false,false] false false false false false true
  checkTerminal [false] true true true true false false
  checkTerminal [false,true,false] false false true false true false
  checkTerminal [true,false] true true true false true false
  checkTerminal [true,false] true false true true false true
  checkCore ⟨⟨.inl 1,false⟩,3⟩ ⟨⟨.inl 0,true⟩,3⟩ 2 true
  checkCore ⟨⟨.inl 0,true⟩,4⟩ ⟨⟨.inl 0,true⟩,2⟩ 2 true
  checkCore ⟨⟨.inl 0,true⟩,2⟩ ⟨⟨.inl 0,true⟩,4⟩ 2 false
  checkCore ⟨⟨.inl 0,true⟩,3⟩ ⟨⟨.inl 0,false⟩,1⟩ 2 true
  checkCore ⟨⟨.inl 0,true⟩,2⟩ ⟨⟨.inl 0,false⟩,1⟩ 2 false
  checkCore ⟨⟨.inl 2,false⟩,4⟩ ⟨⟨.inl 1,false⟩,0⟩ 2 true
