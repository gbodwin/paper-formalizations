import DirectedFlowCutGap.CandidateConfiguredCutProgram
import DirectedFlowCutGap.PhysicalCoverExecution

open DirectedFlowCutGap BinaryArithmetic ImmutableReferenceSimulation

private def storeWords : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], prep => PackedWordPairTable.allocate .nil prep
  | word::rest, prep =>
    let tail := storeWords rest prep
    let head := PackedWordPairTable.word word tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def storeTable : List (List Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [], prep => PackedWordPairTable.allocate .nil prep
  | row::rest, prep =>
    let tail := storeTable rest prep
    let head := storeWords row tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

private def readPair (heap : NaturalHeap) (root : ℕ) : Option (ℕ×ℕ) :=
  match heap[root]? with
  | some (.pair a b) => some (a,b)
  | _ => none

private def readConfiguration (heap : NaturalHeap) (root : ℕ) :
    Option (ℕ×ℕ×List ℕ×List Bits×List (ℕ×ℕ)) := do
  let (vs,bundle) ← readPair heap root
  let (source,ends) ← readPair heap bundle
  let (target,edges) ← readPair heap ends
  let labels ← PhysicalCoverReader.readList heap some heap.length vs
  let words ← labels.mapM (PhysicalCoverReader.readWord heap)
  let table ← PhysicalCoverReader.readList heap (readPair heap) heap.length edges
  pure (source,target,labels,words,table)

private def checkRange (word : Bits) (size : ℕ) : IO Unit := do
  let input := PackedWordPairTable.word word PackedWordPairTable.seed
  let tape := [true,false]
  let initial : BitState 65 := ⟨input.heap,input.next,⟨input.root,[],[],[]⟩,[],0,tape⟩
  let k := BinaryLabelRangeProgram.steps word
  let run := fun fuel => PhysicalCoverExecution.executeCached BinaryLabelRangeProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "canonical label range did not halt")
  let final := eraseState out
  unless PhysicalCoverReader.readList final.heap (PhysicalCoverReader.readWord final.heap)
      final.heap.length final.registers.d == some ((List.range size).map Nat.bits) &&
      out.stack.isEmpty && out.pc == 4 && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "canonical label order or paid halt disagreed")
  IO.println s!"PASS physical labels 0 through {size} exclusive, {k} instructions, paid {paid}"

private def checkProduct (xs ys : List Bits) : IO Unit := do
  let a := storeWords xs PackedWordPairTable.seed
  let b := storeWords ys a
  let tape := [false,true]
  let initial : BitState 32 := ⟨b.heap,b.next,⟨a.root,b.root,[],[]⟩,[],0,tape⟩
  let initialHeap := eraseHeap initial.heap
  let some x := PhysicalCoverReader.readList initialHeap some initialHeap.length (value a.root)
    | throw (IO.userError "initial row addresses were unreadable")
  let some y := PhysicalCoverReader.readList initialHeap some initialHeap.length (value b.root)
    | throw (IO.userError "initial column addresses were unreadable")
  let k := WordPairProductProgram.steps xs.length ys.length
  let run := fun fuel => PhysicalCoverExecution.executeCached WordPairProductProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "word pair product did not halt")
  let final := eraseState out
  unless PhysicalCoverReader.readList final.heap (readPair final.heap) final.heap.length final.registers.d == some (x.product y) &&
      out.pc == 2 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "ordered pairs did not preserve the Cartesian order and word references")
  IO.println s!"PASS physical {xs.length} by {ys.length} word pairs, {k} instructions, paid {paid}"

private def checkConfiguration (n L : ℕ) : IO Unit := do
  let size := CandidatePhysicalCut.networkSize n L
  let count := size.bits++[false,false]
  let input := PackedWordPairTable.word count PackedWordPairTable.seed
  let tape := [true,false,true]
  let initial : BitState 129 := ⟨input.heap,input.next,⟨input.root,[],[],[]⟩,[],0,tape⟩
  let k := CandidateSearchConfigurationProgram.steps count
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateSearchConfigurationProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "candidate configuration did not halt")
  let final := eraseState out
  let some (source,target,labels,words,table) := readConfiguration final.heap final.registers.d
    | throw (IO.userError "candidate configuration was unreadable")
  unless words == (List.range size).map Nat.bits && table == labels.product labels &&
      labels[size-2]? == some source && labels[size-1]? == some target &&
      out.pc == 9 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "candidate configuration returned the wrong vertices, endpoints, or diagonal-inclusive pairs")
  IO.println s!"PASS physical candidate configuration with {size} labels and {table.length} pairs, {k} instructions, paid {paid}"

private def checkFromInputs (n L : ℕ) : IO Unit := do
  let nw := n.bits++[false]
  let lw := L.bits++[false,false]
  let vertices := PackedWordPairTable.word nw PackedWordPairTable.seed
  let grid := PackedWordPairTable.word lw vertices
  let tape := [true,false,true,false]
  let initial : BitState 299 := ⟨grid.heap,grid.next,⟨vertices.root,grid.root,[],[]⟩,[],0,tape⟩
  let k := CandidateInputConfigurationProgram.steps nw lw
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateInputConfigurationProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError "input-to-configuration run did not halt")
  let final := eraseState out
  let some count := PhysicalCoverReader.readWord final.heap final.registers.a
    | throw (IO.userError "the computed network size was not stored")
  let some (source,target,labels,words,table) := readConfiguration final.heap final.registers.d
    | throw (IO.userError "the configuration computed from inputs was unreadable")
  let size := 6*n*(L+1)+2
  unless value count == size && words == (List.range size).map Nat.bits && table == labels.product labels &&
      labels[size-2]? == some source && labels[size-1]? == some target &&
      out.pc == 3 && out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "the computed size, configuration, or paid halt disagreed")
  IO.println s!"PASS physical input n={n}, grid={L}, {size} labels and {table.length} pairs, {k} instructions, paid {paid}"

private def checkConfiguredCut : IO Unit := do
  let D : EncodedCandidateCapacity.Input 2 := {
    adjacency := Vector.ofFn fun _ => Vector.ofFn fun _ => false
    removed := Vector.ofFn fun _ => true }
  let F := CandidateEnumeration.make 2 1
  let original := F.network.enumeration.vertices
  let m := CandidatePhysicalCut.networkSize 2 1
  let rows := original.map fun a => original.map fun b => (D.directCapacity 0 1 1 1 0 a b).bits
  let ws := (List.range m).map Nat.bits
  unless original.map CandidateEnumeration.networkIndex == List.range m do
    throw (IO.userError "candidate fixture enumeration departed from its numeric labels")
  let problem := D.construct 0 1 1 1 F.nodes.enumeration F.network.enumeration
  let reference := RetainedCandidateSolver.backend F problem.cells problem.budget
  let selected := reference.vertices.map CandidateEnumeration.networkIndex
  let expected := original.map fun p => selected.contains (CandidateEnumeration.networkIndex p)
  let cs := storeTable rows PackedWordPairTable.seed
  let nw := [false,true,false]
  let lw := [true,false,false]
  let dimension := PackedWordPairTable.word nw cs
  let mask := PackedWordPairTable.word D.removed.toList dimension
  let size := PackedWordPairTable.word lw mask
  let bundle := PackedWordPairTable.allocate (.pair mask.root size.root) size
  let tape := [false,true,true]
  let initial : BitState 2177 := ⟨bundle.heap,bundle.next,⟨cs.root,dimension.root,bundle.root,[]⟩,[],0,tape⟩
  let flow := ResidualZeroTableProgram.table rows
  let edges := ws.product ws
  let s := (m-2).bits
  let t := (m-1).bits
  unless problem.budget == 0 && (ResidualFlowStepProgram.path flow ws edges s t).isEmpty do
    throw (IO.userError "the stored candidate was expected to be terminal at zero budget")
  let loop := ResidualFlowStepProgram.steps flow ws edges s t+12
  let k := CandidateInputConfigurationProgram.steps nw lw+CandidateBudgetProgram.steps D.removed.toList lw+
    ResidualZeroTableProgram.tableSteps rows+BinaryCounterProgram.steps []+loop+
    ResidualCutProgram.steps flow ws edges t+32
  let run := fun fuel => PhysicalCoverExecution.executeCached CandidateConfiguredCutProgram.program fuel initial 0
  let some (out,paid) := run (k+1) | throw (IO.userError s!"the configured candidate cut did not halt after {k} steps")
  let final := eraseState out
  unless PhysicalCoverReader.readWord final.heap final.registers.d == some expected && out.pc == 2 &&
      out.stack.isEmpty && out.source == tape && out.heap.take initial.heap.length == initial.heap &&
      (run k).isNone && 0 < paid do
    throw (IO.userError "configured candidate cut disagreed with the retained solver or the paid halt")
  IO.println s!"PASS physical configured candidate cut with {m} vertices and {(expected.filter id).length} selected, {k} instructions, paid {paid}"

def main : IO Unit := do
  checkRange [] 0
  checkRange [true,false,true,false,false] 5
  checkRange [false,false,false,true] 8
  checkProduct [[true,false],[]] [[false,true],[true,true],[]]
  checkProduct [] [[true]]
  checkProduct [[true]] []
  checkConfiguration 0 0
  checkConfiguration 2 1
  checkFromInputs 0 3
  checkFromInputs 2 1
  checkConfiguredCut
