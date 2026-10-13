import DirectedFlowCutGap.KeptAdjacencyMatrixRepresentation
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.KeptAdjacencyMatrixSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) (fuel : ℕ) (s : BitState C) : Trace C :=
  go fuel s [] 0 0
where
  go : ℕ → BitState C → List Event → ℕ → ℕ → Trace C
  | 0,s,events,operations,instructions => ⟨s,events.reverse,operations,instructions,false⟩
  | fuel+1,s,events,operations,instructions =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,events.reverse,operations+a.operations,instructions,true⟩
      | some r => go fuel r.state (r.events.reverse++events) (operations+a.operations) (instructions+1)

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none


def vertices : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | u::us,s =>
    let tail := vertices us s
    let head := PackedWordPairTable.word u tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

def readVertices (heap : NaturalHeap) : ℕ → ℕ → Option (List Bits)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair h t) => do
      let u ← readBits heap (heap.length+1) h
      let us ← readVertices heap fuel t
      pure (u::us)
    | _ => none

def check (name : String) (rows : List Bits) (remaining kept : Bits) (expected : List Bits) : IO Unit := do
  let ar := vertices rows PackedWordPairTable.seed
  let rr := PackedWordPairTable.word remaining ar
  let kr := PackedWordPairTable.word kept rr
  let ctx := PackedWordPairTable.allocate (.pair rr.root kr.root) kr
  let source := [true,false,true]
  let initial : BitState 84 := ⟨ctx.heap,ctx.next,⟨ar.root,ctx.root,ar.root,ctx.root⟩,[],82,source⟩
  let actual := execute KeptAdjacencyMatrix.program (KeptAdjacencyMatrix.steps kept rows remaining+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := KeptAdjacencyMatrix.inputSteps rows
  unless actual.halted && readVertices heap (heap.length+1) regs.d==some expected &&
      readVertices heap (heap.length+1) regs.a==some rows && regs.b==value ctx.root &&
      readBits heap (heap.length+1) (value rr.root)==some remaining &&
      readBits heap (heap.length+1) (value kr.root)==some kept &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==KeptAdjacencyMatrix.steps kept rows remaining+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 84 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==83 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+KeptAdjacencyMatrix.cells kept rows remaining do
    throw (IO.userError ("FAIL actual kept adjacency matrix "++name))
  IO.println ("PASS actual kept adjacency matrix "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] [] [] []
  check "single-kept" [[true]] [true] [true] [[true]]
  check "single-row-removed" [[true]] [false] [true] [[false]]
  check "single-column-removed" [[true]] [true] [false] [[false]]
  check "single-no-edge" [[false]] [true] [true] [[false]]
  check "directed" [[false,true],[false,false]] [true,true] [true,true] [[false,true],[false,false]]
  check "remove-target" [[false,true],[true,false]] [true,false] [true,false] [[false,false],[false,false]]
  check "self-loops" [[true,false],[false,true]] [true,false] [true,false] [[true,false],[false,false]]
  check "asymmetric-masks" [[true,true],[true,true]] [true,false] [false,true] [[false,true],[false,false]]
  check "three-vertices" [[true,true,false],[false,true,true],[true,false,true]] [true,false,true] [true,false,true]
    [[true,false,false],[false,false,false],[true,false,true]]
  check "all-removed" [[true,true],[true,true]] [false,false] [false,false] [[false,false],[false,false]]
  check "empty-width" [[],[]] [true,false] [] [[],[]]
end DirectedFlowCutGap.KeptAdjacencyMatrixSmoke

def main := DirectedFlowCutGap.KeptAdjacencyMatrixSmoke.main
