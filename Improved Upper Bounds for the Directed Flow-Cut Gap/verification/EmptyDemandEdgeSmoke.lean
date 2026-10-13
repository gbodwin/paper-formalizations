import DirectedFlowCutGap.ActualEmptyDemandEdge
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.EmptyDemandEdgeSmoke
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

def check (name : String) (u v : Bits) (rows : List Bits) (expected : Bool) : IO Unit := do
  let ur := PackedWordPairTable.word u PackedWordPairTable.seed
  let vr := PackedWordPairTable.word v ur
  let ar := vertices rows vr
  let demand := PackedWordPairTable.allocate (.pair ur.root vr.root) ar
  let source := [true,false,true]
  let initial : BitState 128 := ⟨demand.heap,demand.next,⟨demand.root,ar.root,ur.root,vr.root⟩,[],126,source⟩
  let actual := execute EmptyDemandEdge.program (EmptyDemandEdge.steps u v+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := EmptyDemandEdge.inputSteps rows u v
  unless actual.halted && heap[regs.d]?==some (.flag expected) &&
      readVertices heap (heap.length+1) regs.b==some rows && regs.a==value demand.root &&
      readBits heap (heap.length+1) (value ur.root)==some u &&
      readBits heap (heap.length+1) (value vr.root)==some v &&
      heap.take demand.heap.length==(eraseState initial).heap &&
      actual.instructions==EmptyDemandEdge.steps u v+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 128 (demand.heap.length+1) (demand.heap.length+1) bound &&
      actual.state.pc==127 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==demand.heap.length+EmptyDemandEdge.cells u v do
    throw (IO.userError ("FAIL actual empty-demand edge "++name))
  IO.println ("PASS actual empty-demand edge "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "diagonal-no-loop" [] [] [[false]] true
  check "diagonal-loop" [] [] [[true]] true
  check "padded-zero-diagonal" [] [false,false] [[false]] true
  check "padded-one-diagonal" [true] [true,false,false] [[false,false],[false,false]] true
  check "forward-edge" [] [true] [[false,true],[false,false]] true
  check "reverse-no-edge" [true] [] [[false,true],[false,false]] false
  check "reverse-edge" [true] [] [[false,false],[true,false]] true
  check "forward-no-edge" [] [true] [[true,false],[true,true]] false
  check "third-column" [] [false,true] [[false,false,true],[false,false,false],[false,false,false]] true
  check "third-row" [false,true] [] [[false,false,false],[false,false,false],[false,true,false]] false
  check "padded-direct" [false,false] [true,false] [[false,true],[false,false]] true
  check "rectangular" [] [false,true] [[false,false,true]] true
end DirectedFlowCutGap.EmptyDemandEdgeSmoke

def main := DirectedFlowCutGap.EmptyDemandEdgeSmoke.main
