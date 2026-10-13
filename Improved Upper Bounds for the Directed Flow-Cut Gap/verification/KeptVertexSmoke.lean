import DirectedFlowCutGap.ActualKeptVertex
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.KeptVertexSmoke
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


def check (name : String) (s t u : Bits) (zero expected : Bool) : IO Unit := do
  let sr := PackedWordPairTable.word s PackedWordPairTable.seed
  let tr := PackedWordPairTable.word t sr
  let ur := PackedWordPairTable.word u tr
  let ep := PackedWordPairTable.allocate (.pair sr.root tr.root) ur
  let z := PackedWordPairTable.allocate (.flag zero) ep
  let ctx := PackedWordPairTable.allocate (.pair ep.root z.root) z
  let source := [true,false,true]
  let initial : BitState 80 := ⟨ctx.heap,ctx.next,⟨ur.root,ctx.root,ur.root,ctx.root⟩,[],78,source⟩
  let actual := execute KeptVertex.program (KeptVertex.keepSteps s t u zero+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := 32*(s.length+t.length+u.length+2)+1
  unless actual.halted && heap[regs.d]?==some (.flag expected) &&
      readBits heap (heap.length+1) regs.a==some u && regs.b==value ctx.root &&
      actual.instructions==KeptVertex.keepSteps s t u zero+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 80 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==79 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+KeptVertex.keepCells s t u zero do
    throw (IO.userError ("FAIL actual kept vertex "++name))
  IO.println ("PASS actual kept vertex "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "nonzero-kept" [true] [false,true] [true,true] false true
  check "source-empty" [] [true] [] true true
  check "source-padded" [false,false] [true] [] true true
  check "target-padded" [true] [false,true] [false,true,false] true true
  check "neither-endpoint" [true] [false,true] [true,true] true false
  check "duplicate-endpoints" [true] [true,false] [true,false,false] true true
  check "all-zero-labels" [] [false] [false,false,false] true true
  check "short-circuit" (List.replicate 8 false) (List.replicate 7 true) (List.replicate 9 true) false true
end DirectedFlowCutGap.KeptVertexSmoke

def main := DirectedFlowCutGap.KeptVertexSmoke.main
